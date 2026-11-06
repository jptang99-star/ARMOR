package essent

import java.io.{File, FileWriter, Writer}

import armor.ArmorPassPipeline
import armor.slp._
import essent.Emitter._
import essent.Extract._
import essent.ir._
import essent.Util._
import firrtl._
import firrtl.ir._
import firrtl.options.Dependency
import firrtl.stage.TransformManager.TransformDependency
import firrtl.stage.transforms

import logger._


class EssentEmitter(initialOpt: OptFlags, w: Writer, circuit: Circuit) extends LazyLogging {
  val flagVarName = "PARTflags"
  implicit val rn: Renamer = new Renamer
  val actTrac = new ActivityTracker(w, initialOpt)
  val vcd: Option[Vcd] = if (initialOpt.withVCD) Some(new Vcd(circuit,initialOpt,w,rn)) else None

  private final class PreparedSlp(
    val context:                       SlpAnalysisContext,
    val packerConfiguration:           SlpPackerConfiguration,
    val phase3Enabled:                 Boolean,
    val temporalStateExpansionEnabled: Boolean,
    val discovered:                    SlpPackingResult,
    val planned:                       SlpPackingResult,
    val plan:                          SlpPlan,
    val regPacking:                    SlpRegPackingResult,
    val rejections:                    Vector[SlpLoweringRejection],
    val filtering:                     Option[SlpPackFilterResult]
  )

  private def prepareSlp(circuit: Circuit, sg: StatementGraph, lowering: Boolean): PreparedSlp = {
    val slpConfig = SlpConfig.AnalysisOnly.copy(enablePhase2 = initialOpt.slpEnablePhase2)
    val context = SlpPipeline.prepare(circuit, sg, slpConfig) match {
      case Right(value) => value
      case Left(cycle) =>
        throw new IllegalStateException(
          s"SLP requires an acyclic StatementGraph; remaining nodes: ${cycle.remainingNodeIds.mkString(",")}"
        )
    }
    val packerKind = SlpPackerKind.parse(initialOpt.slpPacker).getOrElse(
      throw new IllegalArgumentException(s"unknown SLP packer: ${initialOpt.slpPacker}")
    )
    val packerConfiguration = SlpPackerFactory.resolveConfiguration(packerKind, context.config)
    val phase2Discovered = SlpPackerFactory.create(packerConfiguration, context).run()
    val provisionalValidation = if (lowering) SlpLoweringValidator.validate(context, phase2Discovered)
      else SlpLoweringValidation(phase2Discovered, Vector.empty)
    val provisionalFiltering = if (lowering) Some(
      new SlpIsolatedPackFilter(context).filter(provisionalValidation.result)
    ) else None
    val provisional = provisionalFiltering.map(_.result).getOrElse(provisionalValidation.result)

    // State-transition proposals are deliberately resolved only after the
    // ordinary ICT packs have established their retained lane layouts.
    // Phase 3 is enabled by default and can be disabled for experiments.
    val phase3Enabled = !java.lang.Boolean.getBoolean("armor.slp.disablePhase3")
    val phase3 = (packerKind, phase3Enabled) match {
      case (ICTPackerKind, true) => new SlpStateTransitionPhase3(context).run(provisional)
      case _ => SlpStateTransitionPhase3Result(
        provisional,
        SlpStateTransitionPhase3Stats(0, 0, 0, 0, 0, 0, 0)
      )
    }
    val provisionalRegPacking = new SlpRegUpdatePacker(context, phase3.result).run()
    val temporalEnabled = !java.lang.Boolean.getBoolean("armor.slp.disableTemporalStateExpansion")
    val temporal = (packerKind, temporalEnabled) match {
      case (ICTPackerKind, true) => new SlpTemporalStateExpansion(context).run(phase3.result, provisionalRegPacking)
      case _ => SlpTemporalStateExpansionResult(
        phase3.result,
        SlpTemporalStateExpansionStats(0, 0, 0, 0, 0, 0)
      )
    }
    val discovered = temporal.result
    val regPacking = new SlpRegUpdatePacker(context, discovered).run()
    val validation = if (lowering) SlpLoweringValidator.validate(context, discovered)
      else SlpLoweringValidation(discovered, Vector.empty)
    val filtering = if (lowering) Some(new SlpIsolatedPackFilter(context).filter(validation.result))
      else None
    val planned = filtering.map(_.result).getOrElse(validation.result)
    val (basePlan, retainedRegPacking) = filtering match {
      case Some(filtered) => filtered.plan -> filtered.regFiltering.result
      case None =>
        val packGraph = SlpPackGraph.build(context.graph, planned) match {
          case Right(value) => value
          case Left(cycle) =>
            throw new IllegalStateException(
              s"SLP PackGraph contains a cycle; remaining packs: ${cycle.remainingPackIds.mkString(",")}"
            )
        }
        val residualIndexedMuxes = SlpResidualIndexedMuxPlanner.build(context, packGraph, Some(regPacking))
        val indexedPackReads = SlpIndexedPackReadPlanner.build(context, packGraph, residualIndexedMuxes)
        val alignPlan = SlpAlignPlanner.build(
          context,
          packGraph,
          Some(regPacking),
          indexedPackReads.coveredScalarUses,
          residualIndexedMuxes.scalarUses
        )
        val scalarPlan = SlpPlan.build(
          context,
          packGraph,
          alignPlan,
          Some(regPacking),
          indexedPackReads,
          residualIndexedMuxes
        ) match {
          case Right(value) => value
          case Left(cycle) =>
            throw new IllegalStateException(
              s"SLP plan contains a cycle; remaining nodes: ${cycle.remainingNodes.map(_.label).mkString(",")}"
            )
        }
        scalarPlan -> regPacking
    }
    new PreparedSlp(
      context,
      packerConfiguration,
      phase3Enabled,
      temporalEnabled,
      discovered,
      planned,
      basePlan,
      retainedRegPacking,
      validation.rejections,
      filtering
    )
  }

  private def checkLoweringOptions(opt: OptFlags): Unit = {
    val problems = Vector(
      Option.when(!opt.removeFlatConnects)("removeFlatConnects must be enabled"),
      Option.when(!opt.regUpdates)("regUpdates must be enabled"),
      Option.when(opt.conditionalMuxes)("conditionalMuxes must be disabled"),
      Option.when(opt.useCondParts)("useCondParts must be disabled"),
      Option.when(opt.withVCD)("VCD/FST emission is not supported"),
      Option.when(opt.trackSigs || opt.trackParts || opt.trackExts)("activity tracking is not supported")
    ).flatten
    require(problems.isEmpty, s"SLP lowering configuration is unsupported: ${problems.mkString("; ")}")
  }
  // Declaring Modules
  //----------------------------------------------------------------------------
  private def regStorageDeclarations(regPacking: Option[SlpRegPackingResult]): Vector[String] =
    regPacking.toVector.flatMap(_.packs).map { pack =>
      s"uint64_t ${SlpRegStorageNames.state(pack.id)};"
    }

  private def regStorageInitializers(regPacking: Option[SlpRegPackingResult]): Vector[String] =
    regPacking.toVector.flatMap(_.packs).map { pack =>
      s"${SlpRegStorageNames.state(pack.id)} = UINT64_C(0);"
    }

  def declareModule(
    m: Module,
    topName: String,
    regPacking: Option[SlpRegPackingResult] = None
  ): Unit = {
    val registers = findInstancesOf[DefRegister](m.body)
    val memories = findInstancesOf[DefMemory](m.body)
    val registerDecs = registers flatMap {d: DefRegister => {
      val typeStr = genCppType(d.tpe)
      val regName = d.name
      Seq(s"$typeStr $regName;")
    }}
    val memDecs = memories map {m: DefMemory => {
      s"${genCppType(m.dataType)} ${m.name}[${m.depth}];"
    }}
    val modulesAndPrefixes = findModuleInstances(m.body)
    val moduleDecs = modulesAndPrefixes map { case (module, fullName) => {
      val instanceName = fullName.split("\\.").last
      s"$module $instanceName;"
    }}
    val modName = m.name
    w.writeLines(0, "")
    w.writeLines(0, s"typedef struct $modName {")
    w.writeLines(1, registerDecs)
    if (modName == topName) {
      w.writeLines(1, regStorageDeclarations(regPacking))
    }
    w.writeLines(1, memDecs)
    w.writeLines(1, m.ports flatMap emitPort(modName == topName))
    w.writeLines(1, moduleDecs)
    w.writeLines(0, "")
    w.writeLines(1, s"$modName() {")
    w.writeLines(2, initializeVals(modName == topName)(m, registers, memories))
    if (modName == topName) {
      w.writeLines(2, regStorageInitializers(regPacking))
    }
    w.writeLines(1, "}")
    if (modName == topName) {
      w.writeLines(0, "")
      // w.writeLines(1, s"void connect_harness(CommWrapper<struct $modName> *comm);")
    } else {
      w.writeLines(0, s"} $modName;")
    }
  }

  def declareExtModule(m: ExtModule): Unit = {
    val modName = m.name
    w.writeLines(0, "")
    w.writeLines(0, s"typedef struct $modName {")
    w.writeLines(1, m.ports flatMap emitPort(true))
    w.writeLines(0, s"} $modName;")
  }


  // Write General-purpose Eval
  //----------------------------------------------------------------------------
  // TODO: move specialized CondMux emitter elsewhere?
  def writeBodyInner(indentLevel: Int, sg: StatementGraph, opt: OptFlags,
                     keepAvail: Set[String] = Set()): Unit = {
    sg.stmtsOrdered() foreach { stmt => stmt match {
      case cm: CondMux => {
        if (rn.nameToMeta(cm.name).decType == MuxOut)
          w.writeLines(indentLevel, s"${genCppType(cm.mux.tpe)} ${rn.emit(cm.name)};")
        val muxCondRaw = emitExpr(cm.mux.cond)
        val muxCond = if (muxCondRaw == "reset") s"UNLIKELY($muxCondRaw)" else muxCondRaw
        w.writeLines(indentLevel, s"if (UNLIKELY($muxCond)) {")
        writeBodyInner(indentLevel + 1, StatementGraph(cm.tWay), opt)
        w.writeLines(indentLevel, "} else {")
        writeBodyInner(indentLevel + 1, StatementGraph(cm.fWay), opt)
        w.writeLines(indentLevel, "}")
      }
      case _ => {
        w.writeLines(indentLevel, emitStmt(stmt))
        if (opt.withVCD)  vcd.get.compSmallEval(stmt, indentLevel)
        if (opt.trackSigs) actTrac.emitSigTracker(stmt, indentLevel)
      }
    }}
  }

  def checkRegResetSafety(sg: StatementGraph): Unit = {
    val updatesWithResets = sg.allRegDefs() filter { r => emitExpr(r.reset) != "UInt<1>(0x0)" }
    assert(updatesWithResets.isEmpty)
  }


  // Write Zoning Optimized Eval
  //----------------------------------------------------------------------------
  def genEvalFuncName(partID: Int): String = "EVAL_" + partID

  def genDepPartTriggers(consumerIDs: Seq[Int], condition: String): Seq[String] = {
    consumerIDs.sorted map { consumerID => s"$flagVarName[$consumerID] |= $condition;" }
  }

  def genAllTriggers(signalNames: Seq[String], outputConsumers: Map[String, Seq[Int]],
      suffix: String): Seq[String] = {
    selectFromMap(signalNames, outputConsumers).toSeq flatMap { case (name, consumerIDs) => {
      genDepPartTriggers(consumerIDs, s"${rn.emit(name)} != ${rn.emit(name + suffix)}")
    }}
  }

  def writeZoningPredecs(
                          sg: StatementGraph,
                          condPartWorker: MakeCondPart,
                          topName: String,
                          extIOtypes: Map[String, Type],
                          opt: OptFlags): Unit = {
    // predeclare part outputs
    val outputPairs = condPartWorker.getPartOutputsToDeclare()
    val outputConsumers = condPartWorker.getPartInputMap()
    w.writeLines(1, outputPairs map {case (name, tpe) => s"${genCppType(tpe)} ${rn.emit(name)};"})
    val extIOCacheDecs = condPartWorker.getExternalPartInputTypes(extIOtypes) map {
      case (name, tpe) => s"${genCppType(tpe)} ${rn.emit(name + condPartWorker.cacheSuffix)};"
    }
    w.writeLines(1, extIOCacheDecs)
    w.writeLines(1, s"std::array<bool,${condPartWorker.getNumParts()}> $flagVarName;")
    // FUTURE: worry about namespace collisions with user variables
    w.writeLines(1, s"bool sim_cached = false;")
    w.writeLines(1, s"bool regs_set = false;")
    w.writeLines(1, s"bool update_registers;")
    w.writeLines(1, s"bool done_reset;")
    w.writeLines(1, s"bool verbose;")
    w.writeLines(0, "")
    sg.stmtsOrdered() foreach { stmt => stmt match {
      case cp: CondPart => {
        w.writeLines(1, s"void ${genEvalFuncName(cp.id)}() {")
        if (!cp.alwaysActive)
          w.writeLines(2, s"$flagVarName[${cp.id}] = false;")
        if (opt.trackParts)
          w.writeLines(2, s"${actTrac.actVarName}[${cp.id}]++;")

        val cacheOldOutputs = cp.outputsToDeclare.toSeq map {
          case (name, tpe) => { s"${genCppType(tpe)} ${rn.emit(name + condPartWorker.cacheSuffix)} = ${rn.emit(name)};"
        }}
        w.writeLines(2, cacheOldOutputs)
        val (regUpdates, noRegUpdates) = partitionByType[RegUpdate](cp.memberStmts)
        val keepAvail = (cp.outputsToDeclare map { _._1 }).toSet
        val bodySG = StatementGraph(noRegUpdates)
        if (opt.conditionalMuxes)
          MakeCondMux(bodySG, rn, keepAvail)
        writeBodyInner(2, bodySG, opt, keepAvail)
        w.writeLines(2, genAllTriggers(cp.outputsToDeclare.keys.toSeq, outputConsumers, condPartWorker.cacheSuffix))
        val regUpdateNamesInPart = regUpdates flatMap findResultName
        w.writeLines(2, genAllTriggers(regUpdateNamesInPart, outputConsumers, "$next"))
        // triggers for MemWrites
        val memWritesInPart = cp.memberStmts collect { case mw: MemWrite => mw }
        val memWriteTriggers = memWritesInPart flatMap { mw => {
          val condition = s"${emitExprWrap(mw.wrEn)} && ${emitExprWrap(mw.wrMask)}"
          genDepPartTriggers(outputConsumers.getOrElse(mw.memName, Seq()), condition)
        }}
        w.writeLines(2, memWriteTriggers)
        w.writeLines(2, regUpdates flatMap emitStmt)

        w.writeLines(1, "}")
      }
      case _ => throw new Exception(s"Statement at top-level is not a CondPart (${stmt.serialize})")
    }}
    w.writeLines(0, "")
  }

  def writeZoningBody(sg: StatementGraph, condPartWorker: MakeCondPart, opt: OptFlags): Unit = {
    w.writeLines(2, "if (reset || !done_reset) {")
    w.writeLines(3, "sim_cached = false;")
    w.writeLines(3, "regs_set = false;")
    w.writeLines(2, "}")
    w.writeLines(2, "if (!sim_cached) {")
    w.writeLines(3, s"$flagVarName.fill(true);")
    w.writeLines(2, "}")
    w.writeLines(2, "sim_cached = regs_set;")
    w.writeLines(2, "this->update_registers = update_registers;")
    w.writeLines(2, "this->done_reset = done_reset;")
    w.writeLines(2, "this->verbose = verbose;")
    val outputConsumers = condPartWorker.getPartInputMap()
    val externalPartInputNames = condPartWorker.getExternalPartInputNames()
    // do activity detection on other inputs (external IOs and resets)
    w.writeLines(2, genAllTriggers(externalPartInputNames, outputConsumers, condPartWorker.cacheSuffix))
    // cache old versions
    val extIOCaches = externalPartInputNames map {
      sigName => s"${rn.emit(sigName + condPartWorker.cacheSuffix)} = ${rn.emit(sigName)};"
    }
    w.writeLines(2, extIOCaches.toSeq)
    sg.stmtsOrdered() foreach { stmt => stmt match {
      case cp: CondPart => {
        if (!cp.alwaysActive)
          w.writeLines(2, s"if (UNLIKELY($flagVarName[${cp.id}])) ${genEvalFuncName(cp.id)}();")
        else
          w.writeLines(2, s"${genEvalFuncName(cp.id)}();")
      }
      case _ => w.writeLines(2, emitStmt(stmt))
    }}
    // w.writeLines(2,  "#ifdef ALL_ON")
    // w.writeLines(2, s"$flagVarName.fill(true);" )
    // w.writeLines(2,  "#endif")
    w.writeLines(2, "regs_set = true;")
  }


  // General Structure (and Compiler Boilerplate)
  //----------------------------------------------------------------------------
  def execute(circuit: Circuit): Unit = {
    val opt = initialOpt
    val topName = circuit.main
    val headerGuardName = topName.toUpperCase + "_H_"
    w.writeLines(0, s"#ifndef $headerGuardName")
    w.writeLines(0, s"#define $headerGuardName")
    w.writeLines(0, "")
    w.writeLines(0, "#include <array>")
    w.writeLines(0, "#include <cstdint>")
    w.writeLines(0, "#include <cstdlib>")
    w.writeLines(0, "#include <uint.h>")
    w.writeLines(0, "#include <sint.h>")
    if (opt.slpMode == "lowering") w.writeLines(0, "#include <slp_runtime.h>")
    w.writeLines(0, "#define UNLIKELY(condition) __builtin_expect(static_cast<bool>(condition), 0)")
    if (opt.trackParts || opt.trackSigs || opt.withVCD) {
      w.writeLines(0, "#include <fstream>")
    }

    if(opt.withVCD) {
      w.writeLines(0, "uint64_t vcd_cycle_count = 0;")
      w.writeLines(1,s"""FILE *outfile;""")
      // TODO: size this buffer based on widest signal present in the design
      w.writeLines(1,s"""char VCD_BUF[2000];""")
    }
    val lowering = opt.slpMode == "lowering"
    if (lowering) checkLoweringOptions(opt)
    var workingCircuit = circuit
    var extIOMap = findExternalPorts(workingCircuit)
    var sg = StatementGraph(workingCircuit, opt.removeFlatConnects)
    val outputDirectory = Option(opt.outputDir()).filter(_.nonEmpty)
      .map(new File(_)).getOrElse(new File(System.getProperty("user.dir")))
    val preparedSlp = if (opt.slpMode == "analysis" || lowering) {
      var prepared = prepareSlp(workingCircuit, sg, lowering)
      val retainedRegPacks = prepared.plan.regPacking.map(_.packs.size).getOrElse(0)
      if (lowering && prepared.planned.packs.isEmpty && retainedRegPacks == 0 && opt.regUpdates) {
        logger.info("SLP retained no combinational or RegUpdate packs; restoring scalar RegUpdate elision")
        OptElideRegUpdates(sg)
        prepared = prepareSlp(workingCircuit, sg, lowering)
      }
      SlpConfigWriter.write(
        outputDirectory,
        workingCircuit.main,
        opt.slpMode,
        prepared.context.config,
        prepared.packerConfiguration,
        prepared.phase3Enabled,
        prepared.temporalStateExpansionEnabled
      )
      SlpAnalysisWriter.write(
        prepared.context,
        prepared.discovered,
        outputDirectory,
        workingCircuit.main,
        opt.slpMode,
        Some(prepared.regPacking),
        prepared.plan.packGraph.packs.iterator.flatMap(_.nodeIds).toSet ++
          prepared.regPacking.packs.iterator.flatMap(_.nodeIds)
      )
      SlpAnalysisWriter.writePlan(prepared.context, prepared.plan, outputDirectory, workingCircuit.main, opt.slpMode)
      prepared.filtering.foreach { filtering =>
        SlpPackFilterWriter.write(
          filtering,
          outputDirectory,
          workingCircuit.main,
          prepared.context.config
        )
      }
      logger.info(
        s"SLP ${opt.slpMode} found ${prepared.discovered.stats.acceptedPacks} packs containing " +
          s"${prepared.discovered.stats.packedNodes} nodes; lowering retained ${prepared.planned.packs.size} packs, " +
          s"with ${prepared.plan.stats.scalarToPackAlignments} scalar-to-pack alignments and " +
          s"${prepared.plan.stats.packToScalarAlignments} unpack operations"
      )
      logger.info(
        s"SLP RegUpdate analysis found ${prepared.regPacking.stats.acceptedPacks} packs containing " +
          s"${prepared.regPacking.stats.packedRegisters} registers, " +
          s"${prepared.regPacking.stats.directStateReads} direct state reads and " +
          s"${prepared.regPacking.stats.directStateWrites} direct state writes"
      )
      prepared.rejections.foreach(rejection => logger.warn(
        s"SLP pack ${rejection.originalPackId} fell back to scalar: ${rejection.reason}"
      ))
      Some(prepared)
    } else None
    if (lowering && opt.regUpdates) {
      // Packed RegUpdate discovery must retain the explicit $next producer:
      // it is the source of an exact-layout direct write. Scalar fallback
      // still emits the original $next + RegUpdate pair, while selected
      // register packs contract those nodes in the immutable SLP schedule.
      rn.populateFromSG(sg, extIOMap)
    }
    logger.info(sg.makeStatsString())
    val containsAsserts = sg.containsStmtOfType[Stop]()
    val condPartWorker = MakeCondPart(sg, rn, extIOMap)
    if (!lowering) rn.populateFromSG(sg, extIOMap)
    if (lowering) {
      // SlpPlan owns this exact graph snapshot. Do not mutate it between
      // planning and emission.
    } else if (opt.useCondParts) {
      condPartWorker.doOpt(opt.partCutoff)
    } else {
      if (opt.regUpdates)
        OptElideRegUpdates(sg)
      if (opt.conditionalMuxes)
        MakeCondMux(sg, rn, Set())
    }
    checkRegResetSafety(sg)
    if (opt.trackParts || opt.trackSigs || opt.trackExts)
      actTrac.declareTop(sg, topName, condPartWorker)

    val loweredRegPacking = if (lowering) preparedSlp.flatMap(_.plan.regPacking) else None
    workingCircuit.modules foreach {
      case m: Module => declareModule(m, topName, loweredRegPacking)
      case m: ExtModule => declareExtModule(m)
    }
    val topModule = findModule(topName, workingCircuit) match {case m: Module => m}
    if (initialOpt.writeHarness) {
      w.writeLines(0, "")
      w.writeLines(1, s"void connect_harness(CommWrapper<struct $topName> *comm) {")
      w.writeLines(2, HarnessGenerator.harnessConnections(topModule))
      w.writeLines(1, "}")
      w.writeLines(0, "")
    }
    if (opt.withVCD)  { vcd.get.declareOldvaluesAll(workingCircuit) }
    if(opt.withVCD) { vcd.get.genWaveHeader() }
    if (containsAsserts) {
      w.writeLines(1, "bool assert_triggered = false;")
      w.writeLines(1, "int assert_exit_code;")
      w.writeLines(0, "")
    }
    if (opt.useCondParts)
      writeZoningPredecs(sg, condPartWorker, workingCircuit.main, extIOMap, opt)
    w.writeLines(1, s"void eval(bool update_registers, bool verbose, bool done_reset) {")
    if(opt.withVCD) { vcd.get.initializeOldValues(workingCircuit) }
    if (opt.trackParts || opt.trackSigs)
      w.writeLines(2, "act_cycle_count++;")
    if (lowering) {
      val prepared = preparedSlp.get
      val slpEmitter = new SlpEmitter(prepared.context, prepared.plan, rn)
      val lazyRegViews = java.lang.Boolean.getBoolean("armor.slp.lazyRegViews")
      if (!lazyRegViews) w.writeLines(2, slpEmitter.emitRegViews())
      prepared.plan.topologicalSchedule.foreach { node =>
        val lines = slpEmitter.emit(node)
        if (lazyRegViews) w.writeLines(2, slpEmitter.emitRegViewsUsedBy(lines))
        w.writeLines(2, lines)
      }
      val stats = slpEmitter.stats
      val outputDirectory = Option(opt.outputDir()).filter(_.nonEmpty)
        .map(new File(_)).getOrElse(new File(System.getProperty("user.dir")))
      SlpAnalysisWriter.writeLowering(
        stats,
        prepared.rejections,
        outputDirectory,
        workingCircuit.main
      )
      logger.info(
        s"SLP lowering emitted ${stats.packNodes} packs " +
          s"(${stats.fastBitwisePacks} fast, ${stats.laneWisePacks} lane-wise)"
      )
    } else if (opt.useCondParts)
      writeZoningBody(sg, condPartWorker, opt)
    else
      writeBodyInner(2, sg, opt)
    if(opt.withVCD) { vcd.get.compareOldValues(workingCircuit) }
    if (containsAsserts) {
      w.writeLines(2, "if (!done_reset) assert_triggered = false;")
    }
    w.writeLines(0, "")
    if(opt.withVCD) { vcd.get.assignOldValues(workingCircuit) }
    w.writeLines(2, "")
    w.writeLines(1, "}")
    // if (opt.trackParts || opt.trackSigs) {
    //   w.writeLines(1, s"~$topName() {")
    //   w.writeLines(2, "writeActToJson();")
    //   w.writeLines(1, "}")
    // }
    w.writeLines(0, "")
    w.writeLines(0, "")
    w.writeLines(0, s"} $topName;") //closing top module dec
    w.writeLines(0, "")
    w.writeLines(0, s"#endif  // $headerGuardName")
  }
}


class EssentCompiler(opt: OptFlags) {

  // VerilogMemDelays: compiling memory latencies to combinational-read memories with delay pipelines.
  // This pass eliminates mems with read latency = 1 (introduced by CHIRRTL smem)
  // and thus satisfy essent.pass.FactorMemReads (memHasRightParams)

  // ConvertAsserts: Convert Verification IR (with op == Formal.Assert) into conventional print statement

  val readyForEssent: Seq[TransformDependency] =
    Seq(
      Dependency(firrtl.passes.memlib.VerilogMemDelays),
      Dependency(essent.passes.RemoveFormalNCover),
      Dependency(firrtl.transforms.formal.ConvertAsserts)
    ) ++
    firrtl.stage.Forms.LowFormOptimized ++
    Seq(
//      Dependency(essent.passes.LegacyInvalidNodesForConds),
      Dependency(essent.passes.ReplaceAsyncRegs),
      Dependency(essent.passes.NoClockConnects),
      Dependency(essent.passes.RegFromMem1),
      Dependency(essent.passes.FactorMemReads),
      Dependency(essent.passes.FactorMemWrites),
      Dependency(essent.passes.SplitRegUpdates),
      Dependency(essent.passes.FixMulResultWidth),
      Dependency(essent.passes.DistinctTypeInstNames),
      Dependency(essent.passes.RemoveAsAsyncReset),
      Dependency(essent.passes.ReplaceRsvdKeywords)
    ) ++
    ArmorPassPipeline.dependencies(opt.slpMode)

  def compileAndEmit(circuit: Circuit): Unit = {
    val topName = circuit.main
    val configuredOutputDir = opt.outputDir()
    if (configuredOutputDir.nonEmpty) {
      val outputDirFile = new File(configuredOutputDir)
      if (!outputDirFile.exists() && !outputDirFile.mkdirs()) {
        throw new java.io.IOException(s"Unable to create output directory: $configuredOutputDir")
      }
    }
    if (opt.writeHarness) {
      val harnessFilename = new File(opt.outputDir(), s"$topName-harness.cc")
      val harnessWriter = new FileWriter(harnessFilename)
      if (opt.withVCD) { HarnessGenerator.topFile(topName, harnessWriter," |  dut.genWaveHeader();") }
      else { HarnessGenerator.topFile(topName, harnessWriter, "")}
      harnessWriter.close()
    }
    val firrtlCompiler = new transforms.Compiler(readyForEssent)
    val resultState = firrtlCompiler.execute(CircuitState(circuit, Seq()))
    if (opt.dumpLoFirrtl) {
      val debugFilename = new File(opt.outputDir(), s"$topName.lo.fir")
      val debugWriter = new FileWriter(debugFilename)
      debugWriter.write(resultState.circuit.serialize)
      debugWriter.close()
    }

    val outputDir = if (opt.outputDir().nonEmpty) opt.outputDir() else System.getProperty("user.dir")
    val dutFile = new File(outputDir, s"$topName.h")

    val dutWriter = new FileWriter(dutFile)
    val emitter = new EssentEmitter(opt, dutWriter,resultState.circuit)
    emitter.execute(resultState.circuit)
    dutWriter.close()
  }
}
