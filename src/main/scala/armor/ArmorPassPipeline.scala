package armor

import firrtl.options.Dependency
import firrtl.stage.TransformManager.TransformDependency

object ArmorPassPipeline {
  private val slpDependencies: Seq[TransformDependency] = Seq(
    Dependency(ExpressionDecomposePass),
    Dependency(BitOpNormalizePass),
    Dependency(MemWriteGuardNormalizePass),
    Dependency(BitProjectionPromotionPass),
    Dependency(IrCanonicalCsePass)
  )

  def dependencies(slpMode: String): Seq[TransformDependency] =
    if (slpMode == "off") Seq.empty else slpDependencies
}
