
# Armor workflow

Armor extends [Essent](https://github.com/ucsc-vama/essent) with configurable SLP-oriented optimizations and provides a reproducible flow from FIRRTL input to a native C++ simulator.

```text
FIRRTL design -> Essent/Armor -> generated C++ header -> driver -> emulator
```


## Requirements

- Linux on an x86-64 host with BMI2 support.
- Clang 12 (`clang++-12`). Armor-generated simulators require `-mbmi2`.
- Java and sbt 1.x.
- Python 3, GNU Make, `ar`, and `taskset` (from util-linux).

If Clang 12 or sbt are not on `PATH`, provide their paths explicitly:

```sh
export ARMOR_CXX=/path/to/clang++-12
export ARMOR_SBT=/path/to/sbt
```

`ARMOR_CXX` is used by both `build.sh` and `run_armor.py`.

## Get the source

Install Git LFS before cloning so the Boom designs are downloaded:

```sh
git lfs install
git clone https://github.com/jptang99-star/ARMOR.git
cd ARMOR
git lfs pull
```

SmallBoom, LargeBoom, and MegaBoom use Git LFS. A file starting with
`version https://git-lfs.github.com/spec/v1` is a pointer, not a FIRRTL design.

## Build

Build all local dependencies and the Essent JAR:

```sh
make build
# equivalent to: ./build.sh all
```

Individual targets are also available:

```sh
./build.sh fesvr    # third_party/fesvr/build/libfesvr.a
./build.sh essent   # utils/bin/essent.jar
```



## Run a design

The runner accepts a design name without the `.fir` suffix:

```sh
python3 script/run_armor.py <design> [options]
```

Useful examples:

```sh
# Randomly stimulate a GEMM design.
python3 script/run_armor.py Conv2D_16_16_8 --driver random --config O2_slp

# Run a Rocket design through the FESVR-backed emulator.
python3 script/run_armor.py MediumRocket-8C --driver emulator --config O2_slp

# Generate and compile only, with SLP disabled.
python3 script/run_armor.py MediumRocket-8C --driver emulator --config O2_no_slp --steps gen_sim compile
```

To quickly start the Armor workflow, use the makefile:

```sh
make run DESIGN=Conv2D_16_16_8
make run DESIGN=MediumRocket-8C
```


## Options

| Option | Default | Purpose |
| --- | --- | --- |
| `--config {O0,O2_no_slp,O2_slp}` | `O2_slp` | Select Armor optimization settings. |
| `--driver {emulator,random}` | `emulator` | Select the C++ driver. |
| `--work-dir PATH` | `work_dir` | Choose the root directory for generated results. |
| `--core N` | `10` | Bind the simulator process with `taskset -c N`. |
| `--steps ...` | all stages | Run any subset of `gen_sim`, `compile`, and `run`. |

Armor configurations are:

| Name | Essent level | SLP mode |
| --- | --- | --- |
| `O0` | `O0` | off |
| `O2_no_slp` | `O2` | off |
| `O2_slp` | `O2` | on |



## Drivers

### `emulator`

This driver builds `driver/emulator_essent.cc`, links FESVR, and runs `workload/dhrystone.riscv`. Rocket and Boom designs can use this mode.

### `random`

This driver uses `script/gen_random_driver.py` to inspect the generated header, create a C++ random-stimulus driver, and run it with a fixed cycle count. It does not require FESVR.



## Output layout

Results are isolated by date, design, Armor configuration, and driver:

```text
<work-dir>/<YYYYMMDD>/<design>/<config>/<driver>/
```

The directory contains the generated header, generated random driver when applicable, compiled emulator, and per-stage logs. `simrun.log` is the primary summary log: it records each invoked stage, its command, timestamps, exit code, and elapsed time.

## ICT implementation

The supported packer is ICT (`--slp-packer ict`). The pipeline performs ARMOR
normalization, ICT discovery, register packing, filtering, alignment planning,
scheduling, and packed C++ emission. The paper packer has been removed.

SLP sources are organized under `src/main/scala/armor/slp/` into `analysis`,
`packing`, `planning`, `lowering`, `emission`, and `reporting`. They retain the
Scala package `armor.slp`.

The simulator runner uses a 128 MB JVM stack for generation. Select a CPU
available on your machine with `--core N` (default: 10). The performance matrix
scripts are separate experiment tools; review their design/configuration lists
and set `CORE` before running them. The completed-matrix runner also requires
`BASE_DIR` pointing to an existing matrix directory.

## Validation

```sh
sbt compile test
```

The existing suite contains 37 tests. GEMM C++ output was also compared before
and after the alignment emission refactor for ICT Phase 1 and Phase 2 and was
byte-identical. This does not constitute end-to-end validation of every design.

## Licenses and third-party code

The existing repository license is retained in `LICENSE`. Essent-derived code
retains its original terms in `LICENSE.essent`. See `THIRD_PARTY_NOTICES.txt`
and the accompanying FESVR and FIRRTL integer library license files.

## Citation

If you use Armor in your research, please cite:


```bibtex
@inproceedings{tang2026armor,
  title     = {ARMOR: Accelerating RTL Simulation by Mitigating the Front-End Bottleneck Using Node Compression},
  author    = {Jiaping Tang, Jianna Mu, Zhiteng Chao, JingZhong Wen, Jing Ye, and Huawei Li},
  booktitle = {2026 59th IEEE/ACM International Symposium on Microarchitecture (MICRO)},
  location  = {Athens, Greece},
  year      = {2026}
}

@misc{tang2026armoracceleratingrtlsimulation,
      title={ARMOR: Accelerating RTL Simulation by Mitigating the Front-End Bottleneck Using Node Compression},
      author={Jiaping Tang and Jianan Mu and Zhiteng Chao and Jingzhong Wen and Jing Ye and Huawei Li},
      year={2026},
      eprint={2608.08462},
      archivePrefix={arXiv},
      primaryClass={cs.AR},
      url={https://arxiv.org/abs/2608.08462},
}
```
