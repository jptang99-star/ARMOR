
# Armor workflow

Armor extends Essent(https://github.com/ucsc-vama/essent/tree/master) with configurable SLP-oriented optimizations and provides a reproducible flow from FIRRTL input to a native C++ simulator.

```text
FIRRTL design -> Essent/Armor -> generated C++ header -> driver -> emulator
```


## Code Release

**The ARMOR source code will be publicly released after MICRO 2026.**



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
python3 script/run_armor.py MediumRocket-8C --driver emulator --config O2_no_slp --steps gen_sim compile run
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

## Citation

If you use Armor in your research, please cite:


```bibtex
@inproceedings{tang2026armor,
  title     = {ARMOR: Accelerating RTL Simulation by Mitigating the Front-End Bottleneck Using Node Compression},
  author    = {Jiaping Tang, Jianna Mu, JingZhong Wen, Zhiteng Chao, Jing Ye, and Huawei Li},
  booktitle = {2026 59th IEEE/ACM International Symposium on Microarchitecture (MICRO)},
  location  = {Athens, Greece},
  year      = {2026}
}
```

