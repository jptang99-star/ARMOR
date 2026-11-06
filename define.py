from dataclasses import dataclass
import os
from pathlib import Path
from types import MappingProxyType
from typing import Mapping, Optional


PROJECT_DIR = Path(__file__).resolve().parent

DESIGN_DIR = PROJECT_DIR / "designs"
WORK_DIR = PROJECT_DIR / "work_dir"
DRIVER_PATH = PROJECT_DIR / "driver" / "emulator_essent.cc"
WORKLOAD_PATH = PROJECT_DIR / "workload" / "dhrystone.riscv"
ESSENT_JAR_PATH = PROJECT_DIR / "utils" / "bin" / "essent.jar"

SBT_BIN = "sbt"
JAVA_BIN = "java"
JAVA_HEAP = "32G"
JAVA_STACK = "128M"


ESSENT_SLP_PACKER = "ict"

DEFAULT_RUNING_CORE = 10

###############################
@dataclass(frozen=True)
class ArmorConfiguration:
    """One named Armor optimization configuration.

    ``slp_enable_phase2=None`` deliberately leaves the compiler's default
    untouched.  This is what the regular O2+SLP configuration uses.
    """

    opt_level: str
    slp_mode: str
    log_level: str
    slp_enable_phase2: Optional[bool] = None


ARMOR_CONFIGS: Mapping[str, ArmorConfiguration] = MappingProxyType(
    {
        "O0": ArmorConfiguration(opt_level="O0", slp_mode="off", log_level="info"),
        "O2_no_slp": ArmorConfiguration(opt_level="O2", slp_mode="off", log_level="info"),
        "O2_slp": ArmorConfiguration(opt_level="O2", slp_mode="lowering", log_level="info"),
    }
)

DEFAULT_ARMOR_CONFIG = "O2_slp"


###############################
@dataclass(frozen=True)
class DriverConfig:
    """One simulator-driver mode and its external runtime requirements."""

    requires_fesvr: bool
    uses_workload: bool


DRIVER_CONFIGS: Mapping[str, DriverConfig] = MappingProxyType(
    {
        "emulator": DriverConfig(requires_fesvr=True, uses_workload=True),
        "random": DriverConfig(requires_fesvr=False, uses_workload=False),
    }
)

DEFAULT_DRIVER = "emulator"



###############################
@dataclass(frozen=True)
class CPPConfig:
    """Configuration for the required Clang 12 C++ compilation toolchain.

    ``compiler`` is a command on ``PATH`` by default, but can be set to an
    absolute Clang 12 path through ``ARMOR_CXX``.  BMI2 is a required target
    ISA feature for Armor-generated simulators and is therefore not optional.
    """

    compiler: str
    opt_level: str = "O2"
    standard: str = "c++20"
    extra_flags: tuple[str, ...] = ("-fbracket-depth=10240", "-mbmi2")


CLANG_12_PATH = "clang++-12"
CPP_CONFIG = CPPConfig(compiler=os.environ.get("ARMOR_CXX", CLANG_12_PATH))



###############################
FESVR_ROOT = PROJECT_DIR / "third_party" / "fesvr"
FESVR_INCLUDE_DIR = FESVR_ROOT / "include"
FESVR_LIBRARY = FESVR_ROOT / "build" / "libfesvr.a"


###############################
EXPECTED_TOP = "TestHarness"
EMULATOR_NAME = "emulator"
MAX_CYCLES = 100_000_000
RANDOM_CYCLES = 1_000_000
RANDOM_SEED = 0
DATE_FORMAT = "%Y%m%d"
DEFAULT_STEPS = ("gen_sim", "compile", "run")
