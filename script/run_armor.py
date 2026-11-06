#!/usr/bin/env python3

import argparse
import re
import shlex
import subprocess
import sys
import time
from datetime import datetime
from pathlib import Path
from typing import Iterable, Sequence


SCRIPT_DIR = Path(__file__).resolve().parent
sys.dont_write_bytecode = True
sys.path.insert(0, str(SCRIPT_DIR.parent))

from define import (  # noqa: E402
    ARMOR_CONFIGS,
    CPP_CONFIG,
    DATE_FORMAT,
    DEFAULT_ARMOR_CONFIG,
    DEFAULT_DRIVER,
    DEFAULT_RUNING_CORE,
    DEFAULT_STEPS,
    DESIGN_DIR,
    DRIVER_CONFIGS,
    DRIVER_PATH,
    EMULATOR_NAME,
    ESSENT_JAR_PATH,
    ESSENT_SLP_PACKER,
    EXPECTED_TOP,
    FESVR_INCLUDE_DIR,
    FESVR_LIBRARY,
    JAVA_BIN,
    JAVA_HEAP,
    JAVA_STACK,
    MAX_CYCLES,
    PROJECT_DIR,
    RANDOM_CYCLES,
    RANDOM_SEED,
    WORKLOAD_PATH,
    WORK_DIR,
)


VALID_STEPS = ("gen_sim", "compile", "run")
_CIRCUIT_PATTERN = re.compile(r"^\s*circuit\s+([^\s:]+)\s*:")


class ArmorRun:
    def __init__(
        self,
        design: str,
        config_name: str,
        driver_name: str,
        work_dir: Path = WORK_DIR,
        jar_args: Sequence[str] = (),
        running_core: int = DEFAULT_RUNING_CORE,
    ) -> None:
        self.design = self._normalize_design_name(design)
        try:
            self.armor_config = ARMOR_CONFIGS[config_name]
        except KeyError as error:
            raise ValueError(f"unknown Armor configuration: {config_name}") from error
        try:
            self.driver_config = DRIVER_CONFIGS[driver_name]
        except KeyError as error:
            raise ValueError(f"unknown driver: {driver_name}") from error
        self.config_name = config_name
        self.driver_name = driver_name
        self.work_dir = Path(work_dir)
        self.jar_args = tuple(jar_args)
        if running_core < 0:
            raise ValueError("core must be a non-negative CPU index")
        self.running_core = running_core
        self.fir_path = Path(DESIGN_DIR) / f"{self.design}.fir"
        self.top_name = self._read_top_name()
        date_name = datetime.now().strftime(DATE_FORMAT)
        self.result_dir = (
            self.work_dir / date_name / self.design / self.config_name / self.driver_name
        )
        self.header_path = self.result_dir / f"{self.top_name}.h"
        self.emulator_path = self.result_dir / EMULATOR_NAME
        self.random_driver_path = self.result_dir / "random_driver.cpp"
        self.simrun_log_path = self.result_dir / "simrun.log"

    @staticmethod
    def _normalize_design_name(design: str) -> str:
        if not design or Path(design).name != design:
            raise ValueError("design must be a name from the designs directory")
        return design[:-4] if design.endswith(".fir") else design

    def _read_top_name(self) -> str:
        if not self.fir_path.is_file():
            raise FileNotFoundError(f"FIR design not found: {self.fir_path}")

        with self.fir_path.open("r", encoding="utf-8", errors="replace") as fir_file:
            for line in fir_file:
                match = _CIRCUIT_PATTERN.match(line)
                if match:
                    return match.group(1)

        raise RuntimeError(f"Unable to find the circuit name in {self.fir_path}")

    @staticmethod
    def _require_file(path: Path, description: str) -> None:
        if not Path(path).is_file():
            raise FileNotFoundError(f"{description} not found: {path}")

    @staticmethod
    def _append_log(log_path: Path, content: str) -> None:
        with log_path.open("a", encoding="utf-8") as log_file:
            log_file.write(content)
            log_file.flush()

    def _run_logged(
        self, stage: str, command: Sequence[str], cwd: Path, log_path: Path
    ) -> None:
        command_text = shlex.join(str(item) for item in command)
        start_time = datetime.now().astimezone()
        start_timestamp = start_time.strftime("%Y-%m-%d %H:%M:%S%z")
        start_record = (
            f"\n[{start_timestamp}] [{stage}] START\n"
            f"cwd: {cwd}\n"
            f"command: {command_text}\n"
            f"detail_log: {log_path}\n"
        )

        print(f"$ {command_text}")
        print(f"  log: {log_path}")
        self._append_log(self.simrun_log_path, start_record)

        start_counter = time.perf_counter()
        try:
            with log_path.open("a", encoding="utf-8") as log_file:
                log_file.write(start_record)
                log_file.flush()
                process = subprocess.Popen(
                    [str(item) for item in command],
                    cwd=cwd,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.STDOUT,
                    text=True,
                    encoding="utf-8",
                    errors="replace",
                    bufsize=1,
                )
                assert process.stdout is not None
                for line in process.stdout:
                    sys.stdout.write(line)
                    log_file.write(line)

                return_code = process.wait()
                end_time = datetime.now().astimezone()
                elapsed_seconds = time.perf_counter() - start_counter
                end_record = (
                    f"[{end_time.strftime('%Y-%m-%d %H:%M:%S%z')}] "
                    f"[{stage}] END\n"
                    f"exit_code: {return_code}\n"
                    f"elapsed_seconds: {elapsed_seconds:.3f}\n"
                )
                log_file.write(end_record)
                log_file.flush()
        except OSError as error:
            end_time = datetime.now().astimezone()
            elapsed_seconds = time.perf_counter() - start_counter
            end_record = (
                f"[{end_time.strftime('%Y-%m-%d %H:%M:%S%z')}] [{stage}] END\n"
                "exit_code: launch_error\n"
                f"elapsed_seconds: {elapsed_seconds:.3f}\n"
                f"error: {error}\n"
            )
            self._append_log(log_path, end_record)
            self._append_log(self.simrun_log_path, end_record)
            raise

        self._append_log(self.simrun_log_path, end_record)

        if return_code != 0:
            raise subprocess.CalledProcessError(return_code, command)

    def _require_essent_jar(self) -> None:
        self._require_file(Path(ESSENT_JAR_PATH), "Essent JAR")

    def _require_emulator_top(self) -> None:
        if self.top_name != EXPECTED_TOP:
            raise ValueError(
                f"emulator driver requires top-level {EXPECTED_TOP}, found {self.top_name}"
            )

    def gen_sim(self) -> None:
        self.result_dir.mkdir(parents=True, exist_ok=True)
        self._require_essent_jar()

        command = [
            JAVA_BIN,
            f"-Xmx{JAVA_HEAP}",
            f'-Xss{JAVA_STACK}',
            "-cp",
            str(ESSENT_JAR_PATH),
            "essent.Driver",
            str(self.fir_path),
            f"-{self.armor_config.opt_level}",
            "--output-dir",
            str(self.result_dir),
            "--essent-log-level",
            self.armor_config.log_level,
            "--slp-mode",
            self.armor_config.slp_mode,
            "--slp-packer",
            ESSENT_SLP_PACKER,
        ]
        if self.armor_config.slp_enable_phase2 is not None:
            command.extend(
                ("--slp-phase2", str(self.armor_config.slp_enable_phase2).lower())
            )
        command.extend(self.jar_args)
        print(f"============== Generate {self.design} ==============")
        self._run_logged(
            "gen_sim", command, Path(PROJECT_DIR), self.result_dir / "essent.log"
        )
        self._require_file(self.header_path, "generated simulator header")

    def compile(self) -> None:
        self.result_dir.mkdir(parents=True, exist_ok=True)
        self._require_file(self.header_path, "generated simulator header")

        if self.driver_config.requires_fesvr:
            self._require_emulator_top()
            self._require_file(Path(DRIVER_PATH), "emulator driver")
            self._require_file(Path(FESVR_LIBRARY), "FESVR library")
            source_files = [str(DRIVER_PATH), str(FESVR_LIBRARY), "-lpthread"]
            extra_includes = [f"-I{FESVR_INCLUDE_DIR}"]
        else:
            generator_path = SCRIPT_DIR / "gen_random_driver.py"
            self._require_file(generator_path, "random driver generator")
            generator_command = [
                sys.executable,
                str(generator_path),
                str(self.header_path),
                self.top_name,
                str(self.random_driver_path),
            ]
            print(f"============== Generate random driver {self.design} ==============")
            self._run_logged(
                "gen_random_driver",
                generator_command,
                self.result_dir,
                self.result_dir / "random-driver-generate.log",
            )
            self._require_file(self.random_driver_path, "random driver")
            source_files = [str(self.random_driver_path)]
            extra_includes = []

        command = [
            CPP_CONFIG.compiler,
            f"-{CPP_CONFIG.opt_level}",
            f"-std={CPP_CONFIG.standard}",
            *CPP_CONFIG.extra_flags,
            f"-I{self.result_dir}",
            f"-I{PROJECT_DIR / 'include'}",
            *extra_includes,
            *source_files,
            "-o",
            str(self.emulator_path),
        ]
        print(f"============== Compile {self.design} ==============")
        self._run_logged(
            "compile", command, self.result_dir, self.result_dir / "compile.log"
        )
        self._require_file(self.emulator_path, "compiled emulator")

    def run(self) -> None:
        self.result_dir.mkdir(parents=True, exist_ok=True)
        self._require_file(self.emulator_path, "compiled emulator")
        command = ["time", "taskset", "-c", str(self.running_core), str(self.emulator_path)]
        if self.driver_config.uses_workload:
            self._require_file(Path(WORKLOAD_PATH), "workload")
            command.extend(
                ["-c", f"--max-cycles={MAX_CYCLES}", str(WORKLOAD_PATH)]
            )
        else:
            command.extend([str(RANDOM_CYCLES), str(RANDOM_SEED)])
        print(f"============== Run {self.design} ==============")
        self._run_logged("run", command, self.result_dir, self.result_dir / "run.log")

    def execute(self, steps: Iterable[str]) -> None:
        requested_steps = set(steps)
        for step in VALID_STEPS:
            if step in requested_steps:
                getattr(self, step)()


# python3 script/run_armor.py Conv2D_16_16_8 --driver random
# python3 script/run_armor.py gemmini-full-32x32mesh-1x1-all-uint8 --driver random
# python3 script/run_armor.py MediumRocket-8C --driver emulator --slp-phase2 false

def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate, compile, and run one Armor design.",
        epilog=(
            "Unknown options are forwarded to essent.Driver.  For example: "
            "--slp-phase2 false"
        ),
    )
    parser.add_argument("design", help="design name under the designs directory")
    parser.add_argument(
        "--config",
        choices=tuple(ARMOR_CONFIGS),
        default=DEFAULT_ARMOR_CONFIG,
        help=f"Armor optimization configuration (default: {DEFAULT_ARMOR_CONFIG})",
    )
    parser.add_argument(
        "--driver",
        choices=tuple(DRIVER_CONFIGS),
        default=DEFAULT_DRIVER,
        help=f"simulation driver (default: {DEFAULT_DRIVER})",
    )
    parser.add_argument(
        "--work-dir",
        type=Path,
        default=WORK_DIR,
        help=f"base result directory (default: {WORK_DIR})",
    )
    parser.add_argument(
        "--core",
        type=int,
        default=DEFAULT_RUNING_CORE,
        help=f"CPU core to bind with taskset (default: {DEFAULT_RUNING_CORE})",
    )
    parser.add_argument(
        "--steps",
        nargs="+",
        choices=VALID_STEPS,
        default=list(DEFAULT_STEPS),
        help="stages to execute (default: gen_sim compile run)",
    )
    args, jar_args = parser.parse_known_args()
    if jar_args[:1] == ["--"]:
        jar_args = jar_args[1:]
    args.jar_args = tuple(jar_args)
    return args


def main() -> int:
    args = parse_args()
    try:
        run = ArmorRun(
            args.design,
            args.config,
            args.driver,
            args.work_dir,
            args.jar_args,
            args.core,
        )
        print(f"Result directory: {run.result_dir}")
        run.execute(args.steps)
    except (FileNotFoundError, RuntimeError, ValueError, subprocess.SubprocessError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
