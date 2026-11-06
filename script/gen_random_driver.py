#!/usr/bin/env python3

import argparse
import re
from dataclasses import dataclass
from pathlib import Path
from typing import List


_DECLARATION = re.compile(r"^\s*(UInt|SInt)<(\d+)>\s+([^;\s]+);\s*$")


@dataclass(frozen=True)
class Port:
    kind: str
    width: int
    name: str


def read_top_ports(header_path: Path, dut_name: str) -> List[Port]:
    struct_start = f"typedef struct {dut_name} {{"
    constructor_start = f"{dut_name}() {{"
    inside_struct = False
    inside_port_block = False
    ports: List[Port] = []

    with header_path.open("r", encoding="utf-8", errors="replace") as header:
        for line in header:
            stripped = line.strip()
            if stripped == struct_start:
                inside_struct = True
                continue
            if not inside_struct:
                continue
            if stripped == constructor_start:
                break

            match = _DECLARATION.fullmatch(line)
            if match and match.group(3) == "clock":
                inside_port_block = True
            if inside_port_block:
                if match:
                    kind, width, name = match.groups()
                    ports.append(Port(kind, int(width), name))
                elif stripped:
                    break

    if not ports:
        raise RuntimeError(
            f"unable to find the top-level port block for {dut_name} in {header_path}"
        )
    if not any(port.name == "reset" for port in ports):
        raise RuntimeError(f"top-level reset port not found in {header_path}")
    return ports


def is_output_port(port: Port) -> bool:
    name = port.name.lower()
    return (
        "_out_" in name
        or name.startswith("out_")
        or name.startswith("io_out")
        or name.endswith("_out")
    )


def random_assignment(port: Port) -> str:
    if "valid" in port.name.lower():
        value = "1"
    elif port.kind == "SInt":
        value = "static_cast<int64_t>(random_engine())"
    else:
        value = "random_engine()"
    return f"    dut->{port.name} = {port.kind}<{port.width}>({value});"


def render_driver(header_path: Path, dut_name: str, ports: List[Port]) -> str:
    inputs = [
        port
        for port in ports
        if port.name not in {"clock", "reset"}
        and "_padding" not in port.name.lower()
        and not is_output_port(port)
    ]
    outputs = [port for port in ports if is_output_port(port) and port.kind == "UInt"]
    if not inputs:
        raise RuntimeError(f"no randomizable input ports found for {dut_name}")

    assignments = "\n".join(random_assignment(port) for port in inputs)
    checksum_lines = "\n".join(
        f"    checksum ^= dut->{port.name}.as_single_word();" for port in outputs
    )
    if not checksum_lines:
        checksum_lines = "    checksum ^= 0;"

    return f'''#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <random>

#include "{header_path.name}"

int main(int argc, char** argv) {{
  if (argc != 3) {{
    std::cerr << "Usage: " << argv[0] << " CYCLES SEED\\n";
    return 1;
  }}

  const uint64_t cycles = std::strtoull(argv[1], nullptr, 0);
  const uint64_t seed = std::strtoull(argv[2], nullptr, 0);
  std::mt19937_64 random_engine(seed);
  auto* dut = new {dut_name};

  dut->reset = UInt<1>(1);
  dut->eval(false, false, false);
  for (int cycle = 0; cycle < 5; ++cycle) {{
    dut->eval(true, false, false);
  }}
  dut->reset = UInt<1>(0);
  dut->eval(false, false, false);

  uint64_t checksum = 0;
  const auto start = std::chrono::steady_clock::now();
  for (uint64_t cycle = 0; cycle < cycles; ++cycle) {{
{assignments}
    dut->eval(true, false, true);
{checksum_lines}
  }}
  const auto stop = std::chrono::steady_clock::now();
  const auto elapsed_us =
      std::chrono::duration_cast<std::chrono::microseconds>(stop - start).count();

  std::cout << "cycles: " << cycles << '\\n';
  std::cout << "random_seed: " << seed << '\\n';
  std::cout << "checksum: " << checksum << '\\n';
  std::cout << "elapsed_us: " << elapsed_us << '\\n';

  delete dut;
  return 0;
}}
'''


def generate_random_driver(
    header_path: Path, dut_name: str, output_path: Path
) -> None:
    ports = read_top_ports(header_path, dut_name)
    output_path.write_text(
        render_driver(header_path, dut_name, ports), encoding="utf-8"
    )
    input_count = sum(
        port.name not in {"clock", "reset"}
        and "_padding" not in port.name.lower()
        and not is_output_port(port)
        for port in ports
    )
    output_count = sum(is_output_port(port) for port in ports)
    print(f"generated: {output_path}")
    print(f"top-level ports: {len(ports)}")
    print(f"randomized inputs: {input_count}")
    print(f"observed outputs: {output_count}")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate a simple random C++ driver from an Essent header."
    )
    parser.add_argument("header", type=Path)
    parser.add_argument("dut_name")
    parser.add_argument("output", type=Path)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    try:
        generate_random_driver(args.header, args.dut_name, args.output)
    except (OSError, RuntimeError, ValueError) as error:
        print(f"error: {error}")
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
