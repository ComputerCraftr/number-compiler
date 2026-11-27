"""Check the optional C++20 reversal extension with Clang diagnostics."""

import argparse
import subprocess
import sys
import sysconfig
from pathlib import Path

from devtools.runs import run_reported

_NATIVE = Path("src/number_compiler/kernels/native_reverse")
_WARNINGS = (
    "-Wall",
    "-Wextra",
    "-Wpedantic",
    "-Wcast-qual",
    "-Wconversion",
    "-Wdouble-promotion",
    "-Wfloat-equal",
    "-Wformat=2",
    "-Wimplicit-fallthrough",
    "-Wpointer-arith",
    "-Wsign-conversion",
    "-Wswitch-enum",
    "-Wundef",
    "-Wunused-but-set-parameter",
    "-Wunused-but-set-variable",
    "-Wunused-const-variable",
    "-Wunused-function",
    "-Wunused-local-typedefs",
    "-Wunused-macros",
    "-Wunused-parameter",
    "-Wunused-value",
    "-Wunused-variable",
    "-Wvla",
    "-Wwrite-strings",
    "-Wcast-align",
    "-Wmissing-prototypes",
    "-Wnewline-eof",
    "-Wnull-dereference",
    "-Wshadow-all",
    "-Wunreachable-code",
    "-Wunreachable-code-break",
    "-Wunreachable-code-return",
    "-Wunused-lambda-capture",
    "-Wunused-private-field",
    "-Wunneeded-internal-declaration",
)


def _compile_options() -> list[str]:
    options = ["-std=c++20", "-fPIC", "-DNDEBUG", "-DPY_SSIZE_T_CLEAN"]
    python_headers = dict.fromkeys(
        sysconfig.get_path(layout) for layout in ("include", "platinclude")
    )
    for header in python_headers:
        options.extend(("-isystem", header))
    if sys.platform == "darwin":
        sdk = subprocess.check_output(("xcrun", "--show-sdk-path"), text=True).strip()
        options.extend(("-isysroot", sdk))
    return options


def _portable_warnings(compiler: str) -> list[str]:
    supported: list[str] = []
    for warning in _WARNINGS:
        probe = subprocess.run(
            (compiler, "-Werror", warning, "-x", "c++", "-fsyntax-only", "-"),
            input="",
            capture_output=True,
            text=True,
            check=False,
        )
        if probe.returncode == 0:
            supported.append(warning)
        else:
            print(f"{compiler}: unavailable in C++ mode: {warning}", flush=True)
    return supported


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    compiler_options = parser.add_mutually_exclusive_group()
    compiler_options.add_argument("--llvm-bin", type=Path)
    compiler_options.add_argument(
        "--linux-compiler",
        help="Check a Linux C++ compiler with its supported warnings",
    )
    options = parser.parse_args()
    if options.linux_compiler and sys.platform != "linux":
        parser.error("--linux-compiler requires Linux")
    tools = options.llvm_bin or Path(".")
    clang = str(tools / "clang++")
    clang_format = str(tools / "clang-format")
    clang_tidy = str(tools / "clang-tidy")
    units = sorted(str(source) for source in _NATIVE.glob("[!.]*.cpp"))
    headers = sorted(str(source) for source in _NATIVE.glob("[!.]*.hpp"))
    if not units or not headers:
        parser.error("run from the repository root with the native sources present")
    compile_options = _compile_options()
    try:
        if options.linux_compiler:
            supported = _portable_warnings(options.linux_compiler)
            subprocess.run(
                (
                    options.linux_compiler,
                    *compile_options,
                    *supported,
                    "-Werror",
                    "-fsyntax-only",
                    *units,
                ),
                check=True,
            )
            return 0
        subprocess.run(
            (clang_format, "--dry-run", "--Werror", *units, *headers), check=True
        )
        clang_warnings = (
            _WARNINGS if sys.platform == "darwin" else _portable_warnings(clang)
        )
        subprocess.run(
            (
                clang,
                *compile_options,
                *clang_warnings,
                "-Werror",
                "-Werror=unknown-warning-option",
                "-fsyntax-only",
                *units,
            ),
            check=True,
        )
        subprocess.run((clang_tidy, "--verify-config"), check=True)
        subprocess.run(
            (clang_tidy, *units, "--", *compile_options),
            check=True,
        )
    except (OSError, subprocess.CalledProcessError) as error:
        print(f"Native reversal quality checks failed: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(run_reported(main))
