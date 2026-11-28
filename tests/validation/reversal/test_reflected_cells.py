"""Exhaustive decimal arithmetic checks for the shared reflected cell law."""

from pathlib import Path

import pytest

from number_compiler.arithmetic.carry.reflected_h_power import (
    padded_h_cell,
    padded_h_kernel,
)

pytestmark = pytest.mark.validation


@pytest.mark.parametrize("multiplier", (2, 5))
def test_every_ordered_reflected_neighborhood(multiplier: int) -> None:
    compiled = padded_h_kernel(multiplier)
    for previous in range(100):
        for current in range(100):
            ordinary = multiplier * (100 * current + previous)
            carry_from_tens = multiplier * (ordinary // 10 % 10)
            carry_from_hundreds = multiplier * (ordinary // 100 % 10)
            carry_from_thousands = multiplier * (ordinary // 1000 % 10)
            low = carry_from_hundreds // 10 + carry_from_tens % 10
            high = carry_from_thousands // 10 + carry_from_hundreds % 10
            expected = 10 * high + low
            assert padded_h_cell(previous, current, multiplier) == expected
            assert compiled(previous, current) == expected


def test_native_relative_gate_matches_python_and_physical_arithmetic(
    tmp_path: Path,
) -> None:
    """Check the executing C++ miter over all ordered decimal inlets."""
    import shutil
    import subprocess

    from number_compiler.sequences.double_reverse.stencil_moore import stencil_cell

    compiler = shutil.which("clang++") or shutil.which("g++")
    if compiler is None:
        pytest.skip("C++ compiler is unavailable")

    header = (
        Path(__file__).resolve().parents[3]
        / "src/number_compiler/kernels/native_reverse/relative_return.hpp"
    )
    source = tmp_path / "relative_cells.cpp"
    executable = tmp_path / "relative_cells"
    source.write_text(
        '#include "relative_return.hpp"\n'
        "#include <cstdio>\n"
        "#include <initializer_list>\n"
        "int main() {\n"
        "  for (int m : {2, 5})\n"
        "    for (int a = 0; a < 10; ++a)\n"
        "      for (int b = 0; b < 10; ++b)\n"
        "        for (int c = 0; c < 10; ++c)\n"
        "          std::putchar('0' + rev10::relative_cell(m, 10 / m, a, b, c));\n"
        "}\n",
        encoding="ascii",
    )
    subprocess.run(
        [
            compiler,
            "-std=c++20",
            "-I",
            str(header.parent),
            str(source),
            "-o",
            str(executable),
        ],
        check=True,
        capture_output=True,
        timeout=60,
    )
    actual = subprocess.run(
        [str(executable)], check=True, capture_output=True, timeout=60
    ).stdout
    assert len(actual) == 2000
    index = 0
    for multiplier in (2, 5):
        base = 10 // multiplier
        for left in range(10):
            for center in range(10):
                for right in range(10):
                    first = multiplier * (center % base) + left // base
                    next_first = multiplier * (right % base) + center // base
                    expected = multiplier * (first % base) + next_first // base
                    assert actual[index] - ord("0") == expected
                    if multiplier == 2:
                        assert stencil_cell(left, center, right) == expected
                    index += 1
