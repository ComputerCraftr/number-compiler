"""Optional bounded native reflected-multiply extension."""

import os

from setuptools import Extension, setup

source = "src/number_compiler/kernels/native_reverse/"
extensions: list[Extension] = []

if os.environ.get("NUMBER_COMPILER_BUILD_REFLECTED_MULTIPLY") == "1":
    extensions.append(
        Extension(
            "number_compiler.kernels._reflected_multiply",
            sources=[
                source + "reflected_multiply_bindings.cpp",
                source + "rev10.cpp",
            ],
            depends=[source + name for name in ("rev10.hpp", "relative_return.hpp", "dense_digitplanes.hpp")],
            define_macros=[("PY_SSIZE_T_CLEAN", None)],
            extra_compile_args=["-std=c++20"],
            language="c++",
        )
    )

if os.environ.get("NUMBER_COMPILER_BUILD_NATIVE_REVERSE") == "1":
    extensions.append(
        Extension(
            "number_compiler.kernels._reverse_quotients",
            sources=[
                source + name
                for name in ("bindings.cpp", "causal_add.cpp", "rev10.cpp")
            ],
            depends=[
                source + name
                for name in (
                    "causal_add.hpp",
                    "small_radix.hpp",
                    "bitplane_word.hpp",
                    "pair_half_kick.hpp",
                    "rev10.hpp",
                    "dense_digitplanes.hpp",
                    "relative_return.hpp",
                    "joint_slab.hpp",
                    "guarded_q19_clock.hpp",
                    "q19_four_tile.hpp",
                )
            ],
            define_macros=[("PY_SSIZE_T_CLEAN", None)],
            extra_compile_args=["-std=c++20"],
            language="c++",
        )
    )

if os.environ.get("NUMBER_COMPILER_BUILD_CF_CONTINUANT") == "1":
    extensions.append(
        Extension(
            "number_compiler.kernels._cf_continuant",
            sources=["src/number_compiler/kernels/native_cf/continuant.cpp"],
            define_macros=[("PY_SSIZE_T_CLEAN", None)],
            extra_compile_args=["-std=c++20"],
            language="c++",
        )
    )

setup(ext_modules=extensions)
