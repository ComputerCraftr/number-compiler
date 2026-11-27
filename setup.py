"""Optional bounded native reflected-multiply extension."""

import os

from setuptools import Extension, setup

if os.environ.get("NUMBER_COMPILER_BUILD_REFLECTED_MULTIPLY") == "1":
    source = "src/number_compiler/kernels/native_reverse/"
    setup(
        ext_modules=[
            Extension(
                "number_compiler.kernels._reflected_multiply",
                sources=[
                    source + "reflected_multiply_bindings.cpp",
                    source + "rev10.cpp",
                ],
                depends=[source + "rev10.hpp"],
                define_macros=[("PY_SSIZE_T_CLEAN", None)],
                extra_compile_args=["-std=c++20"],
                language="c++",
            )
        ]
    )
else:
    setup()
