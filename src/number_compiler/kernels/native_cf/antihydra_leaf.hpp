#ifndef NUMBER_COMPILER_ANTIHYDRA_LEAF_HPP
#define NUMBER_COMPILER_ANTIHYDRA_LEAF_HPP

#include <Python.h> // IWYU pragma: keep

#if defined(__SIZEOF_INT128__) && PY_VERSION_HEX >= 0x030D0000
namespace number_compiler {
PyObject *antihydra_leaf(PyObject *self, PyObject *args);
}
#endif

#endif
