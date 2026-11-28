#include "rev10.hpp"
#include <Python.h> // IWYU pragma: keep
#include <cstddef>
#include <exception>
#include <new>
#include <string>

// CPython derives this symbol from the extension module name.
// NOLINTNEXTLINE(bugprone-reserved-identifier)
PyMODINIT_FUNC PyInit__reflected_multiply();

namespace {
PyObject *multiply_impl(PyObject *args, int report_work) {
    const char *data = nullptr;
    Py_ssize_t size = 0;
    long long steps = 0;
    if (PyArg_ParseTuple(args, "s#L", &data, &size, &steps) == 0) {
        return nullptr;
    }
    if (size < 1 || size > 262144 || steps < 128 || steps > 8192) {
        PyErr_SetString(PyExc_ValueError,
                        "reflected multiply exceeds bounded geometry");
        return nullptr;
    }
    try {
        const auto result =
            rev10::nth(std::string(data, static_cast<std::size_t>(size)), 2,
                       steps, "diagonal", 3);
        if (PyErr_CheckSignals() < 0) {
            return nullptr;
        }
        if (report_work == 2) {
            return Py_BuildValue(
                "s#KKKKKK", result.digits.data(),
                static_cast<Py_ssize_t>(result.digits.size()),
                static_cast<unsigned long long>(result.stats.word_updates),
                static_cast<unsigned long long>(result.stats.front_columns),
                static_cast<unsigned long long>(result.stats.front_probes),
                static_cast<unsigned long long>(result.stats.train_columns),
                static_cast<unsigned long long>(
                    result.stats.train_words_skipped),
                static_cast<unsigned long long>(
                    result.stats.train_ready_lookups));
        }
        if (report_work == 1) {
            return Py_BuildValue(
                "s#K", result.digits.data(),
                static_cast<Py_ssize_t>(result.digits.size()),
                static_cast<unsigned long long>(result.stats.word_updates));
        }
        return Py_BuildValue("s#", result.digits.data(),
                             static_cast<Py_ssize_t>(result.digits.size()));
    } catch (const std::bad_alloc &) {
        return PyErr_NoMemory();
    } catch (const std::exception &error) {
        PyErr_SetString(PyExc_ValueError, error.what());
        return nullptr;
    }
}
PyObject *multiply(PyObject * /*unused*/, PyObject *args) {
    return multiply_impl(args, 0);
}
PyObject *multiply_profiled(PyObject * /*unused*/, PyObject *args) {
    return multiply_impl(args, 1);
}
PyObject *multiply_front_profiled(PyObject * /*unused*/, PyObject *args) {
    return multiply_impl(args, 2);
}
PyMethodDef methods[] = {
    {
        "multiply_front_profiled",
        multiply_front_profiled,
        METH_VARARGS,
        "Bounded reflected multiply with periodic front work.",
    },
    {
        "multiply_profiled",
        multiply_profiled,
        METH_VARARGS,
        "Bounded reflected multiply with dense word work.",
    },
    {"multiply", multiply, METH_VARARGS, "Bounded reflected multiply."},
    {nullptr, nullptr, 0, nullptr},
};
PyModuleDef module = {
    PyModuleDef_HEAD_INIT,
    "_reflected_multiply",
    nullptr,
    -1,
    methods,
    nullptr,
    nullptr,
    nullptr,
    nullptr,
};
} // namespace
PyMODINIT_FUNC PyInit__reflected_multiply() { return PyModule_Create(&module); }
