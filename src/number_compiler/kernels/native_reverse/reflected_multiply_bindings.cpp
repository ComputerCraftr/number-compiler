#include "rev10.hpp"
#include <Python.h>
#include <exception>
#include <new>
#include <string>

namespace {
PyObject *multiply(PyObject *, PyObject *args) {
    const char *data = nullptr;
    Py_ssize_t size = 0;
    long long steps = 0;
    if (!PyArg_ParseTuple(args, "s#L", &data, &size, &steps))
        return nullptr;
    if (size < 1 || size > 262144 || steps < 128 || steps > 8192) {
        PyErr_SetString(PyExc_ValueError,
                        "reflected multiply exceeds bounded geometry");
        return nullptr;
    }
    try {
        const auto result =
            rev10::nth(std::string(data, static_cast<std::size_t>(size)), 2,
                       steps, "diagonal", 3);
        if (PyErr_CheckSignals() < 0)
            return nullptr;
        return PyUnicode_FromStringAndSize(
            result.digits.data(),
            static_cast<Py_ssize_t>(result.digits.size()));
    } catch (const std::bad_alloc &) {
        return PyErr_NoMemory();
    } catch (const std::exception &error) {
        PyErr_SetString(PyExc_ValueError, error.what());
        return nullptr;
    }
}
PyMethodDef methods[] = {
    {"multiply", multiply, METH_VARARGS, "Bounded reflected multiply."},
    {nullptr, nullptr, 0, nullptr}};
PyModuleDef module = {PyModuleDef_HEAD_INIT,
                      "_reflected_multiply",
                      nullptr,
                      -1,
                      methods,
                      nullptr,
                      nullptr,
                      nullptr,
                      nullptr};
} // namespace
PyMODINIT_FUNC PyInit__reflected_multiply() { return PyModule_Create(&module); }
