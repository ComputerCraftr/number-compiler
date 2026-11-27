#include <Python.h> // IWYU pragma: keep

#include "causal_add.hpp"
#include "rev10.hpp"

#include <cstddef>
#include <cstdint>
#include <exception>
#include <new>
#include <string>
#include <utility>
#include <vector>

namespace {

std::vector<std::uint8_t> symbols(const char *data, Py_ssize_t size) {
    return {data, data + size};
}

void translate_exception(std::exception_ptr error) {
    try {
        std::rethrow_exception(std::move(error));
    } catch (const std::bad_alloc &) {
        PyErr_NoMemory();
    } catch (const std::exception &failure) {
        PyErr_SetString(PyExc_ValueError, failure.what());
    } catch (...) {
        PyErr_SetString(PyExc_RuntimeError, "unknown native reversal failure");
    }
}

PyObject *multiply(PyObject * /*unused*/, PyObject *args) {
    const char *source = nullptr;
    Py_ssize_t size = 0;
    int multiplier = 0;
    long long steps = 0;
    int side = 0;
    if (PyArg_ParseTuple(args, "s#iLi", &source, &size, &multiplier, &steps,
                         &side) == 0) {
        return nullptr;
    }
    if ((side != 3 && side != 4) || steps < 0 || steps > 1000000 || size < 0 ||
        size > 32000000) {
        PyErr_SetString(PyExc_ValueError,
                        "native diagonal exceeds its finite limits");
        return nullptr;
    }
    try {
        const auto result =
            rev10::nth(std::string(source, static_cast<std::size_t>(size)),
                       multiplier, steps, "diagonal", side);
        if (PyErr_CheckSignals() < 0) {
            return nullptr;
        }
        const auto &work = result.stats;
        return Py_BuildValue(
            "s#(KKKKKKdd)", result.digits.data(),
            static_cast<Py_ssize_t>(result.digits.size()),
            static_cast<unsigned long long>(work.tiles),
            static_cast<unsigned long long>(work.fringe_gates),
            static_cast<unsigned long long>(work.rows),
            static_cast<unsigned long long>(work.word_updates),
            static_cast<unsigned long long>(work.table_entries),
            static_cast<unsigned long long>(work.table_bytes +
                                            work.table_aux_bytes),
            work.setup_ms, work.eval_ms);
    } catch (...) {
        translate_exception(std::current_exception());
        return nullptr;
    }
}

PyObject *add(PyObject * /*unused*/, PyObject *args) {
    const char *source = nullptr;
    Py_ssize_t size = 0;
    unsigned long long steps = 0;
    unsigned long long cap = 0;
    int height = 0;
    int width = 0;
    if (PyArg_ParseTuple(args, "y#KiiK", &source, &size, &steps, &height,
                         &width, &cap) == 0) {
        return nullptr;
    }
    if (steps > 65536 || cap == 0 || cap > 4ULL * 1024 * 1024) {
        PyErr_SetString(PyExc_ValueError,
                        "native causal band exceeds its finite limits");
        return nullptr;
    }
    try {
        const auto result = causal_add::advance(symbols(source, size), steps,
                                                height, width, cap, false);
        if (PyErr_CheckSignals() < 0) {
            return nullptr;
        }
        const auto &work = result.work;
        return Py_BuildValue(
            "y#(KKKKKK)", reinterpret_cast<const char *>(result.pairs.data()),
            static_cast<Py_ssize_t>(result.pairs.size()),
            static_cast<unsigned long long>(work.states),
            static_cast<unsigned long long>(work.bands),
            static_cast<unsigned long long>(work.joins),
            static_cast<unsigned long long>(work.pulls),
            static_cast<unsigned long long>(work.births),
            static_cast<unsigned long long>(work.peak_table_bytes));
    } catch (...) {
        translate_exception(std::current_exception());
        return nullptr;
    }
}

PyObject *guard98(PyObject * /*unused*/, PyObject *args) {
    const char *source = nullptr;
    Py_ssize_t size = 0;
    int returns = 0;
    int endpoint = 0;
    unsigned long long cap = 0;
    if (PyArg_ParseTuple(args, "y#ipK", &source, &size, &returns, &endpoint,
                         &cap) == 0) {
        return nullptr;
    }
    if (returns < 1 || returns > 512 || cap < 1 || cap > 8192) {
        PyErr_SetString(PyExc_ValueError,
                        "native border guard exceeds its finite limits");
        return nullptr;
    }
    try {
        const auto result = causal_add::guard98(symbols(source, size), returns,
                                                endpoint != 0, cap);
        if (PyErr_CheckSignals() < 0) {
            return nullptr;
        }
        return Py_BuildValue("IKK", result.mask,
                             static_cast<unsigned long long>(result.nodes),
                             static_cast<unsigned long long>(result.appends));
    } catch (...) {
        translate_exception(std::current_exception());
        return nullptr;
    }
}

PyMethodDef methods[] = {
    {
        "multiply",
        multiply,
        METH_VARARGS,
        "Compute a bounded diagonal endpoint.",
    },
    {"add", add, METH_VARARGS, "Compute a bounded causal pair field."},
    {
        "guard98",
        guard98,
        METH_VARARGS,
        "Project the bounded conditional border guard.",
    },
    {nullptr, nullptr, 0, nullptr},
};

PyModuleDef module = {
    PyModuleDef_HEAD_INIT,
    "_reverse_quotients",
    nullptr,
    -1,
    methods,
    nullptr,
    nullptr,
    nullptr,
    nullptr,
};

} // namespace

// The CPython loader requires this exact module initialization symbol.
PyMODINIT_FUNC
PyInit__reverse_quotients(); // NOLINT(bugprone-reserved-identifier)

PyMODINIT_FUNC PyInit__reverse_quotients() { return PyModule_Create(&module); }
