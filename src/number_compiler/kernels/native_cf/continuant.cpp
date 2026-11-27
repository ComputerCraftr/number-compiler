#include <Python.h> // IWYU pragma: keep
#include <array>
#include <bytesobject.h>
#include <cstddef>
#include <cstdint>
#include <cstring>
#ifdef __ARM_NEON
#include <arm_neon.h>
#endif

namespace {
struct SmallMatrix {
    std::uint16_t a, b, c, d;
};
constexpr SmallMatrix word_action(unsigned value) {
    unsigned a = 1, b = 0, c = 0, d = 1;
    for (unsigned place = 10; place != 0U; place /= 10) {
        const unsigned digit = value / place;
        value %= place;
        const unsigned next_a = (a * (digit + 1)) + b;
        const unsigned next_c = (c * (digit + 1)) + d;
        b = a;
        a = next_a;
        d = c;
        c = next_c;
    }
    return {
        static_cast<std::uint16_t>(a),
        static_cast<std::uint16_t>(b),
        static_cast<std::uint16_t>(c),
        static_cast<std::uint16_t>(d),
    };
}
constexpr auto make_alphabet() {
    std::array<SmallMatrix, 100> words{};
    for (unsigned i = 0; i < words.size(); ++i) {
        words[i] = word_action(i);
    }
    return words;
}
constexpr auto alphabet = make_alphabet();

struct DecimalWord {
    std::uint64_t value = 0;
    unsigned long width = 0;
    std::uint64_t place = 1;
};

bool parse_word(PyObject *args, DecimalWord &input) {
    PyObject *value_object = nullptr;
    PyObject *width_object = nullptr;
    if (PyArg_ParseTuple(args, "OO", &value_object, &width_object) == 0) {
        return false;
    }
    if (!PyLong_CheckExact(value_object) || !PyLong_CheckExact(width_object)) {
        PyErr_SetString(PyExc_TypeError,
                        "ordered source and width must be integers");
        return false;
    }
    input.value = PyLong_AsUnsignedLongLong(value_object);
    if (PyErr_Occurred() != nullptr) {
        return false;
    }
    input.width = PyLong_AsUnsignedLong(width_object);
    if (PyErr_Occurred() != nullptr) {
        return false;
    }
    if (input.width == 0 || input.width > 16) {
        PyErr_SetString(PyExc_ValueError,
                        "ordered digit width outside native range");
        return false;
    }

    for (unsigned long i = 1; i < input.width; ++i) {
        input.place *= 10;
    }
    if (input.value / input.place >= 10) {
        PyErr_SetString(PyExc_ValueError, "ordered source exceeds digit width");
        return false;
    }
    return true;
}

PyObject *ordered_product(PyObject * /*unused*/, PyObject *args) {
    DecimalWord input;
    if (!parse_word(args, input)) {
        return nullptr;
    }
    auto [value, width, place] = input;
    // Every coefficient is at most 10, so each entry is bounded by 11^16
    // and fits in uint64_t throughout the admitted 16-digit product.
    std::uint64_t a = 1, b = 0, c = 0, d = 1;
    const auto leading = width % 2;
    for (unsigned long i = 0; i < leading; ++i, place /= 10) {
        const auto digit = value / place;
        value %= place;
        const auto next_a = (a * (digit + 1)) + b;
        const auto next_c = (c * (digit + 1)) + d;
        b = a;
        a = next_a;
        d = c;
        c = next_c;
    }
#ifdef __ARM_NEON
    if (width <= 9) {
        // The two lanes are the upper and lower rows of each column.
        // Every entry is at most 11^9, so uint32 lanes are exact here.
        const std::uint32_t first[] = {
            static_cast<std::uint32_t>(a),
            static_cast<std::uint32_t>(c),
        };
        const std::uint32_t second[] = {
            static_cast<std::uint32_t>(b),
            static_cast<std::uint32_t>(d),
        };
        uint32x2_t column0 = vld1_u32(first);
        uint32x2_t column1 = vld1_u32(second);
        while (place != 0U) {
            const auto lower = place / 10;
            const auto index = static_cast<std::size_t>(value / lower);
            value %= lower;
            const auto word = alphabet[index];
            const uint32x2_t next0 =
                vmla_n_u32(vmul_n_u32(column0, word.a), column1, word.c);
            const uint32x2_t next1 =
                vmla_n_u32(vmul_n_u32(column0, word.b), column1, word.d);
            column0 = next0;
            column1 = next1;
            place /= 100;
        }
        a = vget_lane_u32(column0, 0);
        c = vget_lane_u32(column0, 1);
        b = vget_lane_u32(column1, 0);
        d = vget_lane_u32(column1, 1);
    }
#endif
    while (place != 0U) {
        const auto lower = place / 10;
        const auto index = static_cast<std::size_t>(value / lower);
        value %= lower;
        const auto word = alphabet[index];
        const auto next_a = (a * word.a) + (b * word.c);
        const auto next_b = (a * word.b) + (b * word.d);
        const auto next_c = (c * word.a) + (d * word.c);
        const auto next_d = (c * word.b) + (d * word.d);
        a = next_a;
        b = next_b;
        c = next_c;
        d = next_d;
        place /= 100;
    }
    return Py_BuildValue("(KKKK)", static_cast<unsigned long long>(a),
                         static_cast<unsigned long long>(b),
                         static_cast<unsigned long long>(c),
                         static_cast<unsigned long long>(d));
}
// Each 32-byte record is the MSD-first continuant up to this cut. The
// buffer is private to the issuing process and uses its native byte order.
PyObject *ordered_prefix_bank(PyObject * /*unused*/, PyObject *args) {
    DecimalWord input;
    if (!parse_word(args, input)) {
        return nullptr;
    }
    auto [value, width, place] = input;
    using Matrix = std::array<std::uint64_t, 4>;
    constexpr auto record_size = 4 * sizeof(std::uint64_t);
    const auto bytes = static_cast<Py_ssize_t>((width + 1) * record_size);
    PyObject *bank = PyBytes_FromStringAndSize(nullptr, bytes);
    if (bank == nullptr) {
        return nullptr;
    }
    char *record = PyBytes_AsString(bank);
    Matrix matrix{1, 0, 0, 1};
    std::memcpy(record, matrix.data(), record_size);
    auto append = [&](std::uint64_t coefficient) {
        const auto [top, previous_top, bottom, previous_bottom] = matrix;
        matrix = {
            (top * coefficient) + previous_top,
            top,
            (bottom * coefficient) + previous_bottom,
            bottom,
        };
        record += record_size;
        std::memcpy(record, matrix.data(), record_size);
    };
    if (width % 2 != 0) {
        append((value / place) + 1);
        value %= place;
        place /= 10;
    }
    while (place != 0) {
        const auto lower = place / 10;
        const auto pair = alphabet[static_cast<std::size_t>(value / lower)];
        // The off-diagonal entries of A(x)A(y) are x and y in order.
        append(pair.b);
        append(pair.c);
        value %= lower;
        place /= 100;
    }
    return bank;
}

PyMethodDef methods[] = {
    {
        "ordered_product",
        ordered_product,
        METH_VARARGS,
        "Compile a bounded decimal continuant.",
    },
    {
        "ordered_prefix_bank",
        ordered_prefix_bank,
        METH_VARARGS,
        "Compile all ordered prefixes of one bounded decimal word.",
    },
    {nullptr, nullptr, 0, nullptr},
};
PyModuleDef module = {
    PyModuleDef_HEAD_INIT,
    "_cf_continuant",
    nullptr,
    -1,
    methods,
    nullptr,
    nullptr,
    nullptr,
    nullptr,
};
} // namespace
// The CPython extension ABI requires this exact entry point spelling.
// NOLINTBEGIN(bugprone-reserved-identifier)
PyMODINIT_FUNC PyInit__cf_continuant();
PyMODINIT_FUNC PyInit__cf_continuant() { return PyModule_Create(&module); }
// NOLINTEND(bugprone-reserved-identifier)
