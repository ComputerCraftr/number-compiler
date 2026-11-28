#include "antihydra_leaf.hpp"
#include <Python.h> // IWYU pragma: keep
#include <array>
#include <bytesobject.h>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <patchlevel.h>
#if defined(__SIZEOF_INT128__) && PY_VERSION_HEX >= 0x030D0000
#if __has_include(<refcount.h>)
#include <refcount.h>
#endif
#include <tupleobject.h>
#endif
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
PyObject *prefix_bank(DecimalWord input) {
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

PyObject *ordered_prefix_bank(PyObject * /*unused*/, PyObject *args) {
    DecimalWord input;
    return parse_word(args, input) ? prefix_bank(input) : nullptr;
}
#if defined(__SIZEOF_INT128__) && PY_VERSION_HEX >= 0x030D0000
// Two adjacent rows can share their base-100 input. At the settled cut,
// 5^n mod 10^6 = 15625 * (5^(n-6) mod 64). The high part of five
// times that suffix is exactly the inlet to the successor head.
using Row = std::array<std::uint64_t, 4>;
constexpr Row prepend(SmallMatrix word, Row row) {
    const auto [top, prior, bottom, previous] = row;
    return {
        (word.a * top) + (word.b * bottom),
        (word.a * prior) + (word.b * previous),
        (word.c * top) + (word.d * bottom),
        (word.c * prior) + (word.d * previous),
    };
}
struct Suffix {
    Row matrix;
    unsigned low, carry;
};
constexpr auto settled_phases() {
    std::array<Suffix, 16> result{};
    unsigned residue = 1;
    for (auto &phase : result) {
        unsigned value = 15625 * residue;
        phase.low = value;
        phase.carry = (5 * value) / 1000000;
        Row row{1, 0, 0, 1};
        for (unsigned pair = 0; pair < 3; ++pair) {
            row = prepend(alphabet[value % 100], row);
            value /= 100;
        }
        phase.matrix = row;
        residue = (5 * residue) % 64;
    }
    return result;
}
constexpr auto suffixes = settled_phases();
struct CarryWord {
    SmallMatrix matrix;
    unsigned carry;
};
constexpr auto successor_words() {
    std::array<CarryWord, 500> result{};
    for (unsigned input = 0; input < result.size(); ++input) {
        result[input] = {alphabet[input % 100], input / 100};
    }
    return result;
}
constexpr auto successors = successor_words();
constexpr SmallMatrix single(unsigned digit) {
    return {static_cast<std::uint16_t>(digit + 1), 1, 1, 0};
}
// 11^18 < 2^64 for each row; the complete two-row product is bounded
// by 11^36 < 2^128. Keep both rows in physical order and retain zeros.
using Wide = __uint128_t;
PyObject *integer(Wide value) {
    if (value <= UINT64_MAX) {
        return PyLong_FromUnsignedLongLong(
            static_cast<unsigned long long>(value));
    }
    return PyLong_FromUnsignedNativeBytes(&value, sizeof(value), -1);
}
struct PairedRows {
    Row old_row, next_row;
    unsigned carry;
};
PairedRows lower_rows(std::uint64_t head, unsigned width, unsigned phase) {
    Row old_row = suffixes[phase].matrix;
    Row next_row = suffixes[(phase + 1) % 16].matrix;
    unsigned carry = suffixes[phase].carry;
    for (unsigned remaining = width - 6; remaining >= 2; remaining -= 2) {
        const auto digits = static_cast<unsigned>(head % 100);
        head /= 100;
        const auto response = successors[(5 * digits) + carry];
        old_row = prepend(alphabet[digits], old_row);
        next_row = prepend(response.matrix, next_row);
        carry = response.carry;
    }
    if (width % 2 != 0) {
        const auto digit = static_cast<unsigned>(head);
        const unsigned updated = (5 * digit) + carry;
        old_row = prepend(single(digit), old_row);
        next_row = prepend(single(updated % 10), next_row);
        carry = updated / 10;
    }
    return {old_row, next_row, carry};
}
PyObject *join_rows(Row old_row, Row next_row) {
    const auto [left00, left01, left10, left11] = old_row;
    const auto [right00, right01, right10, right11] = next_row;
    return Py_BuildValue(
        "(NNNN)", integer((Wide{left00} * right00) + (Wide{left01} * right10)),
        integer((Wide{left00} * right01) + (Wide{left01} * right11)),
        integer((Wide{left10} * right00) + (Wide{left11} * right10)),
        integer((Wide{left10} * right01) + (Wide{left11} * right11)));
}
PyObject *pair_action(std::uint64_t head, unsigned width, unsigned phase,
                      unsigned next_width) {
    auto [old_row, next_row, carry] = lower_rows(head, width, phase);
    if (width + static_cast<unsigned>(carry != 0) != next_width) {
        PyErr_SetString(PyExc_ValueError,
                        "successor width disagrees with carry");
        return nullptr;
    }
    if (carry != 0) {
        next_row = prepend(single(carry), next_row);
    }
    return join_rows(old_row, next_row);
}
PyObject *settled_four(PyObject * /*unused*/, PyObject *args) {
    PyObject *source_object = nullptr, *widths = nullptr,
             *phase_object = nullptr;
    if (PyArg_ParseTuple(args, "OOO", &source_object, &widths, &phase_object) ==
        0) {
        return nullptr;
    }
    if (!PyLong_CheckExact(source_object) || !PyLong_CheckExact(phase_object) ||
        !PyTuple_CheckExact(widths) || PyTuple_Size(widths) != 4) {
        PyErr_SetString(PyExc_TypeError,
                        "expected a source, four widths and a phase");
        return nullptr;
    }
    const auto source = PyLong_AsUnsignedLongLong(source_object);
    const auto phase = PyLong_AsUnsignedLong(phase_object);
    if (PyErr_Occurred() != nullptr) {
        return nullptr;
    }
    if (phase >= 16 || source > 999999999999999999ULL) {
        PyErr_SetString(PyExc_ValueError,
                        "settled source or phase outside its bound");
        return nullptr;
    }
    std::array<unsigned, 4> sizes{};
    std::uint64_t value = source;
    std::uint64_t place = 1000000;
    unsigned width = 7;
    for (unsigned i = 0; i < sizes.size(); ++i) {
        while (value / place >= 10) {
            place *= 10;
            ++width;
        }
        auto *item = PyTuple_GetItem(widths, i);
        if (!PyLong_CheckExact(item)) {
            PyErr_SetString(PyExc_TypeError, "physical width must be integral");
            return nullptr;
        }
        const auto stated = PyLong_AsUnsignedLong(item);
        if (PyErr_Occurred() != nullptr) {
            return nullptr;
        }
        if (width != stated || width > 18 || value < 1000000 ||
            (i == 0 && value % 1000000 != suffixes[phase].low)) {
            Py_RETURN_NONE;
        }
        sizes[i] = width;
        if (i < 3) {
            value *= 5;
        }
    }
    PyObject *first = pair_action(source / 1000000, sizes[0],
                                  static_cast<unsigned>(phase), sizes[1]);
    if (first == nullptr) {
        return nullptr;
    }
    PyObject *second =
        pair_action(25 * source / 1000000, sizes[2],
                    static_cast<unsigned>((phase + 2) % 16), sizes[3]);
    if (second == nullptr) {
        Py_DECREF(first);
        return nullptr;
    }
    return Py_BuildValue("(NN)", first, second);
}

constexpr auto decimal_places() {
    std::array<std::uint64_t, 19> places{};
    places[0] = 1;
    for (std::size_t i = 1; i < places.size(); ++i) {
        places[i] = 10 * places[i - 1];
    }
    return places;
}
constexpr auto places = decimal_places();

// The ledger has already admitted the indexed successor prefix. Split both
// rows at its lower edge. Only the successor's upper word needs a prefix bank.
PyObject *indexed_pair(PyObject * /*unused*/, PyObject *args) {
    PyObject *high_obj = nullptr, *low_obj = nullptr, *width_obj = nullptr,
             *next_obj = nullptr, *phase_obj = nullptr;
    if (PyArg_ParseTuple(args, "OOOOO", &high_obj, &low_obj, &width_obj,
                         &next_obj, &phase_obj) == 0) {
        return nullptr;
    }
    for (auto *obj : {high_obj, low_obj, width_obj, next_obj, phase_obj}) {
        if (!PyLong_CheckExact(obj)) {
            PyErr_SetString(PyExc_TypeError,
                            "expected integral indexed pair inputs");
            return nullptr;
        }
    }
    const auto high = PyLong_AsUnsignedLongLong(high_obj);
    const auto low = PyLong_AsUnsignedLongLong(low_obj);
    const auto width = PyLong_AsUnsignedLong(width_obj);
    const auto next = PyLong_AsUnsignedLong(next_obj);
    const auto phase = PyLong_AsUnsignedLong(phase_obj);
    if (PyErr_Occurred() != nullptr) {
        return nullptr;
    }
    if (next < 28 || next > 32 || width > next || width + 1 < next ||
        phase >= 16) {
        PyErr_SetString(PyExc_ValueError,
                        "indexed pair outside the admitted geometry");
        return nullptr;
    }
    const unsigned indexed = static_cast<unsigned>(next / 2);
    const unsigned lower = static_cast<unsigned>(next) - indexed;
    const unsigned upper = static_cast<unsigned>(width) - lower;
    if (high < places[upper - 1] || high >= places[upper] ||
        low >= places[lower] || low % 1000000 != suffixes[phase].low) {
        Py_RETURN_NONE;
    }
    auto [lower_old, lower_next, carry] =
        lower_rows(low / 1000000, lower, static_cast<unsigned>(phase));
    const auto next_high = (5 * high) + carry;
    if (next_high < places[indexed - 1] || next_high >= places[indexed]) {
        Py_RETURN_NONE;
    }
    PyObject *bank = prefix_bank({next_high, indexed, places[indexed - 1]});
    if (bank == nullptr) {
        return nullptr;
    }
    Row upper_next{};
    std::memcpy(upper_next.data(),
                PyBytes_AsString(bank) + (indexed * sizeof(Row)), sizeof(Row));
    Row upper_old{1, 0, 0, 1};
    auto digits = high;
    for (unsigned remaining = upper; remaining >= 2; remaining -= 2) {
        upper_old = prepend(alphabet[digits % 100], upper_old);
        digits /= 100;
    }
    if (upper % 2 != 0) {
        upper_old = prepend(single(static_cast<unsigned>(digits)), upper_old);
    }
    return Py_BuildValue("(NNN)", join_rows(upper_old, lower_old),
                         join_rows(upper_next, lower_next), bank);
}
#endif

PyMethodDef methods[] = {
#if defined(__SIZEOF_INT128__) && PY_VERSION_HEX >= 0x030D0000
    {
        "antihydra_leaf",
        number_compiler::antihydra_leaf,
        METH_VARARGS,
        "Fold a bounded Antihydra return leaf with its ordered safety minimum.",
    },
    {
        "indexed_pair",
        indexed_pair,
        METH_VARARGS,
        "Compile both rows and the admitted successor prefixes.",
    },
    {
        "settled_four",
        settled_four,
        METH_VARARGS,
        "Compile two ordered pairs of settled rows.",
    },
#endif
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
