#include <Python.h>
#include <array>
#include <cstdint>
#if defined(__ARM_NEON)
#include <arm_neon.h>
#endif

namespace {
struct SmallMatrix {
    std::uint16_t a, b, c, d;
};
constexpr SmallMatrix word_action(unsigned value) {
    unsigned a = 1, b = 0, c = 0, d = 1;
    for (unsigned place = 10; place; place /= 10) {
        const unsigned digit = value / place;
        value %= place;
        const unsigned next_a = a * (digit + 1) + b;
        const unsigned next_c = c * (digit + 1) + d;
        b = a;
        a = next_a;
        d = c;
        c = next_c;
    }
    return {static_cast<std::uint16_t>(a), static_cast<std::uint16_t>(b),
            static_cast<std::uint16_t>(c), static_cast<std::uint16_t>(d)};
}
constexpr auto make_alphabet() {
    std::array<SmallMatrix, 100> words{};
    for (unsigned i = 0; i < words.size(); ++i)
        words[i] = word_action(i);
    return words;
}
constexpr auto alphabet = make_alphabet();

PyObject *ordered_product(PyObject *, PyObject *args) {
    PyObject *value_object = nullptr;
    PyObject *width_object = nullptr;
    if (!PyArg_ParseTuple(args, "OO", &value_object, &width_object))
        return nullptr;
    if (!PyLong_CheckExact(value_object) || !PyLong_CheckExact(width_object)) {
        PyErr_SetString(PyExc_TypeError,
                        "ordered source and width must be integers");
        return nullptr;
    }
    auto value = PyLong_AsUnsignedLongLong(value_object);
    if (PyErr_Occurred())
        return nullptr;
    const auto width = PyLong_AsUnsignedLong(width_object);
    if (PyErr_Occurred())
        return nullptr;
    if (width == 0 || width > 16) {
        PyErr_SetString(PyExc_ValueError,
                        "ordered digit width outside native range");
        return nullptr;
    }
    std::uint64_t place = 1;
    for (unsigned long i = 1; i < width; ++i)
        place *= 10;
    if (value / place >= 10) {
        PyErr_SetString(PyExc_ValueError, "ordered source exceeds digit width");
        return nullptr;
    }
    // Every coefficient is at most 10, so each entry is bounded by 11^16
    // and fits in uint64_t throughout the admitted 16-digit product.
    std::uint64_t a = 1, b = 0, c = 0, d = 1;
    const auto leading = width % 2;
    for (unsigned long i = 0; i < leading; ++i, place /= 10) {
        const auto digit = value / place;
        value %= place;
        const auto next_a = a * (digit + 1) + b;
        const auto next_c = c * (digit + 1) + d;
        b = a;
        a = next_a;
        d = c;
        c = next_c;
    }
#if defined(__ARM_NEON)
    if (width <= 9) {
        // The two lanes are the upper and lower rows of each column.
        // Every entry is at most 11^9, so uint32 lanes are exact here.
        const std::uint32_t first[] = {static_cast<std::uint32_t>(a),
                                       static_cast<std::uint32_t>(c)};
        const std::uint32_t second[] = {static_cast<std::uint32_t>(b),
                                        static_cast<std::uint32_t>(d)};
        uint32x2_t column0 = vld1_u32(first);
        uint32x2_t column1 = vld1_u32(second);
        while (place) {
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
    while (place) {
        const auto lower = place / 10;
        const auto index = static_cast<std::size_t>(value / lower);
        value %= lower;
        const auto word = alphabet[index];
        const auto next_a = a * word.a + b * word.c;
        const auto next_b = a * word.b + b * word.d;
        const auto next_c = c * word.a + d * word.c;
        const auto next_d = c * word.b + d * word.d;
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
PyMethodDef methods[] = {{"ordered_product", ordered_product, METH_VARARGS,
                          "Compile a bounded decimal continuant."},
                         {nullptr, nullptr, 0, nullptr}};
PyModuleDef module = {PyModuleDef_HEAD_INIT,
                      "_cf_continuant",
                      nullptr,
                      -1,
                      methods,
                      nullptr,
                      nullptr,
                      nullptr,
                      nullptr};
} // namespace
PyMODINIT_FUNC PyInit__cf_continuant();
PyMODINIT_FUNC PyInit__cf_continuant() { return PyModule_Create(&module); }
