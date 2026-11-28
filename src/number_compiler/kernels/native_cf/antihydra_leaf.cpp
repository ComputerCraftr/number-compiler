#include "antihydra_leaf.hpp"
#include <patchlevel.h>
#if defined(__SIZEOF_INT128__) && PY_VERSION_HEX >= 0x030D0000
#include <Python.h> // IWYU pragma: keep
#if __has_include(<refcount.h>)
#include <refcount.h>
#endif
#include <algorithm>
#include <array>
#include <bit>
#include <cstddef>
#include <cstdint>

namespace {
constexpr int leaf_ticks = 8;
constexpr int max_ticks = 128;
constexpr std::uint32_t leaf_gain = 6561;
using Limbs = std::array<std::uint64_t, 4>;

struct Leaf {
    std::uint32_t bias = 0;
    int delta = 0;
    int minimum = 0;
    int odd = 0;
};

constexpr auto carry_sheet() {
    std::array<Leaf, 256> sheet{};
    for (std::uint32_t inlet = 0; inlet < sheet.size(); ++inlet) {
        auto &leaf = sheet[inlet];
        leaf.bias = inlet;
        for (int tick = 0; tick < leaf_ticks; ++tick) {
            const int parity = static_cast<int>(leaf.bias & 1U);
            leaf.bias = (3U * leaf.bias) >> 1U;
            leaf.delta += 2 - (3 * parity);
            leaf.minimum = std::min(leaf.minimum, leaf.delta);
            leaf.odd += parity;
        }
    }
    return sheet;
}

constexpr auto responses = carry_sheet();

int bits(const Limbs &value) {
    for (std::size_t position = value.size(); position != 0; --position) {
        const auto width = std::bit_width(value[position - 1]);
        if (width != 0U) {
            return static_cast<int>(64 * (position - 1)) +
                   static_cast<int>(width);
        }
    }
    return 0;
}

// Apply the bounded low response to the upper quotient in place. The
// unmodified next limb supplies the fractional cut at each word boundary.
void advance(Limbs &value, unsigned shift, std::uint32_t gain,
             std::uint32_t bias) {
    std::uint64_t carry = bias;
    for (std::size_t i = 0; i < value.size(); ++i) {
        const auto high =
            i + 1 < value.size() ? value[i + 1] << (64U - shift) : 0U;
        const auto low = (value[i] >> shift) | high;
        const auto product = (static_cast<__uint128_t>(gain) * low) + carry;
        value[i] = static_cast<std::uint64_t>(product);
        carry = static_cast<std::uint64_t>(product >> 64U);
    }
}

struct LeafResult {
    int delta = 0;
    int minimum = 0;
    int odd = 0;
    int actions = 0;
    int operand_bits = 0;
};

LeafResult fold_leaf(Limbs &value, int ticks) {
    LeafResult result;
    for (; ticks >= leaf_ticks; ticks -= leaf_ticks) {
        const auto &leaf = responses[value.front() & 255U];
        const int old_bits = bits(value);
        advance(value, leaf_ticks, leaf_gain, leaf.bias);
        result.minimum = std::min(result.minimum, result.delta + leaf.minimum);
        result.delta += leaf.delta;
        result.odd += leaf.odd;
        result.operand_bits += old_bits + bits(value) + leaf_ticks;
        ++result.actions;
    }
    for (; ticks > 0; --ticks) {
        const auto parity = static_cast<std::uint32_t>(value.front() & 1U);
        advance(value, 1, 3, parity);
        result.delta += 2 - (3 * static_cast<int>(parity));
        result.minimum = std::min(result.minimum, result.delta);
        result.odd += static_cast<int>(parity);
        result.operand_bits += bits(value) + 1;
    }
    return result;
}
} // namespace

PyObject *number_compiler::antihydra_leaf(PyObject * /*self*/, PyObject *args) {
    if constexpr (std::endian::native != std::endian::little) {
        return Py_NewRef(Py_None);
    }
    PyObject *source = nullptr;
    PyObject *horizon = nullptr;
    if (PyArg_ParseTuple(args, "OO", &source, &horizon) == 0) {
        return nullptr;
    }
    if (!PyLong_CheckExact(source) || !PyLong_CheckExact(horizon)) {
        PyErr_SetString(PyExc_TypeError,
                        "leaf source and horizon must be exact integers");
        return nullptr;
    }
    const auto ticks = PyLong_AsLong(horizon);
    if (PyErr_Occurred() != nullptr) {
        return nullptr;
    }
    if (ticks < 0 || ticks > max_ticks) {
        PyErr_SetString(PyExc_ValueError,
                        "native leaf horizon exceeds its bound");
        return nullptr;
    }
    Limbs value{};
    constexpr int flags = Py_ASNATIVEBYTES_LITTLE_ENDIAN |
                          Py_ASNATIVEBYTES_UNSIGNED_BUFFER |
                          Py_ASNATIVEBYTES_REJECT_NEGATIVE;
    const auto bytes =
        PyLong_AsNativeBytes(source, value.data(), sizeof(value), flags);
    if (bytes < 0) {
        return nullptr;
    }
    // One physical return increases the bit length by at most one.
    if (bytes > static_cast<Py_ssize_t>(sizeof(value)) ||
        bits(value) + ticks > 256) {
        PyErr_SetString(PyExc_ValueError,
                        "native leaf source exceeds fixed precision");
        return nullptr;
    }
    const auto result = fold_leaf(value, static_cast<int>(ticks));
    PyObject *endpoint = PyLong_FromUnsignedNativeBytes(
        value.data(), sizeof(value), Py_ASNATIVEBYTES_LITTLE_ENDIAN);
    if (endpoint == nullptr) {
        return nullptr;
    }
    return Py_BuildValue("Niiiii", endpoint, result.delta, result.minimum,
                         result.odd, result.actions, result.operand_bits);
}
#endif
