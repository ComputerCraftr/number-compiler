#ifndef NUMBER_COMPILER_SMALL_RADIX_HPP
#define NUMBER_COMPILER_SMALL_RADIX_HPP
#include "bitplane_word.hpp"
#include <cstddef>
// Dense Q3/Q5 Boolean planes; one native carry inverse per 64 columns.
#include <cstdint>
#include <stdexcept>
#include <vector>
namespace small_radix {
using U = std::uint64_t;
struct Result {
    std::vector<std::uint8_t> digits;
    U rows = 0, words = 0, full_words = 0, births = 0;
};
struct Carry {
    U in;
    bool out;
};
inline Carry invert(U generate, U propagate, bool inlet, unsigned count) {
    U low = generate | propagate, partial = low + generate,
      sum = partial + U(inlet);
    return {
        (sum ^ low ^ generate) & bitplane_word::ones(count),
        count == 64 ? (partial < low || sum < partial)
                    : ((sum >> count) & 1U) != 0U,
    };
}
inline U opposite(const std::vector<U> &plane, std::size_t count,
                  std::size_t word, unsigned pad) {
    U low = bitplane_word::reverse_bits(plane[count - 1 - word]);
    if (pad == 0U) {
        return low;
    }
    return (low >> pad) |
           (word + 1 < count
                ? bitplane_word::reverse_bits(plane[count - 2 - word])
                      << (64 - pad)
                : 0);
}
template <int Radix>
Result advance(const std::vector<std::uint8_t> &source, U steps) {
    if (source.empty() || (source.size() > 1 && source.back() == 0)) {
        throw std::invalid_argument("noncanonical source");
    }
    if (steps > 1000000 || source.size() + steps > 4000000 ||
        steps * ((source.size() + steps + 63) / 64) > 200000000ULL) {
        throw std::invalid_argument("small radix word-work budget exceeded");
    }
    std::size_t width = source.size(), cap = (width + steps + 63) / 64;
    std::vector<U> lo(cap), hi(Radix == 3 ? cap : 0), nl(cap),
        nh(Radix == 3 ? cap : 0);
    for (std::size_t i = 0; i < width; ++i) {
        if (source[i] >= Radix) {
            throw std::invalid_argument("invalid digit");
        }
        lo[i / 64] |= U(source[i] & 1U) << (i % 64);
        if constexpr (Radix == 3) {
            hi[i / 64] |= U(source[i] >> 1U) << (i % 64);
        }
    }
    Result result;
    for (U tick = 0; tick < steps; ++tick) {
        const std::size_t count = (width + 63) / 64;
        const unsigned pad = unsigned((count * 64) - width);
        bool carry = false;
        for (std::size_t word = 0; word < count; ++word) {
            const unsigned bits = word + 1 == count ? 64 - pad : 64;
            const U mask = bitplane_word::ones(bits);
            const U low = lo[word],
                    reflected = opposite(lo, count, word, pad) & mask;
            if constexpr (Radix == 2) {
                U eq = low ^ reflected, gt = low & reflected;
                auto carries = invert(gt, eq, carry, bits);
                nl[word] = eq ^ carries.in;
                carry = carries.out;
            } else {
                U a2 = hi[word], b2 = opposite(hi, count, word, pad) & mask,
                  a0 = mask & ~(low | a2), b0 = mask & ~(reflected | b2);
                U eq = (a2 & b0) | (a0 & b2) | (low & reflected),
                  gt = (a2 & reflected) | (low & b2) | (a2 & b2);
                U r1 = (low & b0) | (a0 & reflected) | (a2 & b2),
                  r0 = mask & ~(r1 | eq);
                auto carries = invert(gt, eq, carry, bits);
                nl[word] = (r1 & ~carries.in) | (r0 & carries.in);
                nh[word] = (eq & ~carries.in) | (r1 & carries.in);
                carry = carries.out;
            }
        }
        result.words += count;
        result.full_words += width / 64;
        ++result.rows;
        if (carry) {
            if (width % 64 == 0) {
                nl[count] = 1;
                if constexpr (Radix == 3) {
                    nh[count] = 0;
                }
            } else {
                nl[count - 1] |= U{1} << (width % 64);
            }
            ++width;
            ++result.births;
        }
        lo.swap(nl);
        if constexpr (Radix == 3) {
            hi.swap(nh);
        }
    }
    result.digits.resize(width);
    for (std::size_t i = 0; i < width; ++i) {
        result.digits[i] = std::uint8_t((lo[i / 64] >> (i % 64)) & 1U);
        if constexpr (Radix == 3) {
            result.digits[i] |=
                std::uint8_t(((hi[i / 64] >> (i % 64)) & 1U) << 1U);
        }
    }
    return result;
}
} // namespace small_radix
#endif
