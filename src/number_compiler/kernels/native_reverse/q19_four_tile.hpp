#ifndef NUMBER_COMPILER_NATIVE_Q19_FOUR_TILE_HPP
#define NUMBER_COMPILER_NATIVE_Q19_FOUR_TILE_HPP

#include "guarded_q19_clock.hpp"

#include <algorithm>
#include <array>
#include <bit>
#include <cstddef>
#include <cstdint>
#include <span>
#include <vector>

namespace causal_add::q19_tile {

using Word = std::uint64_t;
using Planes = std::array<Word, 5>;

constexpr Word ones(unsigned n) {
    return n == 64U ? ~Word{0} : (Word{1} << n) - 1U;
}

constexpr Word reverse_bits(Word word) {
    word = ((word >> 1U) & 0x5555555555555555ULL) |
           ((word & 0x5555555555555555ULL) << 1U);
    word = ((word >> 2U) & 0x3333333333333333ULL) |
           ((word & 0x3333333333333333ULL) << 2U);
    word = ((word >> 4U) & 0x0f0f0f0f0f0f0f0fULL) |
           ((word & 0x0f0f0f0f0f0f0f0fULL) << 4U);
    word = ((word >> 8U) & 0x00ff00ff00ff00ffULL) |
           ((word & 0x00ff00ff00ff00ffULL) << 8U);
    word = ((word >> 16U) & 0x0000ffff0000ffffULL) |
           ((word & 0x0000ffff0000ffffULL) << 16U);
    return (word >> 32U) | (word << 32U);
}

struct Field {
    std::size_t width = 0;
    std::vector<Planes> words;

    explicit Field(std::size_t physical_width)
        : width(physical_width),
          words(((((physical_width + 1U) / 2U) + 63U) / 64U)) {}

    void put(std::size_t index, unsigned value) {
        for (unsigned bit = 0; bit < 5; ++bit) {
            words[index / 64U][bit] |= Word((value >> bit) & 1U)
                                       << (index % 64U);
        }
    }

    unsigned get(std::size_t index) const {
        unsigned result = 0;
        for (unsigned bit = 0; bit < 5; ++bit) {
            result |= unsigned((words[index / 64U][bit] >> (index % 64U)) & 1U)
                      << bit;
        }
        return result;
    }

    Word window(std::size_t start, unsigned bit) const {
        const auto block = start / 64U;
        const auto shift = unsigned(start % 64U);
        Word result = words[block][bit] >> shift;
        if (shift != 0U && block + 1U < words.size()) {
            result |= words[block + 1U][bit] << (64U - shift);
        }
        return result;
    }

    // Read the physical field in exterior-to-center order, reflecting only
    // where the requested 64-column window crosses the physical midpoint.
    Planes source(std::size_t start) const {
        Planes result{};
        const auto half = (width + 1U) / 2U;
        const auto left = unsigned(std::min<std::size_t>(64U, half - start));
        const auto right =
            unsigned(std::min<std::size_t>(64U - left, width - start - left));
        for (unsigned bit = 0; bit < 5; ++bit) {
            if (left != 0U) {
                result[bit] = window(start, bit) & ones(left);
            }
            if (right != 0U) {
                const auto mirrored = width - start - left - right;
                const Word back = window(mirrored, bit) & ones(right);
                result[bit] |= (reverse_bits(back) >> (64U - right)) << left;
            }
        }
        return result;
    }
};

struct Work {
    std::uint64_t attempts = 0, actions = 0, tiles = 0, refused = 0;
    std::uint64_t converted_pairs = 0, peak_bytes = 0;
};

// One stage over bitplanes. A valid output interval starts after the first
// exact carry reset and ends before the final reset, with a birth extending
// the latter by one. The outer boundary has a known zero carry inlet.
inline Planes advance(Planes x, bool birth, bool outer, int &lo, int &hi) {
    const auto [bit_zero, bit_one, bit_two, bit_three, bit_four] = x;
    const Word greater = bit_four | (bit_three & (bit_one | bit_two));
    const Word equal = bit_zero & ~bit_one & ~bit_two & bit_three & ~bit_four;
    const Word definite = (~equal) & ones(unsigned(hi)) & ~ones(unsigned(lo));
    if (definite == 0U) {
        hi = lo;
        return {};
    }
    const int first = std::countr_zero(definite);
    const int last = 63 - std::countl_zero(definite);
    lo = outer ? 0 : first + 1;
    hi = std::min(hi, last + int(birth));
    Word lower_carry = ((equal | greater) + greater) ^ equal;
    const Word reversed_equal = reverse_bits(equal);
    const Word reversed_greater = reverse_bits(greater);
    Word upper_carry =
        reverse_bits(((reversed_equal | reversed_greater) + reversed_greater) ^
                     reversed_equal);
    const std::array<Word, 4> base{
        bit_zero,
        bit_one ^ greater,
        bit_two ^ ((~bit_one) & greater),
        bit_three ^ greater ^ ((~bit_two) & (~bit_one) & greater),
    };
    const Word lower_keep = ~(equal & lower_carry);
    const Word upper_keep = ~(equal & upper_carry);
    Planes result{};
    Word carry = 0;
    for (unsigned bit = 0; bit < 4; ++bit) {
        const Word lower = (base[bit] ^ lower_carry) & lower_keep;
        Word upper = (base[bit] ^ upper_carry) & upper_keep;
        lower_carry &= base[bit];
        upper_carry &= base[bit];
        if (birth) {
            upper = (upper << 1U) | Word(outer && bit == 0U);
        }
        const Word partial = lower ^ upper;
        result[bit] = partial ^ carry;
        carry = (lower & upper) | (partial & carry);
    }
    result[4] = carry;
    return result;
}

// The receiving source remains untouched until every tile has valid halos.
inline bool four(const Field &input, Field &output, Work &work,
                 int issued_clock = -1) {
    ++work.attempts;
    if (input.width < 64U) {
        ++work.refused;
        return false;
    }
    int clock = issued_clock;
    if (clock < 0) {
        std::array<std::uint32_t, 8> prefix{};
        const auto n = std::min<std::size_t>(prefix.size(), input.width / 2U);
        for (std::size_t i = 0; i < n; ++i) {
            prefix[i] = input.get(i);
        }
        clock = guarded_clock::four(std::span(prefix).first(n));
    }
    if (clock < 0) {
        ++work.refused;
        return false;
    }
    const std::size_t width =
        input.width + std::size_t(std::popcount(unsigned(clock)));
    const auto half = (width + 1U) / 2U;
    output = Field(width);
    for (std::size_t offset = 0; offset < half; offset += 32U) {
        const auto start = offset >= 16U ? offset - 16U : 0U;
        const int local = int(offset - start);
        const auto count = unsigned(std::min<std::size_t>(32U, half - offset));
        Planes value = input.source(start);
        int lo = 0;
        int hi = int(std::min<std::size_t>(64U, input.width - start));
        for (unsigned tick = 0; tick < 4; ++tick) {
            value = advance(value, ((unsigned(clock) >> tick) & 1U) != 0U,
                            start == 0U, lo, hi);
            if (lo >= hi) {
                break;
            }
        }
        ++work.tiles;
        if (lo > local || hi < local + int(count)) {
            ++work.refused;
            return false;
        }
        for (unsigned bit = 0; bit < 5; ++bit) {
            output.words[offset / 64U][bit] |=
                ((value[bit] >> unsigned(local)) & ones(count))
                << (offset % 64U);
        }
    }
    ++work.actions;
    return true;
}

} // namespace causal_add::q19_tile
#endif
