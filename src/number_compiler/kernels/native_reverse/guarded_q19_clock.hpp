#ifndef NUMBER_COMPILER_GUARDED_Q19_CLOCK_HPP
#define NUMBER_COMPILER_GUARDED_Q19_CLOCK_HPP

#include "pair_half_kick.hpp"

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <span>

namespace causal_add::guarded_clock {

// A non-EQ pair fixes the returning carry for every column outside it.
// After a birth the high digit shifts inward and the outer seam contributes 1.
inline int four(std::span<const std::uint32_t> half) {
    std::array<int, 8> sums{}, low{}, high{};
    auto count = std::min(half.size(), sums.size());
    for (std::size_t i = 0; i < count; ++i) {
        if (half[i] > 18U) {
            return -1;
        }
        sums[i] = static_cast<int>(half[i]);
    }
    unsigned word = 0;
    for (int tick = 0; tick < 4; ++tick) {
        auto end = count;
        while (end > 0 && sums[end - 1] == 9) {
            --end;
        }
        if (end == 0) {
            return -1;
        }
        const auto reset = end - 1;
        int carry = static_cast<int>(sums[reset] > 9);
        for (auto j = reset; j > 0; --j) {
            high[j - 1] = phase::digit(sums[j - 1], carry);
            carry = phase::carry(sums[j - 1], carry);
        }
        const int birth = carry;
        word |= static_cast<unsigned>(birth) << static_cast<unsigned>(tick);
        if (tick < 3) {
            count = reset + static_cast<std::size_t>(birth);
            carry = 0;
            for (std::size_t j = 0; j < count; ++j) {
                low[j] = phase::digit(sums[j], carry);
                carry = phase::carry(sums[j], carry);
            }
            for (std::size_t j = 0; j < count; ++j) {
                sums[j] =
                    low[j] + ((birth != 0 && j == 0)
                                  ? 1
                                  : high[j - static_cast<std::size_t>(birth)]);
            }
        }
    }
    return static_cast<int>(word);
}
} // namespace causal_add::guarded_clock
#endif // NUMBER_COMPILER_GUARDED_Q19_CLOCK_HPP
