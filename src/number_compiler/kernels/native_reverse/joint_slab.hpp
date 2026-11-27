#ifndef NUMBER_COMPILER_NATIVE_JOINT_SLAB_HPP
#define NUMBER_COMPILER_NATIVE_JOINT_SLAB_HPP

#include "pair_half_kick.hpp"
#include <array>
#include <cstddef>
#include <cstdint>
#include <vector>

namespace causal_add::joint {
struct Work {
    std::uint64_t probes = 0;
    std::uint64_t columns = 0;
    std::uint64_t collar_cells = 0;
    std::uint64_t bands = 0;
    std::uint64_t clock_13 = 0;
    std::uint64_t clock_7 = 0;
};

constexpr bool admitted(std::uint32_t sum) {
    return sum == 8U || sum == 17U || sum == 18U;
}

// One authenticated physical four-tick action over a folded pair field.
// The fast formula applies only to a protected non-EQ core. Both physical
// collars and the two carry inlets are checked before the endpoint is issued.
inline bool apply(std::vector<std::uint32_t> &state, int &center, Work &work) {
    constexpr std::size_t collar = 128, margin = 8, minimum = 48;
    const auto count = state.size();
    if (count < minimum + (2 * margin) || state[0] != 18U) {
        return false;
    }
    std::size_t left = 1, right = 1;
    while (left < collar && left < count) {
        ++work.probes;
        if (!admitted(state[left])) {
            ++left;
            continue;
        }
        right = left + 1;
        while (right < count && admitted(state[right])) {
            ++right;
            ++work.probes;
        }
        if (right - left >= minimum + (2 * margin)) {
            break;
        }
        left = right;
    }
    if (left >= collar || right - left < minimum + (2 * margin) ||
        count - right > collar) {
        return false;
    }
    const std::size_t cut = left + margin, inner = right - margin;
    std::vector<int> outer(cut), low(cut), high(cut);
    for (std::size_t i = 0; i < cut; ++i) {
        outer[i] = static_cast<int>(state[i]);
    }
    unsigned clock = 0, births = 0;
    for (unsigned tick = 0; tick < 4; ++tick) {
        int forward = 0;
        int backward = tick != 0U ? 1 : static_cast<int>(state[cut] > 9U);
        for (std::size_t i = 0; i < cut; ++i) {
            low[i] = phase::digit(outer[i], forward);
            forward = phase::carry(outer[i], forward);
        }
        for (std::size_t i = cut; i-- > 0;) {
            high[i] = phase::digit(outer[i], backward);
            backward = phase::carry(outer[i], backward);
        }
        clock |= static_cast<unsigned>(backward) << tick;
        births += static_cast<unsigned>(backward);
        for (std::size_t i = 0; i < cut; ++i) {
            int upper = high[i];
            if (backward != 0) {
                upper = i != 0 ? high[i - 1] : 1;
            }
            outer[i] = low[i] + upper;
        }
        work.collar_cells += cut;
    }
    // 13 encodes 1011 in chronological order, 7 encodes 1110.
    if (births != 3U || (clock != 13U && clock != 7U)) {
        return false;
    }
    // Start four pairs inside the protected core. Each physical tick
    // consumes one pair of that collar, leaving exactly the requested
    // center interval after four ticks without importing a remote digit.
    const auto kept = count - (inner - 4);
    std::vector<int> middle((2 * kept) + static_cast<unsigned>(center >= 0));
    std::vector<int> middle_digits;
    for (std::size_t i = 0; i < kept; ++i) {
        middle[i] = middle[middle.size() - 1 - i] =
            static_cast<int>(state[inner - 4 + i]);
    }
    if (center >= 0) {
        middle[kept] = 2 * center;
    }
    for (unsigned tick = 0; tick < 4; ++tick) {
        const bool birth = ((clock >> tick) & 1U) != 0U;
        const int boundary = middle.front();
        if ((tick == 0U && boundary == 9) || (tick != 0U && boundary <= 9)) {
            return false;
        }
        int carry = static_cast<int>(boundary > 9);
        middle_digits.resize(middle.size() - 1);
        for (std::size_t i = 1; i < middle.size(); ++i) {
            middle_digits[i - 1] = phase::digit(middle[i], carry);
            carry = phase::carry(middle[i], carry);
        }
        if (carry != static_cast<int>(boundary > 9)) {
            return false;
        }
        work.collar_cells += middle_digits.size();
        if (!birth) {
            middle_digits.pop_back();
        }
        middle.resize(middle_digits.size());
        for (std::size_t i = 0; i < middle.size(); ++i) {
            middle[i] = middle_digits[i] + middle_digits[middle.size() - 1 - i];
        }
    }
    std::vector<std::uint32_t> next(inner + (middle.size() / 2));
    for (std::size_t i = 0; i < cut; ++i) {
        next[i] = static_cast<std::uint32_t>(outer[i]);
    }
    unsigned mask = 0;
    for (std::size_t i = cut - 3; i < cut; ++i) {
        mask = (mask << 1U) | static_cast<unsigned>(state[i] != 18U);
    }
    for (std::size_t i = cut; i < inner; ++i) {
        mask = ((mask << 1U) | static_cast<unsigned>(state[i] != 18U)) & 15U;
        const unsigned weighted = (mask & 1U) + (3U * ((mask >> 1U) & 1U)) +
                                  (3U * ((mask >> 2U) & 1U)) +
                                  ((mask >> 3U) & 1U);
        next[i] = 18U - (2U * weighted);
    }
    for (std::size_t i = 0; i < middle.size() / 2; ++i) {
        next[inner + i] = static_cast<std::uint32_t>(middle[i]);
    }
    const int next_center =
        (middle.size() % 2U) != 0U ? middle_digits[middle.size() / 2] : -1;
    if ((2 * next.size()) + static_cast<unsigned>(next_center >= 0) !=
            (2 * count) + static_cast<unsigned>(center >= 0) + 3U ||
        next.empty() || next.front() == 0U) {
        return false;
    }
    work.columns += inner - cut;
    ++work.bands;
    if (clock == 13U) {
        ++work.clock_13;
    } else {
        ++work.clock_7;
    }
    state.swap(next);
    center = next_center;
    return true;
}
} // namespace causal_add::joint
#endif
