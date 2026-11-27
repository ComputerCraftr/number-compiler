#ifndef NUMBER_COMPILER_NATIVE_PAIR_HALF_KICK_HPP
#define NUMBER_COMPILER_NATIVE_PAIR_HALF_KICK_HPP

#include <array>
#include <cstddef>

namespace causal_add::phase {

// All 19 pair sums are distinct. In particular EQ 9 passes the inlet carry.
constexpr int carry(int sum, int inlet) {
    return static_cast<int>((sum > 9) || ((sum == 9) && (inlet != 0)));
}

constexpr int phase_digit(int sum, int inlet) {
    // The low residue and high-half parity reconstruct the physical digit.
    const int residue = sum % 5;
    const int parity = (sum / 5) % 2;
    const int low_wrap = static_cast<int>((inlet != 0) && (residue == 4));
    return ((residue + inlet) % 5) + (5 * ((parity + low_wrap) % 2));
}

constexpr auto digit_responses = [] {
    std::array<std::array<int, 2>, 19> responses{};
    for (std::size_t sum = 0; sum < responses.size(); ++sum) {
        for (std::size_t inlet = 0; inlet < responses[sum].size(); ++inlet) {
            responses[sum][inlet] =
                phase_digit(static_cast<int>(sum), static_cast<int>(inlet));
        }
    }
    return responses;
}();

constexpr int digit(int sum, int inlet) {
    return digit_responses[static_cast<std::size_t>(sum)]
                          [static_cast<std::size_t>(inlet)];
}

constexpr bool verify() {
    for (int sum = 0; sum < 19; ++sum) {
        for (int inlet = 0; inlet < 2; ++inlet) {
            if (digit(sum, inlet) != (sum + inlet) % 10 ||
                carry(sum, inlet) != (sum + inlet) / 10) {
                return false;
            }
        }
    }
    return true;
}
static_assert(verify());

} // namespace causal_add::phase

#endif // NUMBER_COMPILER_NATIVE_PAIR_HALF_KICK_HPP
