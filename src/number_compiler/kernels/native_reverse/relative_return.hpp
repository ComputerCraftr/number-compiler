#ifndef NUMBER_COMPILER_RELATIVE_RETURN_HPP
#define NUMBER_COMPILER_RELATIVE_RETURN_HPP

#include <cstddef>
#include <cstdint>
#include <string_view>

namespace rev10 {
struct RelativeRun {
    std::int64_t lo = 0;
    std::int64_t hi = 0;
    int shift = 0;
    bool uniform = false;
};

inline int relative_cell(int multiplier, int base, int left, int digit,
                         int right) {
    const int x = (multiplier * (digit % base)) + (left / base);
    const int y = (multiplier * (right % base)) + (digit / base);
    return (multiplier * (x % base)) + (y / base);
}

inline unsigned relative_matches(std::string_view source, std::int64_t i,
                                 int multiplier, int base) {
    const int left = source[static_cast<std::size_t>(i - 2)] - '0';
    const int digit = source[static_cast<std::size_t>(i - 1)] - '0';
    const int right = source[static_cast<std::size_t>(i)] - '0';
    const int result = relative_cell(multiplier, base, left, digit, right);
    return (result == right ? 1U : 0U) | (result == digit ? 2U : 0U) |
           (result == left ? 4U : 0U) |
           (left == digit && digit == right ? 8U : 0U);
}

// Check the exact two-tick nearest-neighbour action at every covered source
// triple. Bits 0..2 identify translations. Bit 3 certifies the six-gate
// uniform return. The digit triple supplies the physical carry inlet.
inline RelativeRun relative_run(std::string_view source, int multiplier,
                                std::int64_t steps) {
    const auto size = static_cast<std::int64_t>(source.size());
    if (steps < 64 || size < (8 * steps) + 64) {
        return {};
    }
    const auto threshold = (8 * steps) + 64;
    const int base = 10 / multiplier;
    // Every threshold-length interval contains a complete aligned half-span.
    // If each full half-span fails a few exact triples, no eligible interval
    // exists, so ordinary nonrepeating sources avoid a complete scan.
    const auto block = threshold / 2;
    bool possible = false;
    for (std::int64_t begin = 0; begin + block <= size && !possible;
         begin += block) {
        unsigned shifts = 15U;
        for (int probe = 0; probe < 8 && (shifts != 0); ++probe) {
            const auto i = begin + 2 + ((block - 3) * probe / 7);
            shifts &= relative_matches(source, i, multiplier, base);
        }
        possible = shifts != 0;
    }
    if (!possible) {
        return {};
    }
    RelativeRun best;
    std::int64_t start[4] = {};
    for (std::int64_t i = 2; i < size; ++i) {
        const unsigned matches = relative_matches(source, i, multiplier, base);
        for (unsigned shift = 0; shift < 4; ++shift) {
            if ((matches & (1U << shift)) == 0) {
                start[shift] = i - 1;
            } else if (i + 1 - start[shift] > best.hi - best.lo) {
                best = {
                    start[shift],
                    i + 1,
                    shift == 3U ? 0 : static_cast<int>(shift),
                    shift == 3U,
                };
            }
        }
    }
    return best.hi - best.lo < (8 * steps) + 64 ? RelativeRun{} : best;
}
} // namespace rev10
#endif
