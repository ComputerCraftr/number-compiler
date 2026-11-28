#ifndef NUMBER_COMPILER_BITPLANE_WORD_HPP
#define NUMBER_COMPILER_BITPLANE_WORD_HPP
#include <cstdint>
namespace bitplane_word {
using Word = std::uint64_t;
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

} // namespace bitplane_word
#endif
