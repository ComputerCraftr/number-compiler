#ifndef NUMBER_COMPILER_NATIVE_REVERSE_REV10_HPP
#define NUMBER_COMPILER_NATIVE_REVERSE_REV10_HPP
#include <cstdint>
#include <string>
#include <string_view>
namespace rev10 {
struct Stats {
    std::uint64_t tiles = 0, fringe_cells = 0, fringe_gates = 0, rows = 0,
                  word_updates = 0, table_entries = 0, table_bytes = 0,
                  table_aux_bytes = 0;
    double setup_ms = 0, eval_ms = 0;
};
struct Result {
    std::string digits;
    std::string engine;
    Stats stats;
    double total_ms = 0;
};
// Computes F_m^n(seed), F_m(x)=m*decimal_reverse(x), m=2 or 5.
// An explicit diagonal engine never falls back to chronological rows.
Result nth(std::string seed, int multiplier, std::int64_t steps,
           std::string_view requested = "diagonal", int side = 4);
} // namespace rev10

#endif
