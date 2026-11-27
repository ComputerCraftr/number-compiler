#ifndef NUMBER_COMPILER_NATIVE_CAUSAL_ADD_HPP
#define NUMBER_COMPILER_NATIVE_CAUSAL_ADD_HPP
#include <cstdint>
#include <string>
#include <vector>
namespace causal_add {
struct Work {
    std::uint64_t states = 0, transition_cells = 0, endpoint_cells = 0,
                  block_cells = 0, bands = 0, joins = 0, pulls = 0, births = 0;
    std::uint64_t peak_table_bytes = 0, hinge_cells = 0;
    std::uint64_t joint_bands = 0, joint_columns = 0, joint_probes = 0;
    std::uint64_t joint_collar_cells = 0, joint_clock_13 = 0, joint_clock_7 = 0,
                  joint_clock_two_births = 0, joint_clock_one_birth = 0;
    std::uint64_t join_bank_probes = 0, join_bank_builds = 0,
                  join_bank_row_compares = 0, join_bank_slots = 0;
    std::uint64_t tile_attempts = 0, tile_actions = 0, tile_cores = 0,
                  tile_refusals = 0, tile_converted_pairs = 0,
                  tile_peak_bytes = 0;
};
struct Result {
    std::string digits; // MSD-first; empty if the input is already the endpoint
    std::vector<std::uint8_t> pairs; // complete symmetric field, LSD-first
    Work work;
};
// Source pair coefficients are exact, not residues or a carry trace.
Result advance(const std::vector<std::uint8_t> &source, std::uint64_t steps,
               int height, int block_width, std::uint64_t byte_cap,
               bool emit_digits = true);
struct FoldedResult {
    std::vector<std::uint8_t> pairs;
    int center = -1;
    Work work;
};
// Source and endpoint hold the outer half in LSD-first order. The optional
// center is an ordinary decimal digit, or -1 for an even-width source.
FoldedResult advance_folded(const std::vector<std::uint8_t> &half, int center,
                            std::uint64_t steps, std::uint64_t byte_cap,
                            bool joint_enabled = false);
struct GuardResult {
    std::uint32_t
        mask; // bit 0 failure, bit q+1 successful first-interior endpoint
    std::uint64_t nodes, appends;
};
// Input excludes the outermost sum 17. Query every deeper return word.
// When endpoint=false, bit 1 denotes success independent of endpoint.
GuardResult guard98(const std::vector<std::uint8_t> &interior, int returns,
                    bool endpoint, std::uint64_t node_cap);
} // namespace causal_add

#endif // NUMBER_COMPILER_NATIVE_CAUSAL_ADD_HPP
