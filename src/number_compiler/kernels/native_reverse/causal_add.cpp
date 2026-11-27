#include "causal_add.hpp"
#include "joint_slab.hpp"
#include "pair_half_kick.hpp"
#include <algorithm>
#include <array>
#include <bit>
#include <cstddef>
#include <cstdint>
#include <limits>
#include <stdexcept>
#include <unordered_map>
#include <utility>
#include <vector>

namespace causal_add {
namespace {
using U = std::uint64_t;
using I = std::uint32_t;
using Byte = std::uint8_t;
using Word = std::vector<Byte>;
constexpr int MAX_HEIGHT = 7;
constexpr int MAX_BLOCK = 4;
void require(bool v, const char *message) {
    if (!v) {
        throw std::runtime_error(message);
    }
}
using phase::carry;
U checked_product(U a, U b) {
    require((a == 0U) || b <= std::numeric_limits<U>::max() / a,
            "table size overflow");
    return a * b;
}
struct Budget {
    U cap, held = 0, peak = 0;
    void take(U n) {
        require(n <= cap - held, "causal quotient table budget exceeded");
        held += n;
        peak = std::max(peak, held);
    }
    void release(U n) {
        require(n <= held, "table budget underflow");
        held -= n;
    }
};
using Row = std::array<I, 19>;
struct Level {
    std::vector<U> nodes;
    std::vector<Row> append;
    unsigned shift = 5;
    U mask = 31;
    U edge(I id, int b) const {
        return (nodes[id] >> (shift * unsigned(b))) & mask;
    }
};
// Canonical residual response: output/child for both current return bits.
// Build the universal automaton before the source strip is traversed.
std::vector<Level> compile_levels(int h, Budget &budget, Work &work) {
    std::vector<Level> levels(1);
    levels[0].nodes = {0};
    levels[0].append = {Row{}};
    for (int d = 1; d <= h; ++d) {
        const auto &prev = levels.back();
        Level current;
        current.shift = unsigned(5 + std::bit_width(U(prev.nodes.size() - 1)));
        require(current.shift <= 32, "causal response key overflow");
        current.mask = (U(1) << current.shift) - 1;
        std::unordered_map<U, I> interner;
        // 160 bytes per provisional node covers the row/key vectors,
        // amortized vector capacity, interner node and hash buckets.
        constexpr U node_charge = 320;
        auto intern = [&](U key) {
            auto it = interner.find(key);
            if (it != interner.end()) {
                return it->second;
            }
            budget.take(node_charge);
            require(current.nodes.size() < std::numeric_limits<I>::max(),
                    "too many causal states");
            I id = I(current.nodes.size());
            current.nodes.push_back(key);
            interner.emplace(key, id);
            ++work.states;
            return id;
        };
        // Empty exterior prefix: forward inlet zero, birth=return bit,
        // shifted digit is 1 on birth. No physical row is constructed.
        intern(U(4) << current.shift);
        for (I p = 0; p < current.nodes.size(); ++p) {
            U key = current.nodes[p];
            Row row{};
            for (int s = 0; s < 19; ++s) {
                U result = 0;
                for (int b = 0; b < 2; ++b) {
                    U old = (key >> (current.shift * unsigned(carry(s, b)))) &
                            current.mask;
                    int output = int(old & 31U), a = output % 2,
                        high = output / 2;
                    int y = phase::digit(s, b), low = phase::digit(s, a);
                    int successor = low + ((high != 0) ? high - 1 : y);
                    I child = prev.append[old >> 5U][std::size_t(successor)];
                    int symbol = carry(s, a) + (2 * ((high != 0) ? 1 + y : 0));
                    result |= ((U(child) * 32) + U(symbol))
                              << (current.shift * unsigned(b));
                }
                row[std::size_t(s)] = intern(result);
                ++work.transition_cells;
            }
            current.append.push_back(row);
        }
        // Keep charging the conservative bound for the whole request; only
        // the response keys and transition rows remain live after interning.
        levels.push_back(std::move(current));
    }
    return levels;
}
struct Cell {
    int sum, low, left, growth;
};
I pack_cell(Cell c) {
    return I(c.sum) | (I(c.low) << 5U) | (I(c.left) << 9U) |
           (I(c.growth) << 17U);
}
Cell unpack_cell(I v) {
    return {
        int(v & 31U),
        int((v >> 5U) & 15U),
        int((v >> 9U) & 255U),
        int(v >> 17U),
    };
}
using Cells = std::vector<I>;
// Bottom-up temporal composition of one-column pullback responses.
// Each table cell is computed once from a smaller canonical action, not
// from an actual source occurrence or a loop through its temporal rows.
std::vector<Cells> compile_cells(const std::vector<Level> &levels,
                                 Budget &budget, Work &work) {
    std::vector<Cells> all(1);
    for (int h = 1; h < int(levels.size()); ++h) {
        U ports = U(1) << unsigned(h);
        U size = checked_product(
            checked_product(levels[std::size_t(h)].nodes.size(), 19), ports);
        budget.take(checked_product(size, sizeof(I)));
        Cells cells(size);
        for (I p = 0; p < levels[std::size_t(h)].nodes.size(); ++p) {
            for (int s = 0; s < 19; ++s) {
                for (U r = 0; r < ports; ++r) {
                    int b = int(r & 1U), left = carry(s, b);
                    U edge = levels[std::size_t(h)].edge(p, left);
                    int a = int(edge & 1U), high = int((edge & 31U) >> 1U);
                    int low = phase::digit(s, a),
                        next =
                            low + ((high != 0) ? high - 1 : phase::digit(s, b));
                    Cell c = {next, low, left, int(high != 0)};
                    if (h > 1) {
                        U addr =
                            ((((edge >> 5U) * 19) + U(next)) * (ports >> 1U)) +
                            (r >> 1U);
                        c = unpack_cell(all[std::size_t(h - 1)][addr]);
                        c.left = int((unsigned(c.left) << 1U) | unsigned(left));
                        c.growth += int(high != 0);
                    }
                    cells[(((U(p) * 19) + U(s)) * ports) + r] = pack_cell(c);
                    ++work.endpoint_cells;
                }
            }
        }
        all.push_back(std::move(cells));
    }
    return all;
}
// The hinge summarizes the exact center and birth response of an ordered
// band. It retains both incoming carry ports and the number of width births.
struct Hinge {
    U digits = 0;
    unsigned ports = 0, births = 0;
};
using Hinges = std::vector<Hinge>;
U decimal_power(unsigned n) {
    U result = 1;
    while (n-- != 0U) {
        result *= 10;
    }
    return result;
}
std::vector<Hinges> compile_hinges(const std::vector<Level> &levels,
                                   const std::vector<Cells> &cells,
                                   Budget &budget, Work &work) {
    budget.take(11 * sizeof(Hinge));
    std::vector<Hinges> all;
    all.emplace_back(11);
    for (int d = 0; d < 10; ++d) {
        all[0][std::size_t(d) + 1].digits = U(d);
    }
    for (std::size_t h = 1; h < levels.size(); ++h) {
        const auto &lv = levels[h];
        const auto &prev = levels[h - 1];
        budget.take(checked_product(lv.nodes.size(), 11 * sizeof(Hinge)));
        Hinges table(lv.nodes.size() * 11);
        for (I q = 0; q < lv.nodes.size(); ++q) {
            const int a = int(lv.edge(q, 0) & 1U);
            require(a == int(lv.edge(q, 1) & 1U), "acausal hinge response");
            for (int d = -1; d < 10; ++d) {
                const int b = d < 0 ? a : int(d >= 5);
                const U edge = lv.edge(q, b);
                const I child = I(edge >> 5U);
                const int high = int((edge & 31U) >> 1U);
                const bool born = high != 0;
                const int center = d < 0 ? -1 : ((2 * d) + a) % 10;
                Hinge out;
                if (born && d >= 0) {
                    const int v = high - 1, sum = center + v;
                    if (h == 1) {
                        out.digits = U(center) + (10 * U(v));
                    } else {
                        const auto &next =
                            all[h - 1]
                               [U(prev.append[child][std::size_t(sum)]) * 11];
                        const Cell c = unpack_cell(
                            cells[h - 1][(((U(child) * 19) + U(sum)) *
                                          (U(1) << (h - 1))) +
                                         next.ports]);
                        require(c.growth == int(next.births),
                                "hinge pullback width mismatch");
                        require(c.sum >= c.low && c.sum - c.low <= 9,
                                "invalid hinge digit");
                        out = {
                            U(c.low) + (10 * next.digits) +
                                (decimal_power(1 + next.births) *
                                 U(c.sum - c.low)),
                            unsigned(c.left),
                            next.births,
                        };
                    }
                } else {
                    const int next_center = born ? high - 1 : center;
                    out = all[h - 1][(U(child) * 11) + U(next_center + 1)];
                }
                out.ports = (out.ports << 1U) | unsigned(b);
                out.births += unsigned(born);
                table[(U(q) * 11) + U(d + 1)] = out;
                ++work.hinge_cells;
            }
        }
        all.push_back(std::move(table));
    }
    return all;
}

struct BlockTable {
    int h, b;
    U radix = 1, decimal = 1, ports;
    std::vector<I> join;
    unsigned sum_bits, growth_bits, low_shift;
    U sum_mask, growth_mask;
    bool compact;
    std::vector<I> emit32;
    std::vector<U> emit64;
    BlockTable(const Level &lv, const Cells &cells, int height, int block,
               Budget &budget, Work &work)
        : h(height), b(block), ports(U(1) << unsigned(h)) {
        for (int i = 0; i < b; ++i) {
            radix *= 19;
            decimal *= 10;
        }
        U pairs = checked_product(lv.nodes.size(), radix);
        U count = checked_product(pairs, ports);
        sum_bits = unsigned(std::bit_width(radix - 1));
        growth_bits = unsigned(std::bit_width(U(h)));
        sum_mask = (U(1) << sum_bits) - 1;
        growth_mask = (U(1) << growth_bits) - 1;
        low_shift = unsigned(h) + growth_bits + sum_bits;
        compact = low_shift + unsigned(std::bit_width(decimal - 1)) <= 32;
        budget.take(checked_product(pairs, sizeof(I)) +
                    checked_product(count, compact ? sizeof(I) : sizeof(U)));
        join.resize(pairs);
        if (compact) {
            emit32.resize(count);
        } else {
            emit64.resize(count);
        }
        std::array<int, MAX_BLOCK> s{};
        std::array<I, MAX_BLOCK> pre{};
        for (I p = 0; p < lv.nodes.size(); ++p) {
            for (U code = 0; code < radix; ++code) {
                U address = (U(p) * radix) + code, z = code;
                I q = p;
                for (int i = 0; i < b; ++i) {
                    s[std::size_t(i)] = int(z % 19U);
                    z /= 19;
                    pre[std::size_t(i)] = q;
                    q = lv.append[q][std::size_t(s[std::size_t(i)])];
                }
                join[address] = q;
                for (U right = 0; right < ports; ++right) {
                    U r = right, sum = 0, low = 0, births = 0;
                    for (int i = b - 1; i >= 0; --i) {
                        Cell c =
                            unpack_cell(cells[(((U(pre[std::size_t(i)]) * 19) +
                                                U(s[std::size_t(i)])) *
                                               ports) +
                                              r]);
                        r = U(c.left);
                        sum = (sum * 19) + U(c.sum);
                        low = (low * 10) + U(c.low);
                        if (i == b - 1) {
                            births = U(c.growth);
                        } else {
                            require(births == U(c.growth),
                                    "inconsistent compiled birth count");
                        }
                    }
                    // Fixed-word endpoint and separator, not a history of rows.
                    U value = r | (births << unsigned(h)) |
                              (sum << (unsigned(h) + growth_bits)) |
                              (low << low_shift);
                    if (compact) {
                        emit32[(address * ports) + right] = I(value);
                    } else {
                        emit64[(address * ports) + right] = value;
                    }
                    ++work.block_cells;
                }
            }
        }
    }
    int run(std::vector<I> &state, std::vector<I> &low,
            std::vector<U> &addresses, Work &work, bool emit_digits) const {
        addresses.resize(state.size());
        I q = 0;
        for (std::size_t i = 0; i < state.size(); ++i) {
            U index = (U(q) * radix) + state[i];
            addresses[i] = index;
            q = join[index];
        }
        U r = 0;
        int birth = -1;
        if (emit_digits) {
            low.resize(state.size());
        }
        for (std::size_t i = state.size(); i-- > 0;) {
            U address = (addresses[i] * ports) + r;
            U value = compact ? emit32[address] : emit64[address];
            r = value & (ports - 1);
            int growth = int((value >> unsigned(h)) & growth_mask);
            if (birth == -1) {
                birth = growth;
            } else {
                require(birth == growth, "inconsistent physical birth count");
            }
            state[i] = I((value >> (unsigned(h) + growth_bits)) & sum_mask);
            if (emit_digits) {
                low[i] = I(value >> low_shift);
            }
        }
        require(std::popcount(r) == birth, "outer birth port mismatch");
        work.joins += state.size();
        work.pulls += state.size();
        ++work.bands;
        work.births += U(birth);
        return birth;
    }
};

// Fully compared ordered response rows are safe to share, while every
// receiving q remains authenticated on the physical pull.
// A two-column response retains both the exact intermediate state and the
// successor. Only identical complete ordered rows share an action.
struct PairJoinBank {
    static constexpr U min_columns = U(1) << 18U;
    static constexpr U sum_pairs = U(19) * 19U;
    static constexpr U max_rows = U(1) << 7U;
    static constexpr U max_states = U(1) << 9U;
    std::vector<I> joins, row_ids;
    bool attempted = false;

    void admit(const Level &level, Budget &budget, Work &work) {
        attempted = true;
        const auto &rows = level.append;
        const U row_cost = U(rows.size()) * sizeof(I) * 2U;
        const U worst = row_cost + (max_rows * sum_pairs * sizeof(I));
        if (rows.size() > max_states || worst > budget.cap - budget.held) {
            return;
        }
        budget.take(row_cost);
        {
            std::vector<I> representatives;
            representatives.reserve(rows.size());
            row_ids.reserve(rows.size());
            for (I q = 0; q < rows.size(); ++q) {
                I ordinal = 0;
                for (; ordinal < representatives.size(); ++ordinal) {
                    ++work.join_bank_row_compares;
                    if (rows[q] == rows[representatives[ordinal]]) {
                        break;
                    }
                }
                if (ordinal == representatives.size()) {
                    representatives.push_back(q);
                }
                row_ids.push_back(ordinal);
            }
            if (representatives.size() <= max_rows) {
                const U slots = U(representatives.size()) * sum_pairs;
                budget.take(slots * sizeof(I));
                joins.resize(slots);
                work.join_bank_slots = joins.size();
            }
        }
        if (joins.empty()) {
            std::vector<I>().swap(row_ids);
            budget.release(row_cost);
        }
        work.peak_table_bytes = budget.peak;
    }
};

struct PairJoinResponse {
    I middle, end, row;
};

constexpr I pack_pair_join(PairJoinResponse value) {
    return 1U + (value.middle | (value.end << 9U) | (value.row << 18U));
}

constexpr PairJoinResponse unpack_pair_join(I value) {
    --value;
    return {value & 511U, (value >> 9U) & 511U, value >> 18U};
}

// Folded width-one bands do not allocate the reflected second half.
Hinge run_folded(const Level &level, const Cells &cells, unsigned height,
                 std::vector<I> &state, int center, const Hinges &hinges,
                 std::vector<U> &addresses, Work &work, std::vector<I> &joins,
                 const std::vector<I> &row_ids) {
    addresses.resize(state.size());
    I q = 0;
    std::size_t i = 0;
    I row = joins.empty() ? 0U : row_ids[0];
    while (!joins.empty() && i + 1U < state.size()) {
        const I first = state[i], second = state[i + 1U];
        const U key =
            (U(row) * PairJoinBank::sum_pairs) + (U(first) * 19U) + second;
        ++work.join_bank_probes;
        I value = joins[key];
        if (value == 0U) {
            ++work.join_bank_builds;
            const I middle = level.append[q][first];
            const I end = level.append[middle][second];
            value = pack_pair_join({middle, end, row_ids[end]});
            joins[key] = value;
        }
        const PairJoinResponse response = unpack_pair_join(value);
        addresses[i] = (U(q) * 19U) + first;
        addresses[i + 1U] = (U(response.middle) * 19U) + second;
        q = response.end;
        row = response.row;
        i += 2;
    }
    for (; i < state.size(); ++i) {
        addresses[i] = (U(q) * 19U) + state[i];
        q = level.append[q][state[i]];
    }
    work.joins += state.size();
    const Hinge result = hinges[(U(q) * 11) + U(center + 1)];
    U r = result.ports;
    const U ports = U(1) << height;
    for (std::size_t column = state.size(); column-- > 0;) {
        const Cell response =
            unpack_cell(cells[(addresses[column] * ports) + r]);
        r = U(response.left);
        require(unsigned(response.growth) == result.births,
                "inconsistent folded birth count");
        state[column] = I(response.sum);
    }
    require(unsigned(std::popcount(r)) == result.births,
            "outer birth port mismatch");
    work.pulls += state.size();
    ++work.bands;
    work.births += result.births;
    return result;
}
// Guard-only canonical residuals. Terminal bitsets are distinct from
// nonterminal IDs; a child with a constant answer has no observable ports.
constexpr I TERMINAL = I(1) << 31U;
I leaf(I result) { return TERMINAL | result; }
bool terminal(I id) { return bool(id & TERMINAL); }
struct Edge {
    I child;
    Byte a, v;
};
struct GuardKey {
    int h;
    Edge e[2];
    bool operator==(const GuardKey &b) const {
        return h == b.h && e[0].child == b.e[0].child && e[0].a == b.e[0].a &&
               e[0].v == b.e[0].v && e[1].child == b.e[1].child &&
               e[1].a == b.e[1].a && e[1].v == b.e[1].v;
    }
};
struct GuardHash {
    std::size_t operator()(const GuardKey &k) const {
        U v = U(k.h);
        for (const auto &e : k.e) {
            v = (v * 0x9e3779b97f4a7c15ULL) ^
                ((U(e.child) << 8U) | (U(e.a) << 4U) | e.v);
        }
        return std::size_t(v ^ (v >> 32U));
    }
};
class Guard {
    struct AppendFrame {
        U key;
        I id;
        int symbol;
        int next_edge = 0;
        GuardKey output;
    };
    struct AtomEdge {
        int target;
        Byte carry;
        Byte digit;
    };

    bool endpoint;
    U cap;
    std::vector<GuardKey> nodes;
    std::vector<I> masks;
    std::unordered_map<GuardKey, I, GuardHash> interned;
    std::unordered_map<U, I> memo;
    std::vector<std::array<I, 19>> atom;
    std::vector<AppendFrame> pending;

    static AtomEdge atom_edge(int sum, int branch, bool birth) {
        const int forward = carry(sum, branch);
        if (!birth && forward == 0) {
            return {-1, 0, 0};
        }
        const int digit = phase::digit(sum, branch);
        const int inlet = static_cast<int>(birth);
        const int target =
            phase::digit(sum, inlet) + (birth ? 7 + forward : digit);
        return {target, Byte(carry(sum, inlet)), Byte(birth ? digit : 0)};
    }

    static I symbol_bit(int sum) { return I{1} << unsigned(sum); }

    I prepare_atom(int height, Byte source) {
        // Close the selected root under its two ordered carries before
        // allocating any guard nodes. Each child has strictly lower height.
        std::vector<I> needed(atom.size());
        needed.back() = symbol_bit(source);
        for (int d = height; d > 0; --d) {
            const bool birth = d % 2 == 0;
            for (I bits = needed[std::size_t(d)]; bits != 0;
                 bits &= bits - 1U) {
                const int sum = std::countr_zero(bits);
                for (int branch = 0; branch < 2; ++branch) {
                    const int target = atom_edge(sum, branch, birth).target;
                    if (target >= 0) {
                        needed[std::size_t(d - 1)] |= symbol_bit(target);
                    }
                }
            }
        }
        for (I bits = needed.front(); bits != 0; bits &= bits - 1U) {
            const int sum = std::countr_zero(bits);
            atom[0][std::size_t(sum)] =
                leaf(symbol_bit(endpoint ? sum + 1 : 1));
        }
        for (int d = 1; d <= height; ++d) {
            const bool birth = d % 2 == 0;
            for (I bits = needed[std::size_t(d)]; bits != 0;
                 bits &= bits - 1U) {
                const int sum = std::countr_zero(bits);
                GuardKey key{d, {}};
                for (int branch = 0; branch < 2; ++branch) {
                    const AtomEdge edge = atom_edge(sum, branch, birth);
                    if (edge.target < 0) {
                        key.e[branch] = {leaf(1), 0, 0};
                    } else {
                        key.e[branch] = {
                            atom[std::size_t(d - 1)][std::size_t(edge.target)],
                            edge.carry,
                            edge.digit,
                        };
                    }
                }
                atom[std::size_t(d)][std::size_t(sum)] = intern(key);
            }
        }
        return atom.back()[source];
    }
    I mask(I id) const { return terminal(id) ? (id & ~TERMINAL) : masks[id]; }
    I intern(GuardKey k) {
        if (k.e[0].child == k.e[1].child && terminal(k.e[0].child)) {
            return k.e[0].child;
        }
        for (auto &e : k.e) {
            if (terminal(e.child)) {
                e.a = 0;
                e.v = 0;
            }
        }
        auto it = interned.find(k);
        if (it != interned.end()) {
            return it->second;
        }
        require(nodes.size() + memo.size() + pending.size() < cap,
                "conditional guard quotient budget exceeded");
        I id = I(nodes.size());
        nodes.push_back(k);
        masks.push_back(mask(k.e[0].child) | mask(k.e[1].child));
        interned.emplace(k, id);
        return id;
    }
    I append(I id, int s) {
        if (terminal(id)) {
            return id;
        }
        const U initial_key = (U(id) * 19) + U(s);
        if (auto found = memo.find(initial_key); found != memo.end()) {
            return found->second;
        }

        auto push = [&](U key, I child, int symbol) {
            require(nodes.size() + memo.size() + pending.size() < cap,
                    "conditional guard quotient budget exceeded");
            pending.push_back(
                {key, child, symbol, 0, GuardKey{nodes[child].h, {}}});
        };
        push(initial_key, id, s);
        for (;;) {
            AppendFrame &frame = pending.back();
            if (frame.next_edge == 2) {
                const U key = frame.key;
                const I result = intern(frame.output);
                pending.pop_back();
                memo.emplace(key, result);
                if (pending.empty()) {
                    return result;
                }
                AppendFrame &parent = pending.back();
                parent.output.e[parent.next_edge - 1].child = result;
                continue;
            }
            const int branch = frame.next_edge++;
            const Edge edge = nodes[frame.id].e[carry(frame.symbol, branch)];
            if (terminal(edge.child)) {
                frame.output.e[branch] = {edge.child, 0, 0};
                continue;
            }
            const bool birth = frame.output.h % 2 == 0;
            const int digit = phase::digit(frame.symbol, branch);
            const int next =
                phase::digit(frame.symbol, edge.a) + (birth ? edge.v : digit);
            frame.output.e[branch] = {
                0,
                Byte(carry(frame.symbol, edge.a)),
                Byte(birth ? digit : 0),
            };
            const U child_key = (U(edge.child) * 19) + U(next);
            const auto found = memo.find(child_key);
            if (found == memo.end()) {
                push(child_key, edge.child, next);
            } else {
                frame.output.e[branch].child = found->second;
            }
        }
    }

  public:
    Guard(int h, bool want, U limit)
        : endpoint(want), cap(limit), atom(std::size_t(h + 1)) {
        require(cap > 0 && cap < TERMINAL, "invalid guard quotient cap");
    }
    GuardResult query(const Word &source, int h) {
        I id = prepare_atom(h, source.front());
        for (std::size_t i = 1; i < source.size() && !terminal(id); ++i) {
            id = append(id, source[i]);
        }
        return {mask(id), nodes.size(), memo.size()};
    }
};
} // namespace

Result advance(const Word &source, U steps, int height, int block_width, U cap,
               bool emit_digits) {
    require(!source.empty() && source.size() <= 100000000 && steps <= 100000000,
            "invalid causal field extent");
    require(height >= 1 && height <= MAX_HEIGHT && block_width >= 1 &&
                block_width <= MAX_BLOCK,
            "invalid causal table shape");
    for (std::size_t i = 0; i < source.size(); ++i) {
        require(source[i] < 19 && source[i] == source[source.size() - 1 - i],
                "invalid symmetric pair field");
    }
    require(source.size() % 2 == 0 || source[source.size() / 2] % 2 == 0,
            "odd center coefficient");
    require(source.size() == 1 || source.front() != 0,
            "noncanonical zero exterior");
    Result result;
    result.pairs = source;
    if ((steps == 0U) || (source.size() == 1 && source[0] == 0)) {
        if (emit_digits && source.size() == 1 && source[0] == 0) {
            result.digits = "0";
        }
        return result;
    }
    height = int(std::min<U>(U(height), steps));
    Budget budget{cap};
    auto levels = compile_levels(height, budget, result.work);
    auto cells = compile_cells(levels, budget, result.work);
    // Only the complete band and possible remainder table are needed.
    BlockTable main(levels[std::size_t(height)], cells[std::size_t(height)],
                    height, block_width, budget, result.work);
    int remainder = int(steps % U(height));
    std::vector<BlockTable> tail;
    if (remainder != 0) {
        tail.emplace_back(levels[std::size_t(remainder)],
                          cells[std::size_t(remainder)], remainder, block_width,
                          budget, result.work);
    }
    result.work.peak_table_bytes = budget.peak;
    std::size_t width = source.size();
    std::vector<I> state(
        (width + std::size_t(block_width) - 1) / std::size_t(block_width), 0),
        low;
    for (std::size_t i = 0; i < state.size(); ++i) {
        I code = 0;
        for (int j = block_width - 1; j >= 0; --j) {
            std::size_t k = (i * std::size_t(block_width)) + std::size_t(j);
            code = (code * 19) + (k < width ? source[k] : 0);
        }
        state[i] = code;
    }
    std::vector<U> addresses;
    for (U done = 0; done < steps;) {
        const auto &t = steps - done >= U(height) ? main : tail.front();
        // Active width only, with causal zero padding for possible births.
        state.resize((width + std::size_t(t.h) + std::size_t(block_width) - 1) /
                         std::size_t(block_width),
                     0);
        width += std::size_t(t.run(state, low, addresses, result.work,
                                   emit_digits && done + U(t.h) == steps));
        done += U(t.h);
        state.resize((width + std::size_t(block_width) - 1) /
                     std::size_t(block_width));
    }
    result.pairs.resize(width);
    if (emit_digits) {
        result.digits.assign(width, '0');
    }
    for (std::size_t i = 0; i < state.size(); ++i) {
        I code = state[i], digit = emit_digits ? low[i] : 0;
        for (int j = 0; j < block_width; ++j) {
            std::size_t k = (i * std::size_t(block_width)) + std::size_t(j);
            if (k < width) {
                result.pairs[k] = static_cast<Byte>(code % 19);
                if (emit_digits) {
                    result.digits[width - 1 - k] = char('0' + (digit % 10));
                }
            } else {
                {
                    require(code % 19 == 0 && digit % 10 == 0,
                            "nonzero padding at endpoint");
                }
            }
            code /= 19;
            digit /= 10;
        }
    }
    require(!emit_digits || result.digits[0] != '0',
            "noncanonical endpoint width");
    require(result.pairs.front() > 0 &&
                std::equal(result.pairs.begin(), result.pairs.end(),
                           result.pairs.rbegin()),
            "invalid endpoint symmetry");
    require(width % 2 == 0 || result.pairs[width / 2] % 2 == 0,
            "invalid endpoint center");
    return result;
}
FoldedResult advance_folded(const Word &half, int center, U steps, U cap,
                            bool joint_enabled) {
    require(center >= -1 && center <= 9 && (!half.empty() || center >= 0) &&
                half.size() <= 50000000 && steps <= 65536,
            "invalid folded causal extent");
    for (Byte value : half) {
        require(value < 19, "invalid pair coefficient");
    }
    require(half.empty() || half.front() != 0, "noncanonical zero exterior");
    FoldedResult result;
    result.pairs = half;
    result.center = center;
    if (steps == 0 || (half.empty() && center == 0)) {
        return result;
    }
    std::vector<I> state(half.begin(), half.end());
    std::size_t count = half.size();
    std::size_t width = (2 * count) + unsigned(center >= 0);
    U done = 0;
    joint::Work joint_work;
    if (joint_enabled) {
        while ((steps - done) >= 4U &&
               joint::apply(state, center, joint_work)) {
            done += 4U;
            count = state.size();
            width = (2 * count) + unsigned(center >= 0);
        }
    }
    result.work.joint_bands = joint_work.bands;
    result.work.joint_columns = joint_work.columns;
    result.work.joint_probes = joint_work.probes;
    result.work.joint_collar_cells = joint_work.collar_cells;
    result.work.joint_clock_13 = joint_work.clock_13;
    result.work.joint_clock_7 = joint_work.clock_7;
    result.work.joint_clock_two_births = joint_work.clock_two_births;
    result.work.joint_clock_one_birth = joint_work.clock_one_birth;
    result.work.births = joint_work.births;
    result.work.bands = joint_work.bands;
    if (done < steps) {
        const int height = int(std::min<U>(2, steps - done));
        Budget budget{cap};
        auto levels = compile_levels(height, budget, result.work);
        auto cells = compile_cells(levels, budget, result.work);
        auto hinges = compile_hinges(levels, cells, budget, result.work);
        PairJoinBank bank;
        result.work.peak_table_bytes = budget.peak;
        std::vector<U> addresses;
        std::vector<I> empty_joins;
        for (; done < steps;) {
            const int action_height = int(std::min<U>(U(height), steps - done));
            if (!bank.attempted && action_height == 2 &&
                ((steps - done) / 2U) * state.size() >=
                    PairJoinBank::min_columns) {
                bank.admit(levels[std::size_t(height)], budget, result.work);
            }
            const auto &hinge = hinges[std::size_t(action_height)];
            const Hinge close = run_folded(
                levels[std::size_t(action_height)],
                cells[std::size_t(action_height)], unsigned(action_height),
                state, center, hinge, addresses, result.work,
                action_height == height ? bank.joins : empty_joins,
                bank.row_ids);
            const unsigned inner = unsigned(center >= 0) + close.births;
            U digits = close.digits;
            width += close.births;
            const std::size_t next_count = width / 2;
            state.resize(next_count, 0);
            U scale = (inner != 0U) ? decimal_power(inner - 1) : 1;
            for (unsigned j = 0; j < inner / 2; ++j) {
                const int a = int(digits % 10), b = int(digits / scale);
                state[count++] = I(a + b);
                digits = (digits % scale) / 10;
                scale /= 100;
            }
            center = ((inner % 2) != 0U) ? int(digits) : -1;
            require(count == next_count && center < 10,
                    "invalid moving center endpoint");
            done += U(action_height);
        }
    }
    result.pairs.assign(state.begin(), state.end());
    result.center = center;
    require(result.pairs.empty() ? center >= 0 : result.pairs.front() > 0,
            "invalid endpoint exterior");
    return result;
}
GuardResult guard98(const Word &interior, int returns, bool endpoint, U cap) {
    require(!interior.empty() && returns >= 0 && returns <= 512,
            "invalid guarded return extent");
    for (Byte s : interior) {
        require(s < 19, "invalid guard source coefficient");
    }
    Guard compiler(2 * returns, endpoint, cap);
    return compiler.query(interior, 2 * returns);
}
} // namespace causal_add
