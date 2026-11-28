#ifndef NUMBER_COMPILER_DENSE_DIGITPLANES_HPP
#define NUMBER_COMPILER_DENSE_DIGITPLANES_HPP

#include "relative_return.hpp"

#include <algorithm>
#include <array>
#include <chrono>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <optional>
#include <stdexcept>
#include <string>
#include <string_view>
#include <vector>

#if defined(__aarch64__) || defined(__arm64__)
#include <arm_neon.h>
#ifdef __APPLE__
#include <sys/sysctl.h>
#elif defined(__linux__)
#include <asm/hwcap.h>
#include <sys/auxv.h>
#endif
#endif

namespace rev10::dense {

using Word = std::uint64_t;
using Planes = std::array<Word, 5>;

struct State {
    Planes r{}, c{}, s{}, t{};
};

// A carryless product with all ones gives inclusive prefix XOR. The target
// attribute isolates the instruction so a portable binary can check its
// availability before execution.
#if (defined(__aarch64__) || defined(__arm64__)) &&                            \
    (defined(__clang__) || defined(__GNUC__))
__attribute__((target("+crypto"))) inline Word pmull_prefix(Word value) {
    const auto product = vmull_p64(static_cast<poly64_t>(value),
                                   static_cast<poly64_t>(~Word{0}));
    return vgetq_lane_u64(vreinterpretq_u64_p128(product), 0);
}
inline bool has_pmull() {
    const char *portable = std::getenv("NUMBER_COMPILER_DENSE_PORTABLE");
    if (portable != nullptr && std::string_view(portable) == "1") {
        return false;
    }
#ifdef __APPLE__
    int available = 0;
    std::size_t size = sizeof(available);
    return sysctlbyname("hw.optional.arm.FEAT_PMULL", &available, &size,
                        nullptr, 0) == 0 &&
           available != 0;
#elif defined(__linux__) && defined(HWCAP_PMULL)
    return (getauxval(AT_HWCAP) & HWCAP_PMULL) != 0;
#else
    return false;
#endif
}
#else
inline bool has_pmull() { return false; }
#endif

inline Word prefix_parity(Word value, bool use_pmull) {
#if (defined(__aarch64__) || defined(__arm64__)) &&                            \
    (defined(__clang__) || defined(__GNUC__))
    if (use_pmull) {
        return pmull_prefix(value);
    }
#else
    (void)use_pmull;
#endif
    for (unsigned shift = 1; shift < 64; shift *= 2) {
        value ^= value << shift;
    }
    return value;
}

// At each temporal position, y = b XOR (a AND inlet). The XOR prefix
// removes invert transitions, leaving a kill/generate/propagate carry scan.
inline Word carry_scan(Word a, Word b, int initial, bool use_pmull) {
    const Word parity = prefix_parity(a & b, use_pmull) << 1U;
    const Word generate = (~a) & (b ^ parity);
    const Word propagate = a | generate;
    return (propagate + generate + static_cast<Word>(initial)) ^ propagate ^
           generate ^ parity;
}

inline Planes quotient_five(Word bit, const Planes &value) {
    return {
        ~bit & (value[0] | value[1]),         ~bit & (value[2] | value[3]),
        (~bit & value[4]) | (bit & value[0]), bit & (value[1] | value[2]),
        bit & (value[3] | value[4]),
    };
}

inline Planes double_mod_five(const Planes &value, Word carry) {
    return {
        (value[0] & ~carry) | (value[2] & carry),
        (value[3] & ~carry) | (value[0] & carry),
        (value[1] & ~carry) | (value[3] & carry),
        (value[4] & ~carry) | (value[1] & carry),
        (value[2] & ~carry) | (value[4] & carry),
    };
}

template <int Multiplier>
int digitplanes(State &state, int inlet, int count, bool emit, bool use_pmull) {
    const auto last_lane = static_cast<unsigned>(count - 1);
    if constexpr (Multiplier == 2) {
        const Word c = state.c[1];
        const Word t = state.t[1];
        const Word a0 = state.r[2] | state.r[4] | (state.r[1] & c);
        const Word a1 = state.r[1] | state.r[4] | (state.r[3] & c);
        const Word b0 = state.s[2] | state.s[4] | (state.s[1] & t);
        const Word b1 = state.s[1] | state.s[4] | (state.s[3] & t);
        const Word delta = b0 ^ b1;
        const Word beta = b0 ^ (a0 & delta);
        const Word mask =
            carry_scan((a0 ^ a1) & delta, beta, inlet / 5, use_pmull);
        const Word q2 = a0 ^ ((a0 ^ a1) & mask);
        const Planes b = double_mod_five(state.s, q2);
        int result = static_cast<int>((t >> last_lane) & 1U);
        for (int i = 1; i < 5; ++i) {
            if (((b[static_cast<std::size_t>(i)] >> last_lane) & 1U) != 0) {
                result += 2 * i;
            }
        }
        if (!emit) {
            return result;
        }
        Planes r = double_mod_five(b, t);
        for (int i = 0; i < 5; ++i) {
            auto &plane = r[static_cast<std::size_t>(i)];
            plane = (plane << 1U) | static_cast<Word>(inlet % 5 == i);
        }
        const Word cc = state.r[3] | state.r[4] | (state.r[2] & mask);
        const Word tt = state.s[3] | state.s[4] | (state.s[2] & q2);
        state.s = double_mod_five(double_mod_five(state.r, mask), c);
        state.r = r;
        state.c[0] = ~cc;
        state.c[1] = cc;
        state.t[0] = ~tt;
        state.t[1] = tt;
        return result;
    } else {
        const Word d0 = state.c[1] ^ state.c[3];
        const Word d1 = state.t[1] ^ state.t[3];
        const Word z0 =
            state.c[2] ^ state.c[3] ^ (state.r[1] & d0) ^ state.s[1];
        const Word beta = (state.t[2] | state.t[3]) ^ (z0 & d1);
        const Word mask = carry_scan(d0 & d1, beta, (inlet / 2) % 2, use_pmull);
        const Word z = z0 ^ (mask & d0);
        int result = static_cast<int>((z >> last_lane) & 1U) * 5;
        for (int i = 1; i < 5; ++i) {
            if (((state.t[static_cast<std::size_t>(i)] >> last_lane) & 1U) !=
                0) {
                result += i;
            }
        }
        if (!emit) {
            return result;
        }
        Planes h = quotient_five(z, state.t);
        for (int i = 0; i < 5; ++i) {
            auto &plane = h[static_cast<std::size_t>(i)];
            plane = (plane << 1U) | static_cast<Word>(inlet / 2 == i);
        }
        const Word x = state.r[1] ^ mask;
        const Planes t = quotient_five(state.s[1], quotient_five(x, state.c));
        const Planes c = quotient_five(state.r[1], h);
        const Word r = ((z ^ (state.t[1] | state.t[3])) << 1U) |
                       static_cast<Word>(inlet % 2);
        const Word s = x ^ (state.c[1] | state.c[3]);
        state.r[0] = ~r;
        state.r[1] = r;
        state.s[0] = ~s;
        state.s[1] = s;
        state.c = c;
        state.t = t;
        return result;
    }
}

template <int Multiplier>
constexpr int advance_uniform(std::array<int, 4> &state, int inlet) {
    constexpr int Base = 10 / Multiplier;
    int digit = inlet;
    for (std::size_t left = 0; left < state.size(); left += 2) {
        const auto right = left + 1;
        const int intermediate = (Multiplier * state[left]) + (digit / Base);
        const int result = (Multiplier * (intermediate % Base)) + state[right];
        state[left] = digit % Base;
        state[right] = intermediate / Base;
        digit = result;
    }
    return digit;
}

inline State uniform_planes(const std::array<int, 4> &state) {
    State value;
    value.r[static_cast<std::size_t>(state[0])] = ~Word{0};
    value.c[static_cast<std::size_t>(state[1])] = ~Word{0};
    value.s[static_cast<std::size_t>(state[2])] = ~Word{0};
    value.t[static_cast<std::size_t>(state[3])] = ~Word{0};
    return value;
}

inline void fill_unreached(State &target, const State &uniform, Word reached) {
    for (std::size_t i = 0; i < 5; ++i) {
        target.r[i] = (target.r[i] & reached) | (uniform.r[i] & ~reached);
        target.c[i] = (target.c[i] & reached) | (uniform.c[i] & ~reached);
        target.s[i] = (target.s[i] & reached) | (uniform.s[i] & ~reached);
        target.t[i] = (target.t[i] & reached) | (uniform.t[i] & ~reached);
    }
}

// The five supplied digits determine one cyclic joint-port grammar. Each
// four-tick layer moves by -4 modulo 5, so its temporal phase advances by
// one. A complete ordered transition checks both the digit and the port
// passed to the adjoining column.
template <int Multiplier> class PeriodicFront {
    static constexpr std::array<int, 5> motif =
        Multiplier == 2 ? std::array<int, 5>{6, 9, 2, 0, 7}
                        : std::array<int, 5>{9, 6, 7, 0, 2};

    static constexpr auto symbols = [] {
        std::array<std::array<int, 4>, 5> ports{};
        for (std::size_t phase = 0; phase < motif.size(); ++phase) {
            for (std::size_t offset = 1; offset < motif.size(); ++offset) {
                advance_uniform<Multiplier>(ports[phase],
                                            motif[(phase + offset) % 5]);
            }
        }
        return ports;
    }();

    static_assert([] {
        for (std::size_t phase = 0; phase < motif.size(); ++phase) {
            auto outgoing = symbols[phase];
            const int emitted =
                advance_uniform<Multiplier>(outgoing, motif[phase]);
            const auto next = (phase + 1) % 5;
            if (emitted != motif[next] || outgoing != symbols[next]) {
                return false;
            }
        }
        return true;
    }());

    static constexpr auto windows = [] {
        std::array<State, 5> packed{};
        for (std::size_t phase = 0; phase < motif.size(); ++phase) {
            auto &word = packed[phase];
            for (std::size_t lane = 0; lane < 64; ++lane) {
                const auto &port = symbols[(phase + lane) % 5];
                const Word bit = Word{1} << lane;
                word.r[static_cast<std::size_t>(port[0])] |= bit;
                word.c[static_cast<std::size_t>(port[1])] |= bit;
                word.s[static_cast<std::size_t>(port[2])] |= bit;
                word.t[static_cast<std::size_t>(port[3])] |= bit;
            }
        }
        return packed;
    }();

    const std::size_t blocks_;

    static const State &window(std::size_t phase, std::size_t chunk) {
        return windows[(phase + (4 * (chunk % 5))) % 5];
    }

  public:
    explicit PeriodicFront(std::size_t blocks) : blocks_(blocks) {}
    static constexpr std::size_t table_bytes = sizeof(windows);

    bool matches_phase(const std::vector<State> &current,
                       std::size_t phase) const {
        if (current.size() != (blocks_ + 63) / 64) {
            return false;
        }
        for (std::size_t j = 0; j < current.size(); ++j) {
            const auto count = std::min<std::size_t>(64, blocks_ - (64 * j));
            const Word mask = count == 64 ? ~Word{0} : (Word{1} << count) - 1;
            const auto &expected = window(phase, j);
            const auto &actual = current[j];
            for (std::size_t i = 0; i < 5; ++i) {
                if (((actual.r[i] ^ expected.r[i]) & mask) != 0 ||
                    ((actual.c[i] ^ expected.c[i]) & mask) != 0 ||
                    ((actual.s[i] ^ expected.s[i]) & mask) != 0 ||
                    ((actual.t[i] ^ expected.t[i]) & mask) != 0) {
                    return false;
                }
            }
        }
        return true;
    }

    static void restore(std::vector<State> &current, std::size_t phase) {
        for (std::size_t j = 0; j < current.size(); ++j) {
            current[j] = window(phase, j);
        }
    }

    static const State &phase_word(std::size_t phase, std::size_t chunk) {
        return window(phase, chunk);
    }

    static constexpr int gate4(int a, int b, int c, int d, int e) {
        constexpr auto pair = [](int left, int digit, int right) {
            return relative_cell(Multiplier, 10 / Multiplier, left, digit,
                                 right);
        };
        return pair(pair(e, d, c), pair(d, c, b), pair(c, b, a));
    }

    static constexpr int port(int digit) {
        if constexpr (Multiplier == 2) {
            return digit / 5;
        } else {
            return (digit / 2) % 2;
        }
    }

    static constexpr std::array<int, 5> train_base =
        Multiplier == 2 ? std::array<int, 5>{0, 0, 1, 0, 0}
                        : std::array<int, 5>{2, 0, 1, 0, 0};

    using ReadyRow = std::array<int, 12>;
    static constexpr std::array train_table{
        Multiplier == 2 ? ReadyRow{2, 4, 5, 7, 8, 10, 11, 13, 14, 16, 17, 19}
                        : ReadyRow{1, 2, 3, 4, 6, 7, 9, 10, 12, 13, 15, 16},
        ReadyRow{1, 3, 4, 6, 7, 9, 10, 12, 13, 15, 16, 18},
        ReadyRow{1, 2, 3, 5, 6, 8, 9, 11, 12, 14, 15, 17},
        ReadyRow{2, 3, 5, 6, 8, 9, 11, 12, 14, 15, 17, 18},
        ReadyRow{1, 2, 4, 5, 7, 8, 10, 11, 13, 14, 16, 17},
    };

    static constexpr std::size_t train_table_bytes =
        sizeof(train_base) + sizeof(train_table);

    static constexpr std::size_t ready(std::size_t phase, std::size_t i) {
        const auto base = static_cast<std::size_t>(train_base[phase]);
        if (i < base) {
            return static_cast<std::size_t>(train_table[phase][i]);
        }
        const auto offset = i - base;
        return static_cast<std::size_t>(
                   train_table[phase][base + (offset % 10)]) +
               (15 * (offset / 10));
    }

    static constexpr int train_value(int column, int tick) {
        const int phase = ((column % 5) + 10 - ((4 * (tick % 5)) % 5)) % 5;
        return motif[static_cast<std::size_t>(phase)];
    }

    static constexpr bool check_train() {
        for (int phase = 0; phase < 5; ++phase) {
            std::array<int, 4> state{};
            for (int i = 0;
                 i < train_base[static_cast<std::size_t>(phase)] + 14; ++i) {
                const int earliest =
                    std::max({state[0], state[1], state[2], state[3]});
                int best = 1000;
                for (int t = earliest; t < earliest + 5; ++t) {
                    const int x = phase + i;
                    const int a = train_value(x - 4, t),
                              b = train_value(x - 3, t);
                    const int c = train_value(x - 2, t),
                              d = train_value(x - 1, t);
                    const int lo = gate4(a, b, c, d, 0),
                              hi = gate4(a, b, c, d, Multiplier == 2 ? 5 : 2);
                    for (int inlet = 0; inlet < 10; ++inlet) {
                        if (gate4(a, b, c, d, inlet) !=
                            (port(inlet) == 0 ? lo : hi)) {
                            return false;
                        }
                    }
                    if (lo == hi) {
                        best = std::min(best, t + 1);
                    } else if (port(lo) == port(hi)) {
                        best = std::min(best, t + 2);
                    }
                }
                if (best !=
                    static_cast<int>(ready(static_cast<std::size_t>(phase),
                                           static_cast<std::size_t>(i)))) {
                    return false;
                }
                state = {state[1], state[2], state[3], best};
            }
        }
        return true;
    }

    static_assert(check_train());

    static int phase_of(int digit) {
        for (std::size_t i = 0; i < motif.size(); ++i) {
            if (motif[i] == digit) {
                return static_cast<int>(i);
            }
        }
        return -1;
    }
    static int input(std::size_t phase) { return motif[phase % 5]; }
    int output(std::size_t phase) const { return motif[(phase + blocks_) % 5]; }
};

template <int Multiplier>
std::string four_tick_wave(const std::string &seed, std::size_t ticks,
                           std::uint64_t &updates, std::uint64_t &front_columns,
                           std::uint64_t &front_probes,
                           std::uint64_t &train_columns,
                           std::uint64_t &train_words_skipped,
                           std::uint64_t &train_ready_lookups,
                           std::uint64_t &front_table_bytes, double &setup_ms,
                           bool enable_front) {
    const std::size_t blocks = ticks / 4;
    const std::size_t width = seed.size() + (4 * blocks);
    std::string output(width, '0');
    if (blocks == 0) {
        std::reverse_copy(seed.begin(), seed.end(), output.begin());
        return output;
    }

    // The physical zero halo is stationary. A source column can reach at
    // most one new four-tick layer. Every unreached layer sees a constant
    // inlet, whose exact four-gate response is carried in the uniform state.
    const auto setup_begin = std::chrono::steady_clock::now();
    std::array<int, 4> uniform{};
    std::vector<State> states;
    states.reserve((blocks + 63) / 64);
    const bool use_pmull = has_pmull();
    setup_ms += std::chrono::duration<double, std::milli>(
                    std::chrono::steady_clock::now() - setup_begin)
                    .count();
    std::optional<PeriodicFront<Multiplier>> front;
    std::size_t i = 0;
    while (i < width) {
        // Probe only a promising complete source word and all reached ports.
        // No periodic inlet is assumed from the source digits alone.
        if (enable_front && i >= blocks && i + 64 <= seed.size() &&
            i % 64 == 0) {
            const int first = seed[seed.size() - i - 1] - '0';
            const int start = PeriodicFront<Multiplier>::phase_of(first);
            bool patterned = start >= 0;
            for (std::size_t j = 0; patterned && j < 64; ++j) {
                const int digit = seed[seed.size() - (i + j) - 1] - '0';
                const int expected = PeriodicFront<Multiplier>::input(
                    static_cast<std::size_t>(start) + j);
                patterned = digit == expected;
            }
            if (patterned) {
                ++front_probes;
                if (!front) {
                    const auto front_begin = std::chrono::steady_clock::now();
                    front.emplace(blocks);
                    front_table_bytes = PeriodicFront<Multiplier>::table_bytes;
                    setup_ms +=
                        std::chrono::duration<double, std::milli>(
                            std::chrono::steady_clock::now() - front_begin)
                            .count();
                }
                auto phase = static_cast<std::size_t>(start);
                if (front->matches_phase(states, phase)) {
                    do {
                        output[i] =
                            static_cast<char>('0' + front->output(phase));
                        ++front_columns;
                        ++i;
                        phase = (phase + 1) % 5;
                    } while (i < seed.size() &&
                             seed[seed.size() - i - 1] - '0' ==
                                 PeriodicFront<Multiplier>::input(phase));
                    PeriodicFront<Multiplier>::restore(states, phase);
                    if (blocks >= 512 && seed.size() - i >= 512) {
                        front_table_bytes +=
                            PeriodicFront<Multiplier>::train_table_bytes;
                        const auto origin = i;
                        const auto origin_phase = phase;
                        states.clear();
                        while (i < width) {
                            ++train_ready_lookups;
                            const auto ready = PeriodicFront<Multiplier>::ready(
                                origin_phase, i - origin);
                            const auto cap = std::min(blocks, ready);
                            while (states.size() < (cap + 63) / 64) {
                                states.push_back(
                                    PeriodicFront<Multiplier>::phase_word(
                                        phase, states.size()));
                            }
                            train_words_skipped += static_cast<std::uint64_t>(
                                ((blocks + 63) / 64) - states.size());
                            int digit = i < seed.size()
                                            ? seed[seed.size() - i - 1] - '0'
                                            : 0;
                            for (std::size_t k = 0; k < states.size(); ++k) {
                                const int count = static_cast<int>(
                                    std::min<std::size_t>(64, cap - (64 * k)));
                                digit = digitplanes<Multiplier>(
                                    states[k], digit, count, i + 1 < width,
                                    use_pmull);
                                ++updates;
                            }
                            output[i] = static_cast<char>(
                                '0' + (blocks >= ready ? front->output(phase)
                                                       : digit));
                            if (blocks >= ready) {
                                ++front_columns;
                                ++train_columns;
                            }
                            ++i;
                            phase = (phase + 1) % 5;
                            if (blocks >= ready && cap % 64 && i < width) {
                                const Word mask = (Word{1} << (cap % 64)) - 1;
                                fill_unreached(
                                    states.back(),
                                    PeriodicFront<Multiplier>::phase_word(
                                        phase, states.size() - 1),
                                    mask);
                            }
                            if (cap == blocks) {
                                break;
                            }
                        }
                    }
                    continue;
                }
            }
        }
        const std::size_t covered = std::min(blocks, i + 1);
        if (states.size() < (covered + 63) / 64) {
            states.push_back(uniform_planes(uniform));
        }
        int value = i < seed.size() ? seed[seed.size() - i - 1] - '0' : 0;
        for (std::size_t j = 0; j < states.size(); ++j) {
            const auto count =
                static_cast<int>(std::min<std::size_t>(64, covered - (64 * j)));
            value = digitplanes<Multiplier>(states[j], value, count,
                                            i + 1 < width, use_pmull);
            ++updates;
        }
        output[i] = static_cast<char>('0' + value);
        if (blocks >= i + 1 && i + 1 < width) {
            advance_uniform<Multiplier>(uniform, value);
            if ((covered % 64) != 0) {
                const Word reached = (Word{1} << (covered % 64)) - 1;
                fill_unreached(states.back(), uniform_planes(uniform), reached);
            }
        }
        ++i;
    }
    return output;
}
} // namespace rev10::dense
#endif
