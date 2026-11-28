// Physical reverse/multiply endpoint engine (C++20).
// Diagonal boundary actions adapted from the supplied collision prototype.
// Finite Laurent support; no physical width replay or temporal carry bank.
#include "rev10.hpp"
#include "relative_return.hpp"
#ifdef __ARM_NEON
#include <arm_neon.h>
#endif
#include <algorithm>
#include <array>
#include <chrono>
#include <cstddef>
#include <cstdint>
#include <limits>
#include <ratio>
#include <stdexcept>
#include <string>
#include <string_view>
#include <utility>
#include <vector>
using namespace std;
namespace rev10 {
using u32 = uint32_t;
using u64 = uint64_t;
using I = int64_t;
using Clock = chrono::steady_clock;
constexpr int MAX_SIDE = 7;
constexpr u32 RANK_MASK = 0xFFFF;

static constexpr int phase_at(I position) {
    return static_cast<int>(position % 2 != 0);
}

static constexpr pair<int, int> gate(int multiplier, int base, bool odd,
                                     int inlet, int digit) {
    const int combined =
        odd ? (multiplier * digit) + inlet : (multiplier * inlet) + digit;
    return odd ? pair{combined % base, combined / base}
               : pair{combined / base, combined % base};
}

// The same exact cell law describes both the finite table and its scalar
// oracle. Boundary ranks use least-significant mixed-radix digits first.
static constexpr pair<int, int> direct_square(int side, int multiplier,
                                              int phase, int west, int south) {
    if (side < 1 || side > MAX_SIDE || (multiplier != 2 && multiplier != 5)) {
        throw runtime_error("invalid diagonal square");
    }
    const int base = 10 / multiplier;
    int west_radix[MAX_SIDE]{}, south_radix[MAX_SIDE]{};
    int inlet[MAX_SIDE]{}, row[MAX_SIDE]{}, east[MAX_SIDE]{};
    for (int i = 0; i < side; ++i) {
        west_radix[i] = phase_at(phase + i) != 0 ? multiplier : base;
        south_radix[i] = 10 / west_radix[i];
        inlet[i] = west % west_radix[i];
        west /= west_radix[i];
        row[i] = south % south_radix[i];
        south /= south_radix[i];
    }
    for (int y = 0; y < side; ++y) {
        int carry = inlet[y];
        for (int x = 0; x < side; ++x) {
            const auto out = gate(multiplier, base,
                                  phase_at(phase + x + y) != 0, carry, row[x]);
            carry = out.first;
            row[x] = out.second;
        }
        east[y] = carry;
    }
    const bool swap_radix = phase_at(side - 1) != 0;
    int e = 0, n = 0;
    for (int i = side - 1; i >= 0; --i) {
        e = (e * (swap_radix ? west_radix[i] : south_radix[i])) + east[i];
        n = (n * (swap_radix ? south_radix[i] : west_radix[i])) + row[i];
    }
    return {e, n};
}

static constexpr array<u32, 500> side_three_table(int multiplier) {
    array<u32, 500> table{};
    const int west_ranks = multiplier == 2 ? 50 : 20;
    for (int j = 0; j < 500; ++j) {
        const auto [east, north] =
            direct_square(3, multiplier, 0, j % west_ranks, j / west_ranks);
        table[static_cast<size_t>(j)] =
            static_cast<u32>(east) | (static_cast<u32>(north) << 16U);
    }
    return table;
}

// Both tables contain only source-independent actions, and the query still
// reserves and owns its copied table before the native call.
static constexpr auto SIDE_THREE_DOUBLE = side_three_table(2);
static constexpr auto SIDE_THREE_FIVE = side_three_table(5);

static int complement_rank(int rank, int total, u32 mask) {
    const auto direct = static_cast<u32>(rank);
    const auto reflected = static_cast<u32>(total - 1 - rank);
    return static_cast<int>(direct ^ ((direct ^ reflected) & mask));
}

static double ms(Clock::time_point a, Clock::time_point b) {
    return chrono::duration<double, milli>(b - a).count();
}
static void require(bool b, const char *msg) {
    if (!b) {
        throw runtime_error(msg);
    }
}
static string decimal(string s) {
    require(!s.empty(), "empty seed");
    for (char c : s) {
        require(c >= '0' && c <= '9', "seed must contain decimal digits only");
    }
    auto i = s.find_first_not_of('0');
    if (i == string::npos) {
        return "0";
    }
    s.erase(0, i);
    return s;
}
static string core(string s) {
    while (s.size() > 1 && s.back() == '0') {
        s.pop_back();
    }
    return s;
}
// In the live image of F_m, at most one trailing zero is possible.
// Restore it iff the normalized output is not divisible by m.
static string physical_readout(string s, int m, I n) {
    auto l = s.find_first_not_of('0');
    if (l == string::npos) {
        return "0";
    }
    auto r = s.find_last_not_of('0');
    s = s.substr(l, r - l + 1);
    if (phase_at(n) != 0) {
        reverse(s.begin(), s.end());
    }
    if (((s.back() - '0') % m) != 0) {
        s.push_back('0');
    }
    return s;
}

// Small rectangular children allow a four-way join at odd square sizes.
// Each parity owns its complementary inlet pairs; no source states are used.
struct Rect {
    int x, y, W[2]{}, S[2]{}, E[2]{}, N[2]{};
    vector<u32> tab[2];
    static int radix(int p) { return phase_at(p) != 0 ? 2 : 5; }
    static int rank_count(int n, int p) {
        int r = 1;
        for (int i = 0; i < n; i++) {
            r *= radix(p + i);
        }
        return r;
    }
    static void unpack(int q, int n, int p, int *a) {
        if (n < 0 || n > MAX_SIDE) {
            throw runtime_error("invalid rectangular boundary width");
        }
        for (int i = 0; i < n; i++) {
            int r = radix(p + i);
            a[i] = q % r;
            q /= r;
        }
    }
    static int pack(int n, int p, const int *a) {
        if (n < 0 || n > MAX_SIDE) {
            throw runtime_error("invalid rectangular boundary width");
        }
        int q = 0;
        for (int i = n - 1; i >= 0; i--) {
            q = (q * radix(p + i)) + a[i];
        }
        return q;
    }
    Rect(int w, int h) : x(w), y(h) {
        for (int p = 0; p < 2; p++) {
            W[p] = rank_count(y, p);
            S[p] = rank_count(x, 1 - p);
            E[p] = rank_count(y, phase_at(p + x));
            N[p] = rank_count(x, phase_at(p + y - 1));
            tab[p].resize(std::size_t(W[p] * S[p] / 2));
            for (int j = 0; j < int(tab[p].size()); j++) {
                int west[MAX_SIDE], row[MAX_SIDE], east[MAX_SIDE];
                unpack(j % W[p], y, p, west);
                unpack(j / W[p], x, 1 - p, row);
                for (int v = 0; v < y; v++) {
                    int a = west[v];
                    for (int u = 0; u < x; u++) {
                        bool odd = phase_at(p + u + v) != 0;
                        int d = odd ? (2 * row[u]) + a : (2 * a) + row[u];
                        a = odd ? d % 5 : d / 5;
                        row[u] = odd ? d / 5 : d % 5;
                    }
                    east[v] = a;
                }
                tab[p][std::size_t(j)] =
                    u32(pack(y, phase_at(p + x), east)) |
                    (u32(pack(x, phase_at(p + y - 1), row)) << 16U);
            }
        }
    }
    pair<int, int> eval(int p, int w, int s) const {
        int j = w + (W[p] * s), total = W[p] * S[p];
        bool c = j >= total / 2;
        j = c ? total - 1 - j : j;
        u32 d = tab[p][std::size_t(j)];
        int a = static_cast<int>(d & RANK_MASK), b = static_cast<int>(d >> 16U);
        return c ? make_pair(E[p] - 1 - a, N[p] - 1 - b) : make_pair(a, b);
    }
};

struct Table {
    int b, m, base;
    int W[2]{}, S[2]{}, E[2]{}, N[2]{}, rad[2][2][MAX_SIDE]{};
    int tot = 0;
    vector<u32> tab;
    Table(int side, int multiplier)
        : b(side), m(multiplier), base(10 / multiplier) {
        require(b >= 1 && b <= MAX_SIDE, "tile side must be 1..7");
        require(m == 2 || m == 5, "invalid multiplier");
        for (int p = 0; p < 2; p++) {
            W[p] = S[p] = E[p] = N[p] = 1;
            for (int j = 0; j < b; j++) {
                rad[p][0][j] = (phase_at(p + j) != 0) ? m : base;
                rad[p][1][j] = 10 / rad[p][0][j];
                W[p] *= rad[p][0][j];
                S[p] *= rad[p][1][j];
            }
        }
        for (int p = 0; p < 2; p++) {
            for (int j = 0; j < b; j++) {
                E[p] *= rad[phase_at(p + b - 1)][1][j];
                N[p] *= rad[phase_at(p + b - 1)][0][j];
            }
        }
        tot = W[0] * S[0];
        tab.resize(std::size_t(tot / 2));
    }
    void unpack(int x, const int *rd, int *out) const {
        if (b < 1 || b > MAX_SIDE) {
            throw runtime_error("invalid diagonal boundary width");
        }
        for (int i = 0; i < b; i++) {
            out[i] = x % rd[i];
            x /= rd[i];
        }
    }
    int pack(const int *x, const int *rd) const {
        if (b < 1 || b > MAX_SIDE) {
            throw runtime_error("invalid diagonal boundary width");
        }
        int v = 0;
        for (int i = b - 1; i >= 0; i--) {
            v = (v * rd[i]) + x[i];
        }
        return v;
    }
    static u32 code(int e, int n) { return u32(e) | (u32(n) << 16U); }
    pair<int, int> eval(int p, int west, int south) const {
        if (p != 0) {
            swap(west, south);
        }
        int j = west + (W[0] * south);
        const u32 mask = 0U - static_cast<u32>(j >= tot / 2);
        const u32 d = tab[std::size_t(complement_rank(j, tot, mask))];
        const int a =
            complement_rank(static_cast<int>(d & RANK_MASK), E[0], mask);
        const int north =
            complement_rank(static_cast<int>(d >> 16U), N[0], mask);
        return (p != 0) ? make_pair(north, a) : make_pair(a, north);
    }
    pair<int, int> direct(int p, int w, int s) const {
        return direct_square(b, m, p, w, s);
    }
    void store(int j, int e, int n) { tab[std::size_t(j)] = code(e, n); }
    size_t payload_bytes() const { return tab.size() * sizeof(u32); }
    static Table side_three(int multiplier) {
        Table table(3, multiplier);
        const auto &precomputed =
            multiplier == 2 ? SIDE_THREE_DOUBLE : SIDE_THREE_FIVE;
        std::copy(precomputed.begin(), precomputed.end(), table.tab.begin());
        return table;
    }
    static Table forward(int side) {
        require(side >= 1 && side <= MAX_SIDE,
                "invalid diagonal boundary width");
        if (side == 3) {
            return side_three(2);
        }
        int base_side = side;
        while (base_side % 2 == 0) {
            base_side /= 2;
        }
        Table current(base_side, 2);
        if (base_side > 1) {
            int a = base_side / 2, c = base_side - a, p = phase_at(a);
            Rect sw(a, a), se(c, a), nw(a, c), ne(c, c);
            for (int j = 0; j < current.tot / 2; j++) {
                int w = j % current.W[0], s = j / current.W[0];
                auto x = sw.eval(0, w % sw.W[0], s % sw.S[0]);
                auto y = se.eval(p, x.first, s / sw.S[0]);
                auto z = nw.eval(p, w / sw.W[0], x.second);
                auto h = ne.eval(0, z.first, y.second);
                current.store(j, y.first + (se.E[p] * h.first),
                              z.second + (nw.N[p] * h.second));
            }
        } else {
            for (int j = 0; j < current.tot / 2; j++) {
                auto [east, north] =
                    current.direct(0, j % current.W[0], j / current.W[0]);
                current.store(j, east, north);
            }
        }
        for (int next_side = base_side * 2; next_side <= side; next_side *= 2) {
            Table next(next_side, 2);
            int p = phase_at(current.b);
            for (int j = 0; j < next.tot / 2; j++) {
                int w = j % next.W[0], s = j / next.W[0];
                auto sw = current.eval(0, w % current.W[0], s % current.S[0]);
                auto se = current.eval(p, sw.first, s / current.S[0]);
                auto nw = current.eval(p, w / current.W[0], sw.second);
                auto ne = current.eval(0, nw.first, se.second);
                next.store(j, se.first + (current.E[p] * ne.first),
                           nw.second + (current.N[p] * ne.second));
            }
            current = std::move(next);
        }
        return current;
    }
    // Rotate by 180 degrees, invert each gate: Q5 with swapped lane types
    // is Q2^{-1}. The edge symbols must be reversed, not just the ranks
    // swapped.
    vector<int> reversal_map(int len, const int *rd) const {
        vector<int> v(std::size_t(len), 0);
        int a[MAX_SIDE];
        for (int j = 0; j < len; j++) {
            unpack(j, rd, a);
            int x = 0;
            for (int k = 0; k < b; k++) {
                x = (x * rd[k]) + a[k];
            }
            v[std::size_t(j)] = x;
        }
        return v;
    }
    Table inverse5() const {
        require(m == 2, "inverse5 requires doubling table");
        Table t(b, 5);
        int q = phase_at(b - 1);
        auto rw = reversal_map(W[0], rad[0][0]),
             rs = reversal_map(S[0], rad[0][1]);
        auto re = reversal_map(E[0], rad[q][1]),
             rn = reversal_map(N[0], rad[q][0]);
        require(t.W[0] == E[0] && t.S[0] == N[0] && t.E[0] == W[0] &&
                    t.N[0] == S[0],
                "inverse radix mismatch");
        for (int j = 0; j < tot / 2; j++) {
            auto d = make_pair(int(tab[std::size_t(j)] & RANK_MASK),
                               int(tab[std::size_t(j)] >> 16U));
            int k =
                re[std::size_t(d.first)] + (t.W[0] * rn[std::size_t(d.second)]);
            int e = rw[std::size_t(j % W[0])], n = rs[std::size_t(j / W[0])];
            if (k >= tot / 2) {
                k = tot - 1 - k;
                e = t.E[0] - 1 - e;
                n = t.N[0] - 1 - n;
            }
            t.store(k, e, n);
        }
        return t;
    }
};

// The four frontier arrays represent adjacent diagonal tile boundaries.
static void full_wave(const Table &t, int p, int lo, int hi, const int *west,
                      const int *south, int *east, int *north) {
    int k = lo;
#ifdef __ARM_NEON
    // Transposition exchanges both inputs and both outputs. Each stored rank
    // fits its own 16-bit field, so packed complement has no cross-field
    // borrow.
    const int *first = p == 0 ? west : south;
    const int *second = p == 0 ? south : west;
    int *low = p == 0 ? east : north;
    int *high = p == 0 ? north : east;
    const auto last = vdupq_n_s32(t.tot - 1);
    const auto top = vdupq_n_u32(Table::code(t.E[0] - 1, t.N[0] - 1));
    for (; k <= hi - 3; k += 4) {
        const auto rank =
            vmlaq_n_s32(vld1q_s32(first + k), vld1q_s32(second + k), t.W[0]);
        const auto reflected = vsubq_s32(last, rank);
        const auto index = vminq_s32(rank, reflected);
        const uint32x4_t entries = {
            t.tab[static_cast<size_t>(vgetq_lane_s32(index, 0))],
            t.tab[static_cast<size_t>(vgetq_lane_s32(index, 1))],
            t.tab[static_cast<size_t>(vgetq_lane_s32(index, 2))],
            t.tab[static_cast<size_t>(vgetq_lane_s32(index, 3))],
        };
        const auto response = vbslq_u32(vcgtq_s32(rank, reflected),
                                        vsubq_u32(top, entries), entries);
        vst1q_s32(low + k, vreinterpretq_s32_u32(
                               vandq_u32(response, vdupq_n_u32(RANK_MASK))));
        vst1q_s32(high + k, vreinterpretq_s32_u32(vshrq_n_u32(response, 16)));
    }
#endif
    for (; k <= hi; k++) {
        auto a = t.eval(p, west[k], south[k]);
        east[k] = a.first;
        north[k] = a.second;
    }
}
static string wave_raw(const Table &t, const string &seed, I n, Stats &st) {
    const I source_end = static_cast<I>(seed.size()) - 1;
    const I output_end = source_end + n;
    const int b = t.b;
    require(output_end <= I(numeric_limits<int>::max()) - MAX_SIDE,
            "coordinate range exceeded");
    const int qmax = int(output_end / b);
    string out(size_t(output_end + 1), '0');
    // E is stored shifted one position: east output at k enters west at k+1.
    vector<int> ew(std::size_t(qmax + 3), 0), sn(std::size_t(qmax + 3), 0),
        ne(std::size_t(qmax + 3), 0), nn(std::size_t(qmax + 3), 0);
    int lo = 0, hi = -1;
    I first =
        max<I>(0, (source_end - (2 * (static_cast<I>(b) - 1)) + b - 1) / b);
    for (int q = int(first); q <= qmax; q++) {
        I z0 = (I(q) * b) - source_end, z1 = z0 + (2 * (static_cast<I>(b) - 1));
        int p = phase_at(z0);
        bool source = z0 <= 0 && z1 >= 0;
        int a = lo, c = min(q, hi);
        if (hi < lo) {
            a = 0;
            c = -1;
        }
        if (source) {
            a = 0;
            c = q;
        }
        if (c < a) {
            continue;
        }
        // Entries outside the preceding wave's active interval are zero. Clear
        // only newly exposed frontier cells, not the whole bounding rectangle.
        if (a < lo || hi < lo) {
            int end = hi < lo ? c : min(c, lo - 1);
            fill(ew.begin() + a, ew.begin() + end + 1, 0);
            fill(sn.begin() + a, sn.begin() + end + 1, 0);
        }
        if (hi >= lo && c > hi) {
            fill(ew.begin() + max(a, hi + 1), ew.begin() + c + 1, 0);
            fill(sn.begin() + max(a, hi + 1), sn.begin() + c + 1, 0);
        }
        if (z0 > 0 && z1 < n) {
            full_wave(t, p, a, c, ew.data(), sn.data(), ne.data() + 1,
                      nn.data());
            st.tiles += u64(c - a + 1);
        } else {
            {
                for (int k = a; k <= c; k++) {
                    I u = I(k) * b;
                    int we[MAX_SIDE], row[MAX_SIDE], ea[MAX_SIDE];
                    t.unpack(ew[std::size_t(k)], t.rad[p][0], we);
                    t.unpack(sn[std::size_t(k)], t.rad[p][1], row);
                    for (int y = 0; y < b; y++) {
                        int e = we[y];
                        for (int x = 0; x < b; x++) {
                            I column = u + x, tick = z0 + x + y;
                            bool odd = phase_at(tick) != 0;
                            int d = 0;
                            ++st.fringe_cells;
                            if (tick == 0) {
                                if (column <= source_end) {
                                    d = seed[size_t(column)] - '0';
                                }
                            } else if (tick > 0 && tick <= n) {
                                d = odd ? (t.m * row[x]) + e
                                        : (t.m * e) + row[x];
                                ++st.fringe_gates;
                            }
                            if (tick == n) {
                                out[size_t(column)] = char('0' + d);
                            }
                            e = odd ? d % t.base : d / t.base;
                            row[x] = odd ? d / t.base : d % t.base;
                        }
                        ea[y] = e;
                    }
                    int r = phase_at(p + b - 1);
                    ne[(std::size_t(k) + 1)] = t.pack(ea, t.rad[r][1]);
                    nn[std::size_t(k)] = t.pack(row, t.rad[r][0]);
                }
            }
        }
        ne[std::size_t(a)] = 0;
        nn[(std::size_t(c) + 1)] = 0;
        // The new wave may shrink at either edge. This is a boundary-support
        // scan, not a scan of chronological digit rows or of carry histories.
        int nl = a, nh = c + 1;
        while (nl <= nh && ne[std::size_t(nl)] == 0 &&
               nn[std::size_t(nl)] == 0) {
            ++nl;
        }
        while (nh >= nl && ne[std::size_t(nh)] == 0 &&
               nn[std::size_t(nh)] == 0) {
            --nh;
        }
        // Keep the invariant that the live interval describes incoming ranks,
        // not outgoing tile indices. The following wave can use this interval
        // exactly; its source fringe can extend it if required.
        ew.swap(ne);
        sn.swap(nn);
        lo = nl;
        hi = nh;
    }
    return out;
}

static string wave_tiled(const Table &t, const string &seed, I n, Stats &st,
                         RelativeRun run) {
    if (run.hi == run.lo) {
        return physical_readout(wave_raw(t, seed, n, st), t.m, n);
    }
    // The checked source triples form a protected cone. Recompute both full
    // fringes and preserve their physical overlap with the translated center.
    const I left = run.lo + n, right = run.hi, start = right - n;
    const I turns = n / 2;
    string out = wave_raw(t, seed.substr(0, size_t(left)), n, st);
    out.resize(seed.size() + static_cast<size_t>(n));
    if (run.uniform) {
        int digit = seed[size_t(run.lo)] - '0';
        // The two alternating physical gates agree on a uniform inlet.
        for (I tick = 0; tick < n % 6; ++tick) {
            digit = (t.m * (digit % t.base)) + (digit / t.base);
        }
        std::fill(out.begin() + left, out.begin() + right, char('0' + digit));
    } else {
        for (I i = left; i < right; ++i) {
            const I k = i - (run.shift * turns);
            int digit = seed[size_t(k)] - '0';
            if ((n % 2) != 0) {
                digit = (t.m * (digit % t.base)) +
                        ((seed[size_t(k - 1)] - '0') / t.base);
            }
            out[size_t(i)] = char('0' + digit);
        }
    }
    auto tail = wave_raw(t, seed.substr(size_t(start)), n, st);
    std::copy(tail.begin() + n, tail.end(), out.begin() + right);
    return physical_readout(std::move(out), t.m, n);
}

static string diagonal(string seed, int m, I n, int side, Stats &st) {
    if ((n == 0) || seed == "0") {
        return seed;
    }
    auto a = Clock::now();
    seed = core(std::move(seed));
    const auto run = relative_run(seed, m, n);
    Table f =
        (m == 5 && side == 3) ? Table::side_three(5) : Table::forward(side);
    st.table_entries = std::uint64_t(f.tot / 2);
    if (m == 5 && side != 3) {
        auto inv = f.inverse5();
        st.table_entries += std::uint64_t(inv.tot / 2);
        vector<u32>().swap(f.tab);
        st.table_bytes = inv.payload_bytes();
        auto b = Clock::now();
        st.setup_ms = ms(a, b);
        auto s = wave_tiled(inv, seed, n, st, run);
        st.eval_ms = ms(b, Clock::now());
        return s;
    }
    st.table_bytes = f.payload_bytes();
    auto b = Clock::now();
    st.setup_ms = ms(a, b);
    auto s = wave_tiled(f, seed, n, st, run);
    st.eval_ms = ms(b, Clock::now());
    return s;
}

Result nth(string seed, int multiplier, I steps, string_view requested,
           int side) {
    require(multiplier == 2 || multiplier == 5, "invalid multiplier");
    seed = decimal(std::move(seed));
    require(steps >= 0 && steps <= 1000000000 && seed.size() <= 1000000000 &&
                steps + I(seed.size()) < numeric_limits<int>::max() - 256,
            "coordinate range exceeded");
    require(side >= 1 && side <= MAX_SIDE, "tile side must be 1..7");
    require(requested == "diagonal", "unsupported engine");
    Result result;
    result.engine = "diagonal";
    auto a = Clock::now();
    result.digits =
        diagonal(std::move(seed), multiplier, steps, side, result.stats);
    result.total_ms = ms(a, Clock::now());
    return result;
}

} // namespace rev10
