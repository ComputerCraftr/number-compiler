// Independent mixed-radix gate oracle for the dense native bitplanes.
#include "dense_digitplanes.hpp"

#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <random>
#include <set>
#include <stdexcept>

using Word = std::uint64_t;
using Digits = std::array<Word, 10>;
using State = rev10::dense::State;

template <int M, int K> Digits direct_gate(const State &s) {
    constexpr int B = 10 / M;
    std::array<Word, 5> input{}, a{}, q{}, b{};
    Digits middle{}, output{};
    input[K] = ~Word{0};
    for (int i = 0; i < 10; ++i) {
        const auto j = static_cast<std::size_t>(i);
        const Word z = s.r[j / M] & input[j % M];
        a[j % B] |= z;
    }
    for (int i = 0; i < 10; ++i) {
        const auto j = static_cast<std::size_t>(i);
        middle[j] = a[j / M] & s.c[j % M];
        q[j / B] |= middle[j];
    }
    for (int i = 0; i < 10; ++i) {
        const auto j = static_cast<std::size_t>(i);
        const Word z = s.s[j / M] & q[j % M];
        b[j % B] |= z;
    }
    for (int i = 0; i < 10; ++i) {
        const auto j = static_cast<std::size_t>(i);
        output[j] = b[j / M] & s.t[j % M];
    }
    return output;
}

template <int M> int direct_port(State &s, int value, int count, bool emit) {
    constexpr int B = 10 / M;
    const auto low = direct_gate<M, 0>(s);
    const auto high = direct_gate<M, 1>(s);
    auto port = [](const Digits &p) {
        if constexpr (M == 2)
            return p[5] | p[6] | p[7] | p[8] | p[9];
        else
            return p[2] | p[3] | p[6] | p[7];
    };
    Word bias = port(low);
    Word linear = bias ^ port(high);
    const int inlet = M == 2 ? value / 5 : (value / 2) % 2;
    for (int k = 1; k < count; k *= 2) {
        bias ^= linear & (bias << k);
        linear &= (linear << k) | ((Word{1} << k) - 1);
    }
    const Word choice =
        ((bias ^ (inlet != 0 ? linear : 0)) << 1) | static_cast<Word>(inlet);
    Digits source{};
    int output = 0;
    for (int i = 0; i < 10; ++i) {
        const auto j = static_cast<std::size_t>(i);
        const Word digit = (low[j] & ~choice) | (high[j] & choice);
        if (((digit >> (count - 1)) & 1) != 0)
            output = i;
        source[j] = (digit << 1) | static_cast<Word>(i == value);
    }
    if (!emit)
        return output;

    std::array<Word, 5> q0{}, a{}, q1{}, b{}, q2{}, q3{};
    Digits middle{};
    for (int i = 0; i < 10; ++i)
        q0[static_cast<std::size_t>(i / B)] |=
            source[static_cast<std::size_t>(i)];
    for (int i = 0; i < 10; ++i) {
        const auto j = static_cast<std::size_t>(i);
        const Word z = s.r[j / M] & q0[j % M];
        a[j % B] |= z;
        q1[j / B] |= z;
    }
    for (int i = 0; i < 10; ++i) {
        const auto j = static_cast<std::size_t>(i);
        middle[j] = a[j / M] & s.c[j % M];
        q2[j / B] |= middle[j];
    }
    for (int i = 0; i < 10; ++i) {
        const auto j = static_cast<std::size_t>(i);
        const Word z = s.s[j / M] & q2[j % M];
        b[j % B] |= z;
        q3[j / B] |= z;
    }
    s.c = q1;
    s.t = q3;
    s.r = {};
    s.s = {};
    for (int i = 0; i < 10; ++i) {
        const auto j = static_cast<std::size_t>(i);
        s.r[j % B] |= source[j];
        s.s[j % B] |= middle[j];
    }
    return output;
}

template <int M> void check(State input, int digit, int count) {
    const Word mask = count == 64 ? ~Word{0} : (Word{1} << count) - 1;
    for (const bool emit : {false, true}) {
        for (const bool hardware : {false, rev10::dense::has_pmull()}) {
            State expected = input;
            State actual = input;
            const int reference = direct_port<M>(expected, digit, count, emit);
            const int result = rev10::dense::digitplanes<M>(
                actual, digit, count, emit, hardware);
            if (reference != result)
                throw std::runtime_error("wrong selected digit");
            for (std::size_t i = 0; i < 5; ++i)
                if (((expected.r[i] ^ actual.r[i]) & mask) != 0 ||
                    ((expected.c[i] ^ actual.c[i]) & mask) != 0 ||
                    ((expected.s[i] ^ actual.s[i]) & mask) != 0 ||
                    ((expected.t[i] ^ actual.t[i]) & mask) != 0) {
                    std::cerr
                        << "M=" << M << " digit=" << digit << " count=" << count
                        << " emit=" << emit << " index=" << i
                        << " expected=" << (expected.r[i] & mask) << ","
                        << (expected.c[i] & mask) << ","
                        << (expected.s[i] & mask) << ","
                        << (expected.t[i] & mask)
                        << " actual=" << (actual.r[i] & mask) << ","
                        << (actual.c[i] & mask) << "," << (actual.s[i] & mask)
                        << "," << (actual.t[i] & mask) << "\n";
                    throw std::runtime_error("wrong ordered carry port");
                }
        }
    }
}

template <int M> void validate() {
    constexpr int B = 10 / M;
    std::set<std::array<int, 10>> one_digit_responses;
    std::set<std::array<int, 200>> two_digit_responses;
    for (int r = 0; r < B; ++r)
        for (int c = 0; c < M; ++c)
            for (int s = 0; s < B; ++s)
                for (int t = 0; t < M; ++t)
                    for (int digit = 0; digit < 10; ++digit)
                        for (const int count : {1, 7, 63, 64}) {
                            State input;
                            input.r[static_cast<std::size_t>(r)] = ~Word{0};
                            input.c[static_cast<std::size_t>(c)] = ~Word{0};
                            input.s[static_cast<std::size_t>(s)] = ~Word{0};
                            input.t[static_cast<std::size_t>(t)] = ~Word{0};
                            check<M>(input, digit, count);
                        }
    // A projected first digit has fewer responses than the physical port.
    // Continue each full state through every next digit before quotienting.
    for (int r = 0; r < B; ++r)
        for (int c = 0; c < M; ++c)
            for (int s = 0; s < B; ++s)
                for (int t = 0; t < M; ++t) {
                    State input;
                    input.r[static_cast<std::size_t>(r)] = ~Word{0};
                    input.c[static_cast<std::size_t>(c)] = ~Word{0};
                    input.s[static_cast<std::size_t>(s)] = ~Word{0};
                    input.t[static_cast<std::size_t>(t)] = ~Word{0};
                    std::array<int, 10> first{};
                    std::array<int, 200> pair{};
                    for (int a = 0; a < 10; ++a) {
                        State next = input;
                        first[static_cast<std::size_t>(a)] =
                            rev10::dense::digitplanes<M>(next, a, 1, true,
                                                         false);
                        for (int b = 0; b < 10; ++b) {
                            State later = next;
                            const auto index =
                                static_cast<std::size_t>(20 * a + 2 * b);
                            pair[index] = first[static_cast<std::size_t>(a)];
                            pair[index + 1] = rev10::dense::digitplanes<M>(
                                later, b, 1, true, false);
                        }
                    }
                    one_digit_responses.insert(first);
                    two_digit_responses.insert(pair);
                }
    constexpr std::size_t expected_first = M == 2 ? 30 : 20;
    if (one_digit_responses.size() != expected_first ||
        two_digit_responses.size() != 100)
        throw std::runtime_error("invalid selected-digit response quotient");
    std::mt19937_64 random(2026 + M);
    for (int trial = 0; trial < 3000; ++trial) {
        const int count = 1 + static_cast<int>(random() % 64);
        const int digit = static_cast<int>(random() % 10);
        State input;
        for (int i = 0; i < count; ++i) {
            const Word bit = Word{1} << i;
            input.r[random() % B] |= bit;
            input.c[random() % M] |= bit;
            input.s[random() % B] |= bit;
            input.t[random() % M] |= bit;
        }
        check<M>(input, digit, count);
    }
}

int main() {
    validate<2>();
    validate<5>();
    std::cout << "ordered ports match independent mixed-radix oracle\n";
}
