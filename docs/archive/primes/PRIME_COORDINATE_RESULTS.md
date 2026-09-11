# Prime coordinate / pair-field experiment (v0.15.0)

This experiment applies the reverse-and-add coordinate strategy to the prime projector: digit-pair addition, 0/1 carry fields, quotient-first set maps, packed integer programs, alternate radices, and Fibonacci/Zeckendorf coordinates.

## Exact pair-addition theorem

For `n = p + d` in radix `b`, let `S_i = p_i + d_i` and let `C_i` be the ordinary 0/1 carry field. Normalized digits satisfy

```math
z_i = S_i + C_i - b C_{i+1}.
```

But in the weighted integer sum the carry terms telescope, so

```math
n = \sum_i S_i b^i.
```

Therefore every residue/divisibility projector can consume the unnormalised pair field directly. Keeping both pair sums and normalized prime digits would be duplicate state. The useful carry vector reappears below at the packed-wheel level, where it advances several bounded residues in parallel.

## Least-factor tropical quotient

Replace Boolean overlap by the winner field

```math
\lambda(j)=\min\{q:q\mid(start+2j)\},
```

with `0`/infinity for a prime. A divisor lane survives only if it wins at least one candidate. This is an exact finite-window quotient.

| candidates | periodic prime lanes | winning lanes | packed winning modulus bits | `(factor,phase)` bits |
|---:|---:|---:|---:|---:|
| 16 | 17 | 9 | 44 | 149 |
| 64 | 54 | 25 | 151 | 663 |
| 256 | 150 | 54 | 401 | 2336 |
| 1024 | 317 | 124 | 1044 | 5735 |
| 4096 | 446 | 271 | 2515 | 8686 |

At 4,096 candidates this removes 175 of 446 periodic prime lanes. Multiplying only the 271 winning factors gives a 2,515-bit window-specific modulus. The modulus is an exact canonical state for the projected block, but discovering it currently consumes the factor projection, so it is not charged as a free projector.

## Prime-independent universal packed wheel

Let `m=floor(sqrt(H))`. For every candidate `m < n <= H < (m+1)^2`,

```math
n \text{ prime} \iff \gcd(n,\operatorname{lcm}(1,\ldots,m))=1.
```

For this block `m=3163`. The raw LCM is 4,529 bits. Canonicalizing repeated prime-power generators leaves a squarefree 4,428-bit modulus discovered from all naturals with no supplied prime list. The previous 446 lane `(factor,phase)` coordinates alone cost 8,686 bits.

The squarefree generators can also be packed greedily into <=63-bit products. Their residues evolve as

```math
r_i' = r_i + 2 - M_i c_i, \qquad c_i\in\{0,1\}.
```

That gives **78 packed lanes** instead of 446 factor lanes. Ordered small-factor-first, the search from 9,999,993 to 10,000,019 uses **122 word-gcd probes** and an exact 0/1 wrap-carry vector. With <=62-bit groups those 78 residues fit in one **4,992-bit SWAR word**, and one +2 step computes every modular update/carry with a fixed broadword program.


The generator carrier is also self-modifying: when extending the capacity from `m` to `m+1`, the existing packed groups classify the new integer itself. If it is coprime to every prior group, it is a new prime and is packed into the carrier; otherwise it is discarded. Building through 3,163 this way discovers the same 447 generators / 78 groups with **18,635 bounded-word gcds** and no parallel LCM state.

## Hyperbolic rough-cofactor fusion

Every composite has a unique least-factor decomposition

```math
n=q r,\qquad q=\operatorname{spf}(n),\qquad \gcd(r,\prod_{p<q}p)=1.
```

For each newly discovered `q`, the possible `r` live only in the hyperbolic interval `[ceil(A/q), floor(B/q)]`. Testing those cofactors against the already-built packed prefix wheel makes the decomposition disjoint before any candidate bitmap exists.

For 4,096 candidates it examines **7,562** cofactor points and uses **16,234 bounded-word gcds**. Exactly 3,593 points survive as composites across **271** least-factor classes. The independent packed first-hole scan adds 122 gcd probes and returns the complete summary **(503, 13)** without a block bitmap. The older floor-quotient implementation needs 1,716,105 sieve updates on this same block.

## Power-of-two radix reinterpretations

All rows below represent the same 4,096-candidate composite field and compile the finite winning lanes directly into an r-ary reduced DAG. Node identity alone is misleading, so child references and construction work are charged.

| radix | digits | reachable nodes | reachable child refs | allocated nodes | allocated child refs | OR calls |
|---:|---:|---:|---:|---:|---:|---:|
| 2 | 12 | 456 | 912 | 11939 | 23878 | 37919 |
| 4 | 6 | 241 | 964 | 6178 | 24712 | 40243 |
| 8 | 4 | 127 | 1016 | 3766 | 30128 | 44711 |
| 16 | 3 | 162 | 2592 | 3318 | 53088 | 95519 |
| 64 | 2 | 65 | 4160 | 2056 | 131584 | 214927 |

Radix 8 looks dramatically smaller if only node IDs are counted (127 vs 456), but binary still has the smallest reachable child-reference payload (912) and the fewest OR calls. Radix 64 collapses to 65 high-arity nodes while retaining 4,160 outgoing references. This is exactly the late-accounting failure mode the main project is designed to reject.

## Fibonacci / Zeckendorf coordinate

The 4,096 candidate indices require 17 Zeckendorf digits. The exact partial-domain decision DAG has **788 nodes / 1576 child refs**, versus **456 / 912** for ordinary binary. Factor divisibility also evolves with Pisano periods: across the 446 lanes the average Fibonacci period is **1728.7**, versus an average signed power-of-two folding order of **501.3** for base 2 and **298.3** for base 64. Fibonacci does not expose a smaller modular carrier here.

## Architectural conclusion

The prime analogue of the reverse-and-add pair machinery is not to retain candidate normalization carries. Those carries telescope out of every modular test. The stronger state is:

```text
previous prime / offset
    -> unnormalised pair-sum translation
    -> packed squarefree factor modulus (or bounded word groups)
    -> gcd zero-set
    -> least-factor/min envelope
    -> (count, first-hole) summary.
```

The new positive compression is the factor-set packing and finite least-factor quotient. The unresolved primitive is still first-hole/select over the coprime set without scanning candidates or unpacking the squarefree modulus. Different power-of-two and Fibonacci digit coordinates did not remove that projection barrier.

Also, for odd primes the exact successor relation is `p_next = p + 2j` for the first admissible `j>0`; `2p+1` is a different (Sophie-Germain/safe-prime) construction and is not generally the next prime.
