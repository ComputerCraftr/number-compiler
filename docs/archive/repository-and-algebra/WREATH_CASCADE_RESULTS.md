# Wreath / dependency-cascade powered-operator pass

This pass tests the next operator representation after the full-J guard cleanup.
It does **not** add semantic state.  `FormulaRoot(planes)` remains the only
production state; cascade relations are compiler/operator metadata and are
charged by the release audit.

## 1. Exact dependency-cascade relation IR

`src/reverse_add/cascade.py` adds two exact finite-relation representations:

- `DependencyCascadeArena`: hash-consed suffix dependency functions;
- `GroupedDependencyCascadeArena`: values sharing the same suffix action are
  grouped into exact selectors (explicit-list / dense-bitset / run-description
  cost is charged, so a large selector is not treated as O(1)).

`encode_boxes()` accepts Cartesian dependency boxes directly and never expands
their tuple product.  Tests round-trip the exact relation.

The full-J release audit now additionally counts:

- cascade sections;
- newly created dependency groups;
- selector description bits.

A symbolic backend that merely replaces a large formula DAG by a large wreath
or decision diagram therefore fails certification too.

## 2. Minimize before power

The previous universal bimachine probe powered an exact but unminimized one-step
operator.  Conservative output-preserving minimization gives:

```
                   left states    right states
one step (old)          86             12
one step minimized      50              6
T^2 from minimized T   690             91
T^2 minimized          688             91
```

The minimized one-step and T^2 operators pass randomized exact pair-half tests.
Materializing the defined T^2 output table is not the bottleneck (~1.16M defined
entries, about 3.7 s in this container); an accidental repeated reconstruction
of output signatures in the minimizer was fixed.

## 3. Dependency compression of powered contexts

For the original verified T^2 determinization, optimal coordinate order matters.
Grouped dependency cascades reduce the exact context relations substantially:

- left determinized subsets: 11,551 flat triples -> about 1,623 dependency groups
  in the best grouped ordering;
- right determinized subsets: 95,509 flat triples -> about 4,617 dependency groups
  in the best grouped ordering.

For a capped T^4 probe before the T1/T2 minimization, the first 1,000 left context
states represented 1,134,865 flat triple members.  The optimal grouped cascade
represented them with:

```
2,060 shared dependency nodes
3,801 dependency groups
234,100 charged selector/graph description bits
```

After minimizing T1 and T^2 first, direct grouped T^4 exploration improves the
left side further.  At the first 1,000 discovered left sections:

```
1,000 top-level sections
1,964 shared dependency nodes
3,307 dependency groups
73,197 charged description bits
88,912 represented context triples
```

The right section system is still substantially heavier at the same cap:

```
1,000 top-level sections
5,202 shared dependency nodes
35,117 dependency groups
7,308,646 charged description bits
685,315 represented context triples
```

Thus the flat Cartesian product was a real implementation regression, but it was
not the whole full-J blocker.  The right-context / nonlinear-output dependency
still develops many distinct top-level sections.

## 4. Spatial cascade checks

Two orbit-specialized alternatives were also checked:

1. applying the exact bimachine directly to a hash-consed pair-word SLP;
2. replacing the independent right automaton by a symmetric `BlockSummary`
   radix-tree cascade.

Both are exact and very fast for ordinary sequential iteration, but the current
pair word itself does not remain a small SLP/tree.  At n=4096 the encoded half
has length 858 and the SLP has 878 reachable nodes; the symmetric block tree is
likewise essentially width-sized.  These substrates remove per-digit *scans*
when sharing exists, but they do not create the missing temporal power law.

## 5. Release status

The cascade work changes the representation of the powered operator, not the
semantic state.  It confirms that a cascade/wreath-style dependency IR is a
better fit than flat bimachine determinization, and the release gate now knows
how to charge it.

However, **no exact full-state `J_0/J_1 : FormulaRoot -> FormulaRoot` backend is
installed yet.**  The remaining criterion is whether the number/description
size of distinct powered dependency sections can be made polylogarithmic under
`T, T^2, T^4, ...` after the known centered/binomial/radix action is factored.
The current T^4 probes have not established that.
