"""Canonical quotient behavior for research transducer graph helpers."""

from __future__ import annotations

from dataclasses import dataclass

from devtools.verification.transducer_graph import quotient_graph


@dataclass(frozen=True)
class Arc:
    inp: int
    out: int
    dest: int


def test_quotient_graph_deduplicates_identical_remapped_arcs() -> None:
    arcs, finals, initials = quotient_graph(
        part={0: 0, 1: 1},
        representatives={0: 0, 1: 1},
        remap={0: 0, 1: 1},
        arcs={0: (Arc(1, 2, 1), Arc(1, 2, 1))},
        finals={1: ()},
        initials=(0,),
        make_arc=Arc,
    )
    assert arcs[0] == (Arc(1, 2, 1),)
    assert finals == {1: ()}
    assert initials == (0,)


def test_quotient_graph_deduplicates_destinations_collapsed_by_partition() -> None:
    arcs, _finals, _initials = quotient_graph(
        part={0: 0, 1: 1, 2: 1},
        representatives={0: 0, 1: 1},
        remap={0: 0, 1: 3},
        arcs={0: (Arc(1, 2, 1), Arc(1, 2, 2))},
        finals={1: ()},
        initials=(0,),
        make_arc=Arc,
    )
    assert arcs[0] == (Arc(1, 2, 3),)
