"""Shape and authority boundaries for untrusted symbolic frontier candidates."""

import pytest

from devtools.verification.comma_b1_quotient import B1State, observe_b1
from devtools.verification.comma_frontier_candidate import (
    CLASS_COUNT,
    ENDPOINTS,
    FrontierCandidate,
)


def _document(nodes: list[object], root: int) -> dict[str, object]:
    return {
        "rounds": 24,
        "bad_terminal_endpoints": [list(pair) for pair in ENDPOINTS],
        "one_step_nodes": nodes,
        "one_step_roots": [root] * CLASS_COUNT,
    }


def test_empty_frontier_input_does_not_authenticate_one_step() -> None:
    # An everywhere-stopping input trivially has an empty preimage. It still
    # contradicts the physical arithmetic, irrespective of claimed status.
    document = _document([[4, -1]], 0)
    document["kernel_accepted"] = True
    document["empty_preimage"] = True
    candidate = FrontierCandidate.from_document(document)
    source = B1State(0, 1)
    assert observe_b1(source).successor is not None
    assert candidate.target(source) is None


def test_phase_coordinates_use_document_order_not_old_crt_order() -> None:
    candidate = FrontierCandidate.from_document(
        _document([[4, -1], [4, 12], [0, [0, 1, 0]]], 2)
    )
    assert [candidate.target(B1State(0, p)) for p in range(6)] == [
        None,
        12,
        None,
        None,
        12,
        None,
    ]


def test_skipped_axes_keep_eleven_and_seven_coordinates_distinct() -> None:
    candidate = FrontierCandidate.from_document(
        _document(
            [
                [4, -1],
                [4, 5],
                [3, [0, 0, 1, 0, 0, 0, 0]],
                [2, [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0]],
            ],
            3,
        )
    )
    assert candidate.target(B1State(0, 37)) == 5
    assert candidate.target(B1State(0, 114)) == 5
    assert candidate.target(B1State(0, 4)) is None
    assert candidate.target(B1State(0, 2)) is None


@pytest.mark.parametrize(
    "nodes,root",
    [
        ([[True, -1]], 0),
        ([[4, True]], 0),
        ([[4, 46]], 0),
        ([[4, -2]], 0),
        ([[4, -1], [0, [0, 1, 0]]], 1),
        ([[4, -1], [4, 1], [0, [0, True, 0]]], 2),
        ([[4, -1], [4, 1], [0, [0, 1]]], 2),
        ([[4, -1], [0, [0, 0, 0]]], 1),
        ([[4, -1], [4, -1]], 0),
        ([[4, -1], [4, 1]], 0),
        ([[4, -1], [4, 1], [0, [0, 1, 0]], [1, [2, 1, 2, 1]]], 3),
        ([[4, -1]], -1),
        ([[4, -1]], 1),
    ],
)
def test_malformed_diagrams_fail_before_evaluation(
    nodes: list[object], root: int
) -> None:
    with pytest.raises((ValueError, TypeError)):
        FrontierCandidate.from_document(_document(nodes, root))


@pytest.mark.parametrize("field", ["rounds", "one_step_roots"])
def test_boolean_scope_values_are_not_integer_authority(field: str) -> None:
    document = _document([[4, -1]], 0)
    document[field] = True if field == "rounds" else [False] * CLASS_COUNT
    with pytest.raises(TypeError):
        FrontierCandidate.from_document(document)


def test_endpoint_obligation_cannot_be_replaced_by_claimed_success() -> None:
    document = _document([[4, -1]], 0)
    document["bad_terminal_endpoints"] = []
    document["empty_preimage"] = True
    with pytest.raises(ValueError, match="endpoint"):
        FrontierCandidate.from_document(document)


def test_endpoint_set_order_is_not_a_semantic_identity() -> None:
    document = _document([[4, -1]], 0)
    document["bad_terminal_endpoints"] = [list(pair) for pair in reversed(ENDPOINTS)]
    assert FrontierCandidate.from_document(document).target(B1State(0, 0)) is None


def test_duplicate_endpoints_cannot_replace_a_missing_endpoint() -> None:
    document = _document([[4, -1]], 0)
    document["bad_terminal_endpoints"] = [list(ENDPOINTS[0])] * len(ENDPOINTS)
    with pytest.raises(ValueError, match="endpoint"):
        FrontierCandidate.from_document(document)


@pytest.mark.parametrize(
    "source", [B1State(True, 0), B1State(0, False), B1State(46, 0)]
)
def test_external_state_admission_rejects_aliases(source: B1State) -> None:
    candidate = FrontierCandidate.from_document(_document([[4, -1]], 0))
    with pytest.raises((ValueError, TypeError)):
        candidate.target(source)
