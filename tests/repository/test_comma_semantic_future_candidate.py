"""Bounded checks for the untrusted semantic FutureCID certificate tooling."""

import base64
import json
import sys
from dataclasses import replace
from hashlib import sha256
from pathlib import Path
from typing import Literal

import pytest

from devtools.paths import isabelle_root, repository_root
from devtools.verification.comma_c1_audit import candidate_c1_return
from devtools.verification.comma_semantic_future_artifact import (
    canonical_candidate_bytes,
    decode_unsigned_varints,
    encode_unsigned_varints,
    runtime_candidate_bytes,
    runtime_candidate_record_from_m204_data,
    runtime_candidate_sha256,
    write_runtime_candidate_from_native_export,
)
from devtools.verification.comma_semantic_future_candidate import (
    Control,
    build_semantic_future_candidate,
    class_rank_candidate,
    reencode_candidate,
    refine_with_witnesses,
    validate_class_rows,
    write_new,
)
from devtools.verification.comma_semantic_future_candidate import (
    main as candidate_main,
)
from number_compiler.sequences.comma import future_provider
from number_compiler.sequences.comma.boundary_quotient import (
    BoundaryState,
    construct_completed_return,
    construct_macro,
)
from number_compiler.sequences.comma.future_provider_codec import SOURCE_COUNT
from number_compiler.sequences.comma.occurrence import (
    BoundaryOccurrence,
    OccurrencePrefixReturn,
)


def test_candidate_varint_map_round_trips_and_rejects_forged_values() -> None:
    ids = (0, 127, 128, 4715)
    packed = encode_unsigned_varints(ids, max_value=14783)
    assert decode_unsigned_varints(packed, max_values=4, max_value=14783) == ids

    with pytest.raises(ValueError):
        encode_unsigned_varints((True,), max_value=14783)
    with pytest.raises(ValueError):
        decode_unsigned_varints(b"\x80\x80\x00", max_values=1, max_value=14783)


def test_candidate_class_rows_reject_missing_or_unknown_ordered_slots() -> None:
    controls: tuple[Control, ...] = (("fork", 2), ("landmine", None))
    rows = ((0, 1), (None, None))
    assert validate_class_rows(controls, rows) == (controls, rows)

    for bad_controls, bad_rows in (
        (controls, ((None, 1), (None, None))),
        (controls, ((0,), (None, None))),
        ((("unknown", None),), ((None, None),)),
    ):
        with pytest.raises(ValueError):
            validate_class_rows(bad_controls, bad_rows)


def test_refinement_retains_control_and_rejects_child_order_collision() -> None:
    states = tuple(BoundaryState("N", 2, residue) for residue in range(4))
    controls: tuple[Control, ...] = (
        ("fork", 2),
        ("fork", 2),
        ("landmine", None),
        ("fork", 3),
    )
    rows = ((2, 3), (3, 2), (None, None), (0, 1))

    class_ids, collisions, _ = refine_with_witnesses(rows, controls, states)

    assert class_ids[0] != class_ids[1]
    witness = next(item for item in collisions if item.round_index == 0)
    assert witness.left_state in (states[0], states[1])
    assert witness.right_state in (states[0], states[1])
    assert witness.left_mapped_children != witness.right_mapped_children


def test_candidate_rank_check_has_unique_unranked_child_and_rejects_forged_row() -> (
    None
):
    controls: tuple[Control, ...] = (("fork", 2), ("landmine", None))
    rows = ((0, 1), (None, None))
    assert class_rank_candidate(controls, rows) == (None, 0)

    with pytest.raises(ValueError):
        class_rank_candidate((("fork", 2),), ((None, None),))


def test_future_terminal_keeps_width_beyond_b1_code_range() -> None:
    result = construct_completed_return(BoundaryState("Z", 3, 41))

    assert result.outcome == "fork"
    assert result.destination_a == 5
    assert result.exponent_delta == 27
    assert result.endpoint.evaluate(41) == 5 * 10**68 - 55
    assert result.ordered_children == (
        BoundaryState("N", 5, 68),
        BoundaryState("Z", 5, 68),
    )
    # B1's bounded terminal encoding is not the Future event authority.
    assert 9 * result.exponent_delta + result.destination_a - 2 == 246


@pytest.mark.parametrize("payload", [b"\x80", b"\x80\x00", b"\xff\x7f", b"\x00\x00"])
def test_candidate_decoder_rejects_truncation_aliases_and_excess(
    payload: bytes,
) -> None:
    with pytest.raises(ValueError):
        decode_unsigned_varints(payload, max_values=1, max_value=14783)


def test_candidate_artifact_write_preserves_existing_evidence(tmp_path: Path) -> None:
    artifact = tmp_path / "candidate.json"
    write_new(artifact, "original")
    with pytest.raises(FileExistsError):
        write_new(artifact, "replacement")
    assert artifact.read_text(encoding="utf-8") == "original"


def test_runtime_candidate_bytes_use_the_consumer_digest_contract() -> None:
    record = {
        "format": "comma-semantic-future-candidate-v1",
        "authority": "untrusted-source-derived-candidate",
        "state_universe": future_provider.FUTURE_SOURCE_UNIVERSE,
        "class_of_state_varint_base64": base64.b64encode(bytes(SOURCE_COUNT)).decode(
            "ascii"
        ),
        "controls": [["landmine", None]],
        "ordered_children": [[None, None]],
        "class_rank_candidate": [0],
        "refinement_rounds": 0,
        "refinement_collision_witnesses": [],
        "seam_is_projected_from_cid": True,
        "seam_projection_collision": None,
    }
    payload = runtime_candidate_bytes(record)
    decoded = json.loads(payload)
    assert set(decoded) == {
        "format",
        "authority",
        "state_universe",
        "source_radices",
        "source_roots",
        "source_nodes",
        "controls",
        "ordered_children",
        "class_rank_candidate",
    }
    assert decoded["format"] == future_provider.FUTURE_CANDIDATE_FORMAT
    assert decoded["authority"] == "untrusted-source-derived-candidate"
    assert runtime_candidate_sha256(record) == sha256(payload).hexdigest()
    assert (
        future_provider.future_candidate_sha256(decoded) == sha256(payload).hexdigest()
    )
    with pytest.raises(ValueError, match="requires a v1"):
        runtime_candidate_bytes(
            {**record, "format": future_provider.FUTURE_CANDIDATE_FORMAT}
        )


@pytest.mark.validation
@pytest.mark.parametrize("kind", ["N", "Z"])
@pytest.mark.parametrize("a", [2, 5, 9])
@pytest.mark.parametrize("residue", [1, 5, 13, 923])
def test_candidate_c1_projection_matches_independent_fragment_accumulation(
    kind: Literal["N", "Z"], a: int, residue: int
) -> None:
    state = BoundaryState(kind, a, residue)
    exponent = residue if residue >= 5 else residue + 924
    macro = construct_macro(state, grouped_near=True)
    reference = OccurrencePrefixReturn(BoundaryOccurrence(state, exponent), macro)
    assert candidate_c1_return(state, macro, 10**exponent) == (
        reference.c1_count,
        reference.terminal_low_suffix,
    )
    foreign = BoundaryState(state.kind, 3 if a != 3 else 4, residue)
    with pytest.raises(ValueError, match="another source"):
        candidate_c1_return(foreign, macro, 10**exponent)
    unsealed = replace(macro)
    with pytest.raises(ValueError, match="component seal"):
        candidate_c1_return(state, unsealed, 10**exponent)
    with pytest.raises(ValueError, match="decimal domain"):
        candidate_c1_return(state, macro, 1)


@pytest.mark.validation
def test_full_candidate_m204_graph_matches_independent_source_rebuild(
    tmp_path: Path,
) -> None:
    """Compare every source and ordered edge without assuming matching CID numbers."""
    candidate = build_semantic_future_candidate()
    directory = (
        isabelle_root(repository_root())
        / "families/comma/comma_semantic_future_instance"
    )
    proposal = runtime_candidate_record_from_m204_data(
        (directory / "semantic_future_m204_candidate_data.ML").read_text(
            encoding="utf-8"
        ),
        (directory / "semantic_future_m204_graph_data.ML").read_text(encoding="utf-8"),
    )
    parsed = future_provider.parse_future_candidate(
        proposal, charge_work=lambda _amount: None
    )
    actual_ids = tuple(
        parsed.source_classes.lookup(state) for state in candidate.states
    )
    forward: dict[int, int] = {}
    reverse: dict[int, int] = {}
    for expected, actual in zip(candidate.class_ids, actual_ids, strict=True):
        assert forward.setdefault(expected, actual) == actual
        assert reverse.setdefault(actual, expected) == expected
    assert len(forward) == len(candidate.class_controls) == len(parsed.classes)
    for expected, actual in forward.items():
        row = parsed.classes[actual]
        assert (
            row.control.kind,
            row.control.fork_coefficient,
        ) == candidate.class_controls[expected]
        assert row.ordered_children == tuple(
            None if child is None else forward[child]
            for child in candidate.class_children[expected]
        )
        assert row.rank == candidate.class_ranks[expected]

    v1 = candidate.certificate_record()
    occurrence = candidate.occurrence_payload_record()
    raw = {
        "format": v1["format"],
        "states": [
            [state.kind, state.a, state.exponent_residue] for state in candidate.states
        ],
        "class_of_state": list(candidate.class_ids),
        "controls": v1["controls"],
        "ordered_children": v1["ordered_children"],
        "occurrence_payloads": occurrence["occurrence_payloads"],
        "refinement_rounds": v1["refinement_rounds"],
        "refinement_collision_witnesses": v1["refinement_collision_witnesses"],
        "seam_is_projected_from_cid": v1["seam_is_projected_from_cid"],
        "seam_projection_collision": v1["seam_projection_collision"],
    }
    raw_path = tmp_path / "raw.json"
    runtime_path = tmp_path / "runtime.json"
    occurrence_path = tmp_path / "occurrence.json"
    write_new(raw_path, json.dumps(raw, sort_keys=True, separators=(",", ":")))
    result = reencode_candidate(raw_path, runtime_path, occurrence_path)
    assert runtime_path.read_bytes() == candidate.runtime_candidate_bytes()
    assert result["candidate_sha256"] == candidate.runtime_candidate_sha256()
    assert json.loads(occurrence_path.read_text(encoding="utf-8")) == occurrence
    assert (
        not {
            "refinement_rounds",
            "refinement_collision_witnesses",
            "seam_is_projected_from_cid",
            "seam_projection_collision",
        }
        & proposal.keys()
    )


def test_runtime_candidate_exports_compact_m204_literals_without_rebuilding(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    directory = (
        isabelle_root(repository_root())
        / "families/comma/comma_semantic_future_instance"
    )
    source = directory / "semantic_future_m204_candidate_data.ML"
    graph = directory / "semantic_future_m204_graph_data.ML"
    source_text = source.read_text(encoding="utf-8")
    graph_text = graph.read_text(encoding="utf-8")
    monkeypatch.setattr(
        "devtools.verification.comma_semantic_future_candidate.build_semantic_future_candidate",
        _reject_candidate_rebuild,
    )
    record = runtime_candidate_record_from_m204_data(source_text, graph_text)
    assert future_provider.parse_future_candidate(
        record, charge_work=lambda _amount: None
    )
    output = tmp_path / "candidate-v3.json"
    monkeypatch.setattr(
        sys,
        "argv",
        [
            "candidate",
            "--output",
            str(output),
            "--from-m204-source",
            str(source),
            "--from-m204-graph",
            str(graph),
        ],
    )
    candidate_main()
    assert output.read_bytes() == canonical_candidate_bytes(record)
    with pytest.raises(ValueError):
        runtime_candidate_record_from_m204_data(
            source_text.replace("0 upto", "0 + 0 upto", 1), graph_text
        )


def _native_export_candidate_record() -> dict[str, object]:
    return {
        "format": future_provider.FUTURE_CANDIDATE_FORMAT,
        "authority": future_provider.FUTURE_CANDIDATE_AUTHORITY,
        "state_universe": future_provider.FUTURE_SOURCE_UNIVERSE,
        "source_radices": [3, 4, 7, 11],
        "source_nodes": [[0]],
        "source_roots": [0] * 16,
        "controls": [["landmine", None]],
        "ordered_children": [[None, None]],
        "class_rank_candidate": [0],
    }


def test_runtime_candidate_copies_canonical_native_export_bytes(
    tmp_path: Path,
) -> None:
    source = tmp_path / "native-export.json"
    output = tmp_path / "candidate.json"
    payload = canonical_candidate_bytes(_native_export_candidate_record())
    source.write_bytes(payload)

    result = write_runtime_candidate_from_native_export(source, output)

    assert output.read_bytes() == payload
    assert result["bytes"] == len(payload)
    assert result["sha256"] == sha256(payload).hexdigest()
    assert result["authority"] == future_provider.FUTURE_CANDIDATE_AUTHORITY


@pytest.mark.parametrize(
    ("payload", "message"),
    [
        (b'{"format":"first","format":"second"}', "duplicate"),
        (
            json.dumps(_native_export_candidate_record()).encode("ascii"),
            "canonical",
        ),
    ],
    ids=("duplicate-keys", "noncanonical-whitespace"),
)
def test_runtime_candidate_rejects_duplicate_or_noncanonical_native_export(
    tmp_path: Path, payload: bytes, message: str
) -> None:
    source = tmp_path / "native-export.json"
    output = tmp_path / "candidate.json"
    source.write_bytes(payload)

    with pytest.raises(ValueError, match=message):
        write_runtime_candidate_from_native_export(source, output)
    assert not output.exists()


def test_runtime_candidate_native_export_preserves_existing_output(
    tmp_path: Path,
) -> None:
    source = tmp_path / "native-export.json"
    output = tmp_path / "candidate.json"
    source.write_bytes(canonical_candidate_bytes(_native_export_candidate_record()))
    output.write_bytes(b"existing evidence")

    with pytest.raises(FileExistsError):
        write_runtime_candidate_from_native_export(source, output)
    assert output.read_bytes() == b"existing evidence"


def test_runtime_candidate_native_export_cli_rejects_combined_modes(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    output = tmp_path / "candidate.json"
    monkeypatch.setattr(
        sys,
        "argv",
        [
            "comma-semantic-future-candidate",
            "--output",
            str(output),
            "--from-native-export",
            str(tmp_path / "native-export.json"),
            "--from-m204-source",
            str(tmp_path / "candidate-data.ML"),
        ],
    )

    with pytest.raises(ValueError, match="cannot be combined"):
        candidate_main()
    assert not output.exists()


def _reject_candidate_rebuild() -> object:
    raise AssertionError("source export rebuilt arithmetic")
