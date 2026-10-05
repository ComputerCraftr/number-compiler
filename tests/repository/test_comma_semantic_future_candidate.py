"""Bounded checks for the untrusted semantic FutureCID certificate tooling."""

from pathlib import Path

import pytest

from devtools.checks.isabelle_source_analysis import extract_isabelle_declarations
from devtools.checks.isabelle_syntax import executable_text
from devtools.paths import isabelle_root, repository_root
from devtools.verification.comma_semantic_future_candidate import (
    Control,
    _class_rank_candidate,
    _decode_unsigned_varints,
    _encode_unsigned_varints,
    _refine_with_witnesses,
    _validate_class_rows,
    _write_new,
)
from number_compiler.sequences.comma.boundary_quotient import BoundaryState


def test_candidate_varint_map_round_trips_and_rejects_forged_values() -> None:
    ids = (0, 127, 128, 4715)
    packed = _encode_unsigned_varints(ids, max_value=14783)
    assert _decode_unsigned_varints(packed, max_values=4, max_value=14783) == ids

    with pytest.raises(ValueError):
        _encode_unsigned_varints((True,), max_value=14783)
    with pytest.raises(ValueError):
        _decode_unsigned_varints(b"\x80\x80\x00", max_values=1, max_value=14783)


def test_candidate_class_rows_reject_missing_or_unknown_ordered_slots() -> None:
    controls: tuple[Control, ...] = (("fork", 2), ("landmine", None))
    rows = ((0, 1), (None, None))
    assert _validate_class_rows(controls, rows) == (controls, rows)

    for bad_controls, bad_rows in (
        (controls, ((None, 1), (None, None))),
        (controls, ((0,), (None, None))),
        ((("unknown", None),), ((None, None),)),
    ):
        with pytest.raises(ValueError):
            _validate_class_rows(bad_controls, bad_rows)


def test_refinement_retains_control_and_rejects_child_order_collision() -> None:
    states = tuple(BoundaryState("N", 2, residue) for residue in range(4))
    controls: tuple[Control, ...] = (
        ("fork", 2),
        ("fork", 2),
        ("landmine", None),
        ("fork", 3),
    )
    rows = ((2, 3), (3, 2), (None, None), (0, 1))

    class_ids, collisions, _ = _refine_with_witnesses(rows, controls, states)

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
    assert _class_rank_candidate(controls, rows) == (None, 0)

    with pytest.raises(ValueError):
        _class_rank_candidate((("fork", 2),), ((None, None),))


@pytest.mark.parametrize("payload", [b"\x80", b"\x80\x00", b"\xff\x7f", b"\x00\x00"])
def test_candidate_decoder_rejects_truncation_aliases_and_excess(
    payload: bytes,
) -> None:
    with pytest.raises(ValueError):
        _decode_unsigned_varints(payload, max_values=1, max_value=14783)


def test_candidate_artifact_write_preserves_existing_evidence(tmp_path: Path) -> None:
    artifact = tmp_path / "candidate.json"
    _write_new(artifact, "original")
    with pytest.raises(FileExistsError):
        _write_new(artifact, "replacement")
    assert artifact.read_text(encoding="utf-8") == "original"


def test_compact_template_publication_preserves_shared_nodes_until_demand() -> None:
    root = isabelle_root(repository_root()) / "comma_semantic_b1_instance"
    publication = executable_text(
        (root / "semantic_b1_occurrence_publication.ML").read_text(encoding="utf-8")
    )
    assert "Bound (depth - index - 1)" in publication
    assert "Term.is_open columns_term" in publication
    assert "Term.lambda" not in publication
    assert "expanded_weights" in publication
    # These are source-policy checks; kernel builds exercise the serializer.
    # Diagnostics must not traverse the compressed graph unless requested.
    metrics_start = publication.index("val row_metrics =")
    metrics_guard = publication.index(
        'if getenv "COMMA_PROFILE_LOG" = "" then NONE', metrics_start
    )
    assert metrics_guard < publication.index("val expanded_weights", metrics_start)
    assert metrics_guard < publication.index("Term.size_of_term columns_term")
    assert "val metrics = if not profile then NONE else" in publication
    assert "Candidate.Terminal_Ref (slot, parent)" in publication
    assert "Candidate.Goto_Ref (slot, child, lift_cid)" in publication
    assert "optional_nat parent" not in publication
    assert 'define_data "comma_semantic_b1_crt_lift_refs"' in publication
    assert 'define_data "comma_semantic_b1_crt_lift_descriptors"' in publication
    assert "slot_child_indices" not in publication
    constructor = executable_text(
        (root / "semantic_b1_template_constructor.ML").read_text(encoding="utf-8")
    )
    assert "column_term_mdd" not in constructor
    assert "Pending_Child" not in constructor
    assert "Pending_Goto" in constructor
    assert "lift_descriptors" in constructor
    fixture = (root / "Comma_Semantic_B1_Occurrence_Publication.thy").read_text(
        encoding="utf-8"
    )
    assert "Thm.consolidate [compact_correct, swapped_rejected]" in fixture
    assert fixture.index("swapped_rejected") < fixture.index("local_setup")


def test_compact_lift_contract_keeps_rebase_and_binding_authority() -> None:
    root = isabelle_root(repository_root())
    source = executable_text(
        (
            root / "comma_semantic_b1" / "Comma_Semantic_B1_CRT_Lift_Bindings.thy"
        ).read_text(encoding="utf-8")
    )
    assert "Comma_B1_Lift_Goto_Ref nat nat nat" in source
    local_cover = executable_text(
        (
            root / "comma_semantic_b1" / "Comma_Semantic_B1_CRT_Local_Cover.thy"
        ).read_text(encoding="utf-8")
    )
    assert "comma_semantic_b1_crt_occurrence_beta child_occurrence" in local_cover
    assert "zip lifted_columns child_beta" in local_cover
    assert "comma_semantic_b1_crt_occurrence_rebase child_occurrence" in source
    assert "comma_semantic_b1_crt_lift_descriptor_net_shift descriptor < 924" in source
    assert "[0..<924]" not in source
    assert "template_ids" not in source
    assert "distinct descriptors" not in source


def test_b1_reuses_only_checked_closed_equations_and_constructor_values() -> None:
    root = isabelle_root(repository_root()) / "comma_semantic_b1_instance"
    operation = (root / "semantic_b1_crt_operation_conversion.ML").read_text(
        encoding="utf-8"
    )
    validation = operation.split("fun validate request theorem", 1)[1].split(
        "fun complete_value", 1
    )[0]
    assert (
        "Comma_Selected_List_Conversion.make_cached_equation_validator ()" in operation
    )
    assert validation.index("validate_equation request theorem") < validation.index(
        "Termtab.defined (!completed_values) rhs"
    )
    assert "if reused_rhs then {complete = true, nodes = 0}" in validation
    assert "else check_value rhs" in validation
    assert "if not reused_rhs andalso #complete status" in validation

    fixture = operation.split("val fixture_checker = make ()", 1)[1].split(
        "in make () end", 1
    )[0]
    assert "fun make () =" in operation
    assert "first_request aconv second_request" in fixture
    assert "#reused_rhs second_checked" in fixture
    assert "#reused_closed second_checked" in fixture
    assert "#nodes (#status second_checked) = 0" in fixture
    assert "Exn.Exn (ERROR message)" in fixture
    assert "Exn.Exn failure => Exn.reraise failure" in fixture


def test_indexed_child_checks_preserve_source_authority_and_slot_shape() -> None:
    path = (
        isabelle_root(repository_root())
        / "comma_semantic_b1"
        / "Comma_Semantic_B1_CRT_Lift_Bindings.thy"
    )
    declarations = {
        item.name: item
        for item in extract_isabelle_declarations(
            path.read_text(encoding="utf-8"), path
        )
    }
    slot = declarations["comma_semantic_b1_crt_lift_slot_valid"].body
    assert "slot < length refs" in slot
    assert "child_index < length sources" in slot
    assert "sources ! child_index = comma_source_continuation_base child" in slot
    assert "occurrence_at child_index" in slot
    assert "comma_semantic_b1_crt_lift_descriptor_template_cid descriptor" in slot
    assert "ref_slot = slot" in slot
    assert "List.find" not in slot
    local_path = path.with_name("Comma_Semantic_B1_CRT_Local_Cover.thy")
    local_declarations = {
        item.name: item
        for item in extract_isabelle_declarations(local_path.read_text(), local_path)
    }
    local = local_declarations["comma_semantic_b1_crt_lift_local_cover_witness"].body
    assert "length refs = comma_decisive_sector_period source" in local
    assert "occurrence_binding_check parent" in local
    assert "occurrence_geometry" not in local
    assert "occurrence_wellformed" not in local
    assert {
        "comma_semantic_b1_crt_lift_slot_rejects_foreign_child",
        "comma_semantic_b1_crt_lift_slot_rejects_out_of_range_child",
        "comma_semantic_b1_crt_lift_slot_rejects_terminal_goto",
    } <= declarations.keys()
    assert (
        "comma_semantic_b1_crt_lift_local_cover_rejects_truncated_refs"
        in local_declarations
    )
    parent_column = local_declarations["comma_semantic_b1_crt_local_parent_column"].body
    assert "comma_semantic_b1_crt_find_result_index beta result" in parent_column
    assert "columns ! index" in parent_column
    assert "comma_semantic_b1_crt_occurrence_rebase parent" in parent_column
    assert "zip" not in parent_column
    assert "comma_crt_apply" not in parent_column
    cover = local_declarations["comma_semantic_b1_crt_local_piece_covered"].body
    assert "comma_crt_admitted 0 candidate" in cover
    assert "comma_crt_admitted 0 parent_column" in cover
    assert "comma_crt_negate parent_column" in cover
    assert "comma_crt_supported candidate" in cover
    local_slot = local_declarations["comma_semantic_b1_crt_lift_local_slot_valid"].body
    assert local_slot.index("lift_cid < length descriptors") < local_slot.index(
        "descriptors ! lift_cid"
    )
    assert "length lifted_columns = length child_beta" in local_slot


def test_local_cover_checker_reuses_exact_requests_without_repainting_parents() -> None:
    proof_root = isabelle_root(repository_root())
    root = proof_root / "comma_semantic_b1_instance"
    retired_refinement = (
        proof_root / "comma_semantic_b1" / "Comma_Semantic_B1_CRT_Lift_Refinement.thy"
    )
    assert not retired_refinement.exists()
    bindings = (
        retired_refinement.with_name("Comma_Semantic_B1_CRT_Lift_Bindings.thy")
    ).read_text()
    checker = executable_text(
        (root / "semantic_b1_occurrence_check_cache.ML").read_text(encoding="utf-8")
    )
    for retired in (
        "lift_source_split_action",
        "lift_slot_paint",
        "crt_lift_witness",
        "lift_descriptor_table_valid",
    ):
        assert retired not in checker
        assert retired not in bindings
    assert (
        "comma_semantic_b1_crt_lift_descriptor_valid templates descriptor" in bindings
    )
    assert "comma_semantic_b1_crt_lift_rejects_malformed_descriptor" in bindings
    publication = (root / "Comma_Semantic_B1_Occurrence_Publication.thy").read_text()
    assert "28 * length comma_semantic_b1_crt_sources" in publication
    assert "lift_descriptor_table_valid" not in publication
    for request in (
        "comma_semantic_b1_crt_local_piece_covered parent candidate result",
        "comma_semantic_b1_crt_local_parent_column parent result",
        "comma_semantic_b1_crt_find_result_index beta result",
    ):
        assert request in checker
    assert "comma_semantic_b1_crt_lift_local_cover_witness" in checker
    assert "comma_semantic_b1_crt_lift_local_slot_valid" in checker
    # B32 still consumes checked split actions; eliminating B1 reconstruction
    # must not remove this separate demanded conversion.
    assert "comma_crt_occurrence_split_action occurrence" in checker
