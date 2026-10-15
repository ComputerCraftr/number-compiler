"""Keep the production sparse B1 table on the compact endpoint owner."""

from collections.abc import Mapping

from devtools.checks import isabelle_syntax
from devtools.checks.isabelle_syntax import Session
from devtools.paths import repository_root

ROOT = repository_root()
BASE_THEORY = (
    ROOT
    / "proofs/isabelle/families/comma/comma_sparse_instance/Comma_Sparse_Base_Instance.thy"
)


def test_sparse_b1_retains_compact_authority_during_semantic_migration(
    repository_sessions: Mapping[str, Session],
) -> None:
    theory = BASE_THEORY.read_text(encoding="utf-8")

    name, imports = isabelle_syntax.parse_theory_header(theory, BASE_THEORY)
    assert name == "Comma_Sparse_Base_Instance"
    assert imports == (
        "Comma_Compact_B1.Comma_Compact_B1",
        "Comma_Semantic_B1.Comma_Semantic_B1_Columns",
    )
    # The semantic agreement theorem is not yet a replacement publisher.
    assert "Comma_Compact_Sparse_Base_Constructor.make lthy" in theory
    assert "comma_sparse_base_semantic_output_matches_template" in theory

    base_session = repository_sessions["Comma_Sparse_Base_Instance"]
    assert base_session.parent == "Comma_Compact_B1"
    assert base_session.theories == ("Comma_Sparse_Base_Instance",)
    assert not (
        ROOT
        / "proofs/isabelle/families/comma/comma_response_base/response_base_constructor.ML"
    ).exists()


def test_compact_sparse_rejection_cases_are_registered_for_isabelle_execution() -> None:
    theory = BASE_THEORY.read_text(encoding="utf-8")
    rejection_check = next(
        cartouche
        for cartouche in isabelle_syntax.ml_cartouches(theory)
        if "fun rejected" in cartouche and "List.app rejected" in cartouche
    )
    for rejected in (
        "zero_mask",
        "open_label",
        "open_numeral",
        "nonliteral",
        "live_outside",
        "fork_zero",
        "fork_one",
        "fork_ten",
        "oversized_mask",
        "root_one_equation",
    ):
        assert rejected in rejection_check
