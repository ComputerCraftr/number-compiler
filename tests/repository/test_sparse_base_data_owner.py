"""The sparse B1 definition is the sole stored owner of its row payload."""

from devtools.paths import repository_root

ROOT = repository_root()
BASE_THEORY = (
    ROOT
    / "proofs/isabelle/families/comma/comma_sparse_instance/Comma_Sparse_Base_Instance.thy"
)
POWER_THEORY = (
    ROOT
    / "proofs/isabelle/families/comma/comma_sparse_power/Comma_Sparse_Power_Instance.thy"
)
POWER_SMOKE = (
    ROOT
    / "proofs/isabelle/families/comma/comma_sparse_audit/Comma_Sparse_Power_Smoke.thy"
)
POWER_CONSTRUCTOR = (
    ROOT
    / "proofs/isabelle/families/comma/comma_sparse_power_algebra/sparse_power_constructor.ML"
)


def test_sparse_b1_rows_have_one_proof_owned_data_source() -> None:
    base = BASE_THEORY.read_text(encoding="utf-8")
    power = POWER_THEORY.read_text(encoding="utf-8")

    assert base.count('Binding.name "comma_sparse_base_data"') == 1
    assert 'Binding.name "comma_sparse_base_data"' not in power
    assert "Comma_Sparse_Base_Data" not in base + power
    assert "Theory_Data" not in base + power
    assert "Thm.rhs_of definition" not in power
    assert "comma_sparse_base_data_def" in power


def test_power_publisher_extracts_and_rejects_untrusted_row_payloads() -> None:
    constructor = POWER_CONSTRUCTOR.read_text(encoding="utf-8")
    smoke = POWER_SMOKE.read_text(encoding="utf-8")

    assert "fun publish {base, definition} lthy" in constructor
    assert "Thm.term_of (Thm.rhs_of definition)" in constructor
    assert "HOLogic.dest_list raw_rhs" in constructor
    assert "fastype_of raw_rhs = HOLogic.listT wordT" in constructor
    assert "length terms <> 46" in constructor
    assert "fastype_of term <> wordT" in constructor
    assert 'check_rejected "a forged base owner"' in smoke
    assert 'check_rejected "a wrong-length table"' in smoke
    assert 'check_rejected "open row payloads"' in smoke
    assert 'check_rejected "an assumed definition"' in smoke
    assert "words=words" not in POWER_THEORY.read_text(encoding="utf-8") + smoke
