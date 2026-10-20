"""Delegated proof audits must execute exact theorem collections downstream."""

from pathlib import Path
from typing import cast

import pytest

from devtools.checks import isabelle_oracle_audit as oracle_audit
from devtools.checks import isabelle_proof_index as proof_index
from devtools.paths import isabelle_root


def test_dependency_name_queries_do_not_certify_release_endpoints() -> None:
    source = r"""
      ML \<open>
        val named = Comma_Proof_Dependency_Audit.checked_names
          (Proof_Context.theory_of @{context}) "query" @{thms candidate};
      \<close>
    """
    assert oracle_audit.audited_theorems(source) == ()


def _fixture(
    root: Path,
    monkeypatch: pytest.MonkeyPatch,
    *,
    sample_imports: str = "Helper",
    sample_audit: str | None = None,
    extra_theories: dict[str, str] | None = None,
    registered: tuple[str, ...] = ("Sample",),
) -> Path:
    proof_root = isabelle_root(root)
    directory = proof_root / "families" / "delegated"
    session_directory = directory / "Session"
    session_directory.mkdir(parents=True)
    (proof_root / "ROOTS").write_text("families/delegated\n")
    registered_text = "\n".join(f"    {name}" for name in registered)
    (directory / "ROOT").write_text(
        "session Delegated in Session = HOL +\n  theories\n" + registered_text + "\n"
    )
    (session_directory / "Helper.thy").write_text(
        "theory Helper imports Main begin\n"
        'lemma delegated: "True" by simp\n'
        "lemmas helper_oracle_audit_bundle = delegated\n"
        "end\n"
    )
    audit = sample_audit or (
        "ML \\<open>val _ = if null (Thm_Deps.all_oracles @{thms "
        'helper_oracle_audit_bundle bounded}) then () else error "oracle";\\<close>\n'
    )
    (session_directory / "Sample.thy").write_text(
        f"theory Sample imports {sample_imports} begin\n"
        'lemma bounded: "True" by simp\n' + audit + "end\n"
    )
    for name, text in (extra_theories or {}).items():
        (session_directory / f"{name}.thy").write_text(text)
    monkeypatch.setattr(proof_index, "ROOT", root)
    monkeypatch.setattr(proof_index, "ISABELLE", proof_root)
    return directory


def test_executed_bundle_is_expanded_and_delegated_owner_is_reported(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    _fixture(tmp_path, monkeypatch)

    result = proof_index.build_index()
    theory_rows = result["theories"]
    assert isinstance(theory_rows, list)
    theories: dict[str, dict[str, object]] = {}
    for item in cast(list[object], theory_rows):
        assert isinstance(item, dict)
        row: dict[str, object] = {}
        for key, value in cast(dict[object, object], item).items():
            assert isinstance(key, str)
            row[key] = value
        theory_name = row["theory"]
        assert isinstance(theory_name, str)
        theories[theory_name] = row

    assert theories["Helper"]["oracle_audit_theorems"] == ()
    assert theories["Helper"]["delegated_oracle_audit_bundles"] == (
        "helper_oracle_audit_bundle",
    )
    assert theories["Sample"]["oracle_audit_theorems"] == ("delegated", "bounded")


def test_unexecuted_bundle_does_not_satisfy_owner_audit(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    audit = (
        "ML \\<open>val hidden = @{thms helper_oracle_audit_bundle};\\<close>\n"
        "ML \\<open>val _ = if null (Thm_Deps.all_oracles @{thms bounded}) "
        'then () else error "oracle";\\<close>\n'
    )
    _fixture(tmp_path, monkeypatch, sample_audit=audit)

    with pytest.raises(
        ValueError, match="not executed in its owning registered session"
    ):
        proof_index.build_index()


def test_executed_bundle_requires_import_from_its_declaring_theory(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    importer = (
        "theory Importer imports Helper begin\n"
        'lemma imported: "True" by simp\n'
        "ML \\<open>val _ = if null (Thm_Deps.all_oracles @{thms "
        'helper_oracle_audit_bundle imported}) then () else error "oracle";\\<close>\n'
        "end\n"
    )
    _fixture(
        tmp_path,
        monkeypatch,
        sample_imports="Main",
        extra_theories={"Importer": importer},
        registered=("Sample", "Importer"),
    )

    with pytest.raises(ValueError, match="does not import its owner Helper"):
        proof_index.build_index()


def test_consumer_in_dependent_session_cannot_cover_owner_session(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    proof_root = isabelle_root(tmp_path)
    family = proof_root / "families" / "delegated"
    owner_dir = family / "Owner"
    consumer_dir = family / "Consumer"
    owner_dir.mkdir(parents=True)
    consumer_dir.mkdir(parents=True)
    (proof_root / "ROOTS").write_text("families/delegated\n")
    (family / "ROOT").write_text(
        "session Owner in Owner = HOL +\n"
        "  theories\n"
        "    Owner_Root\n"
        "session Consumer in Consumer = Owner +\n"
        "  theories\n"
        "    Downstream\n"
    )
    (owner_dir / "Helper.thy").write_text(
        "theory Helper imports Main begin\n"
        'lemma delegated: "True" by simp\n'
        "lemmas helper_oracle_audit_bundle = delegated\n"
        "end\n"
    )
    (owner_dir / "Owner_Root.thy").write_text(
        "theory Owner_Root imports Helper begin\nend\n"
    )
    (consumer_dir / "Downstream.thy").write_text(
        "theory Downstream imports Helper begin\n"
        'lemma local: "True" by simp\n'
        "ML \\<open>val _ = if null (Thm_Deps.all_oracles @{thms "
        'helper_oracle_audit_bundle local}) then () else error "oracle";\\<close>\n'
        "end\n"
    )
    monkeypatch.setattr(proof_index, "ROOT", tmp_path)
    monkeypatch.setattr(proof_index, "ISABELLE", proof_root)
    with pytest.raises(ValueError, match="not executed in its owning.*Owner"):
        proof_index.build_index()


def test_bundle_parser_ignores_documentation_and_rejects_malformed_members() -> None:
    source = (
        "theory Sample imports Main begin\n"
        "text \\<open>lemmas fake_oracle_audit_bundle = forged\\<close>\n"
        "lemmas real_oracle_audit_bundle = first second\n"
        "end\n"
    )
    assert oracle_audit.declared_oracle_audit_bundles(source) == (
        ("real_oracle_audit_bundle", ("first", "second")),
    )

    malformed = source.replace("first second", "first + second")
    with pytest.raises(ValueError, match="malformed oracle audit bundle member list"):
        oracle_audit.declared_oracle_audit_bundles(malformed)


@pytest.mark.parametrize(
    ("bundles", "theorems", "message"),
    [
        (
            {"a_oracle_audit_bundle": ("Owner", ("missing",))},
            {},
            "missing theorem",
        ),
        (
            {"a_oracle_audit_bundle": ("Owner", ("same",))},
            {"same": ("Owner", "Other")},
            "ambiguous theorem",
        ),
        (
            {"a_oracle_audit_bundle": ("Owner", ("foreign",))},
            {"foreign": ("Other",)},
            "foreign theorem",
        ),
        (
            {
                "a_oracle_audit_bundle": ("Owner", ("b_oracle_audit_bundle",)),
                "b_oracle_audit_bundle": ("Owner", ("a_oracle_audit_bundle",)),
            },
            {},
            "cyclic oracle audit bundle",
        ),
    ],
)
def test_bundle_claims_reject_missing_ambiguous_foreign_or_cyclic_names(
    bundles: dict[str, tuple[str, tuple[str, ...]]],
    theorems: dict[str, tuple[str, ...]],
    message: str,
) -> None:
    with pytest.raises(ValueError, match=message):
        oracle_audit.validate_bundle_members(bundles, theorems)


def test_audit_parser_expands_only_executed_bundle_references() -> None:
    source = (
        "theory Sample imports Main begin\n"
        "ML \\<open>val captured = @{thms delegated_oracle_audit_bundle};\\<close>\n"
        "ML \\<open>val _ = if null (Thm_Deps.all_oracles "
        "@{thms delegated_oracle_audit_bundle local}) then () "
        'else error "oracle";\\<close>\n'
        "end\n"
    )
    executed: set[str] = set()
    names = oracle_audit.audited_theorems(
        source,
        bundle_members={"delegated_oracle_audit_bundle": ("first", "second")},
        executed_bundles=executed,
    )
    assert names == ("first", "second", "local")
    assert executed == {"delegated_oracle_audit_bundle"}
