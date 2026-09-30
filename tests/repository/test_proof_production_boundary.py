"""Exact row/cut/output-tape reference implementations are never production imports."""

import os
import subprocess
import sys
import textwrap
from typing import cast

import pytest

from devtools.checks.proof_boundary_audit import (
    EXPLICIT_PROOF_BOUNDARIES,
    production_proof_import_violations,
    proof_import_violations,
)
from devtools.paths import repository_root

ROOT = repository_root()


def test_all_production_modules_exclude_exact_oracle_dependencies() -> None:
    assert production_proof_import_violations(ROOT / "src/number_compiler") == ()
    for module in (
        "reverse_spacetime",
        "temporal_quotient",
        "reverse_action",
        "forcing_morphism",
    ):
        assert not (ROOT / "src/number_compiler" / f"{module}.py").exists()


def test_production_has_no_compatibility_proof_exemptions() -> None:
    assert EXPLICIT_PROOF_BOUNDARIES == frozenset()


@pytest.mark.parametrize(
    "source",
    (
        "from .proof.reverse_spacetime import ReverseAddCarrySlab",
        "import proofs.isabelle",
        "importlib.import_module('proofs.isabelle')",
        "from number_compiler import proof",
        "import devtools.verification.temporal_quotient as cut",
        "def hidden():\n    from .proof import reverse_action",
        "importlib.import_module('devtools.verification.reverse_action')",
        "__import__('number_compiler.reverse_spacetime')",
    ),
)
def test_dependency_gate_rejects_local_alias_and_dynamic_oracle_imports(
    source: str,
) -> None:
    assert proof_import_violations(
        source, "number_compiler.sequences.reverse_add.power"
    )


@pytest.mark.validation  # Isolated public cold/warm workload through reverse N=64.
def test_package_import_and_cold_warm_queries_work_with_proof_imports_blocked() -> None:
    script = textwrap.dedent("""
        import importlib.abc
        import sys
        class ForbidProof(importlib.abc.MetaPathFinder):
            def find_spec(self, fullname, path=None, target=None):
                if fullname == "devtools.verification" or fullname.startswith("devtools.verification."):
                    raise AssertionError("production imported exact oracle: " + fullname)
                return None
        sys.meta_path.insert(0, ForbidProof())
        import number_compiler
        from number_compiler import ReverseAddPoweredTerm, PoweredCollatzTerm
        for generations in (0, 1, 20, 64):
            term = ReverseAddPoweredTerm(196, generations)
            scalar = 196
            for _ in range(generations):
                scalar += int(str(scalar)[::-1])
            expected = str(scalar)
            for _ in range(2):
                assert term.digit(0) == int(expected[-1])
                assert term.width() == len(expected)
            assert term.metrics().exact_endpoint_nodes == 0
        from number_compiler import CanonicalSequenceCompiler, ReverseAddSequenceSpec
        diagnostic = CanonicalSequenceCompiler().compile_diagnostic(ReverseAddSequenceSpec(196, 10, 24))
        assert diagnostic.live_rows_average is None
        assert diagnostic.live_rows_max is None
        assert diagnostic.carry_reset_max_bits == 0
        collatz = PoweredCollatzTerm(27, 16)
        assert collatz.digit(0) == collatz.digit(0)
        assert collatz.width() == collatz.width()
        assert not any(name == "devtools.verification" or name.startswith("devtools.verification.") for name in sys.modules)
        for name in ("ReverseAddCarrySlab", "ReverseAddCarryCutState", "ReverseAddForcingMorphismArena", "ReverseAddAffineActionArena", "CarryPortAction"):
            assert not hasattr(number_compiler, name), name
    """)
    env = dict(os.environ)
    result = subprocess.run(
        [sys.executable, "-c", script],
        cwd=ROOT,
        env=env,
        capture_output=True,
        text=True,
        timeout=120,
        check=False,
    )
    assert result.returncode == 0, result.stdout + result.stderr


def test_current_compiler_audit_uses_semantic_scoped_ids_and_lazy_outputs() -> None:
    from devtools.checks.lazy_compiler_audit import current_lazy_compiler_checks

    checks = current_lazy_compiler_checks()
    assert len(checks) == 4
    assert all(checks.values()), checks


def test_generic_admission_rejects_unadapted_proof_machine_handles() -> None:
    """A proof-state ID is never an executable generic kernel atom."""
    from devtools.experiments.reverse_add.field_action import ProofMachineStateID
    from number_compiler.arithmetic.contracts.block_effect import BlockEffect
    from number_compiler.arithmetic.contracts.kernel_admission import immutable_atom
    from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
    from number_compiler.hashlife.actions.lazy_compiler import UnsupportedInterfaceError

    proof_state = ProofMachineStateID(
        ArenaToken("proof-only-state"),
        "proof-machine-state",
        0,
    )
    with pytest.raises(UnsupportedInterfaceError, match="complete immutable"):
        immutable_atom(cast(BlockEffect, proof_state))
