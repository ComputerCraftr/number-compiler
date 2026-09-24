"""Build and validate the Isabelle proof inventory from authored sources."""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path

from devtools.checks.isabelle_syntax import (
    executable_text,
    first_documentation_scope,
    ml_cartouches,
    navigation_text,
    parse_sessions,
    parse_theory_header,
    unquoted_matches,
)
from devtools.paths import repository_root

ROOT = repository_root()
ISABELLE = ROOT / "devtools/proofs/isabelle"

# These links describe implementation or executable-reference counterparts.  An
# empty mapping is deliberate: a standalone mathematical theory must not be
# presented as a production refinement merely because it is registered.
COUNTERPARTS: dict[str, tuple[str, ...]] = {
    "Comma_Macro_Constructor": (
        "src/number_compiler/sequences/comma/boundary_quotient.py",
        "tests/sequences/comma/test_boundary_quotient.py",
    ),
    "Comma_Finite_Transition": (),
    "Comma_Finite_Period": (
        "src/number_compiler/sequences/comma/boundary_quotient.py",
    ),
    "Comma_Macro_Refinement": (),
    "Comma_Weighted_Macro": (),
    "Comma_Future_Safety": (),
    "Comma_Checked_Ranks": (),
    "Comma_Period_Guard": (
        "src/number_compiler/sequences/comma/arithmetic.py",
        "devtools/experiments/comma/macro_lifting.py",
    ),
    "Comma_Exact_Phase_Guard": (
        "src/number_compiler/sequences/comma/arithmetic.py",
        "devtools/experiments/comma/macro_lifting.py",
        "tests/sequences/comma/test_macro_lifting.py",
    ),
    "Comma_Child_Classification": (
        "src/number_compiler/sequences/comma/arithmetic.py",
        "src/number_compiler/sequences/comma/boundary_quotient.py",
        "tests/sequences/comma/test_boundary_quotient.py",
    ),
    "Comma_Affine_Ray": (
        "devtools/experiments/comma/macro_lifting.py",
        "tests/sequences/comma/test_macro_lifting.py",
    ),
    "Comma_Boundary_Quotient": (
        "src/number_compiler/sequences/comma/boundary_quotient.py",
        "devtools/experiments/comma/macro_lifting.py",
        "tests/sequences/comma/test_macro_lifting.py",
    ),
    "Comma_Child_Cylinder": (
        "src/number_compiler/sequences/comma/arithmetic.py",
        "tests/sequences/comma/test_comma_power.py",
    ),
    "Comma_Decimal_Parent": ("devtools/experiments/comma/forest_certificate.py",),
    "Comma_Root_Forest": (
        "devtools/experiments/comma/forest_certificate.py",
        "src/number_compiler/sequences/comma/certificates.py",
    ),
    "S_Arithmetic_Skew": (
        "src/number_compiler/arithmetic/fields/skew_transfer.py",
        "tests/arithmetic/fields/test_integer_cylinder_chart.py",
    ),
    "Dyadic_Source_Lift": (
        "src/number_compiler/hashlife/execution/dyadic_return_reuse.py",
        "src/number_compiler/hashlife/execution/dyadic_return_transport.py",
        "src/number_compiler/hashlife/execution/dyadic_return_observers.py",
        "tests/hashlife/execution/test_dyadic_effect_reuse.py",
        "tests/arithmetic/fields/test_integer_cylinder_chart.py",
    ),
    "Dyadic_Balanced_Worklist": (
        "src/number_compiler/hashlife/execution/dyadic_return_transport.py",
        "tests/hashlife/execution/test_balanced_proof_refinement.py",
    ),
    "Dyadic_Balanced_Arithmetic": (
        "src/number_compiler/hashlife/execution/dyadic_return_transport.py",
        "src/number_compiler/hashlife/execution/dyadic_return_reuse.py",
        "tests/hashlife/execution/test_balanced_proof_refinement.py",
    ),
    "Dyadic_Prefix_Summary": (
        "src/number_compiler/hashlife/execution/dyadic_return_transport.py",
        "tests/hashlife/execution/test_balanced_proof_refinement.py",
    ),
    "Dyadic_Support_Descent": (
        "src/number_compiler/hashlife/execution/dyadic_return_observers.py",
        "tests/hashlife/execution/test_balanced_proof_refinement.py",
    ),
    "Balanced_Dyadic_Families": (
        "src/number_compiler/sequences/collatz/physical_images.py",
        "src/number_compiler/sequences/antihydra/arithmetic_images.py",
        "src/number_compiler/sequences/antihydra/mahler_action.py",
        "tests/hashlife/execution/test_balanced_proof_refinement.py",
    ),
    "Collatz_Reduced_Precision": (
        "devtools/experiments/collatz/powered_boundary_germs.py",
        "tests/hashlife/execution/test_powered_boundary_germs.py",
    ),
    "Collatz_Parity_Shift_Germ": (
        "src/number_compiler/arithmetic/fields/two_adic.py",
        "src/number_compiler/sequences/collatz/parity.py",
        "tests/sequences/collatz/test_collatz_parity.py",
    ),
    "Dyadic_Parity_Inverse_Arithmetic": (
        "src/number_compiler/arithmetic/fields/two_adic.py",
        "tests/sequences/collatz/test_collatz_parity.py",
    ),
    "Reverse_Threshold_Cocycle": (
        "devtools/experiments/reverse_add/cocycle_carrier.py",
        "devtools/experiments/reverse_add/factored_power.py",
        "tests/sequences/reverse_add/test_cocycle_carrier.py",
    ),
    "Reverse_Boundary_Germ_Local": (
        "src/number_compiler/arithmetic/formula/decimal_pair_coordinates.py",
        "devtools/experiments/reverse_add/temporal_boundary_germ.py",
        "tests/validation/proofs/reverse_add/test_temporal_boundary_germ.py",
    ),
    "Mahler_Spatial_Carry_Pump": (
        "devtools/experiments/antihydra/spatial_carry.py",
        "devtools/experiments/antihydra/future_grammar.py",
        "tests/validation/proofs/test_mahler_spatial_carry.py",
        "tests/validation/proofs/test_mahler_f5_production_bridge.py",
    ),
    "Reverse_Centered_Future_Grammar": (
        "devtools/experiments/reverse_add/centered_future.py",
        "tests/validation/proofs/reverse_add/test_centered_future_grammar.py",
    ),
    "Reverse_Growth_Run_Admission": (
        "src/number_compiler/arithmetic/polynomials/frobenius_sector.py",
        "tests/validation/proofs/reverse_add/test_source_growth_admission.py",
    ),
    "Mahler_Reachable_Repetition": (
        "devtools/experiments/antihydra/future_grammar.py",
        "tests/validation/proofs/test_mahler_future_grammar.py",
    ),
    "Mahler_Source_Cylinder_Transport": (
        "devtools/experiments/antihydra/source_safety.py",
        "tests/validation/proofs/test_mahler_source_transport.py",
    ),
    "Mahler_Source_Event_Safety": (
        "devtools/experiments/antihydra/source_safety.py",
        "devtools/experiments/antihydra/source_observers.py",
        "tests/validation/proofs/test_mahler_source_observers.py",
    ),
    "Mahler_Joint_Quotient_Algebra": (
        "src/number_compiler/arithmetic/fields/branch_quotients.py",
        "tests/arithmetic/fields/test_branch_quotients.py",
        "tests/validation/proofs/test_mahler_source_observers.py",
    ),
    "Antihydra_Mahler_Associated_Action": (
        "src/number_compiler/sequences/antihydra/arithmetic_images.py",
        "src/number_compiler/sequences/antihydra/mahler_action.py",
        "tests/api/test_antihydra_mahler_action.py",
    ),
    "Collatz_Saturated_Threshold_Composition": (
        "src/number_compiler/arithmetic/fields/threshold_envelope.py",
        "src/number_compiler/sequences/collatz/saturated_future.py",
        "tests/arithmetic/fields/test_threshold_envelope.py",
    ),
    "Generated_Mahler_Safety": (
        "tests/validation/proofs/test_mahler_safety_cylinders.py",
    ),
    "Mahler_Safety_Ledger_Separation": (
        "tests/validation/proofs/test_mahler_safety_cylinders.py",
    ),
    "Cylinder_Radial_Event_Clock": (
        "devtools/experiments/reverse_add/radial_event_clock.py",
        "tests/validation/proofs/reverse_add/test_radial_event_clock.py",
    ),
    "Cylinder_Radial_Hypergeometric_Elimination": (),
    "Cylinder_Innovation_Transport": (
        "src/number_compiler/arithmetic/fields/symbolic_innovation.py",
        "src/number_compiler/arithmetic/fields/innovation_substitution.py",
        "tests/arithmetic/fields/test_innovation_pullback.py",
    ),
    "Cylinder_Live_Forcing_Reduction": (
        "src/number_compiler/arithmetic/fields/live_forcing.py",
        "tests/arithmetic/fields/test_live_forcing.py",
    ),
    "Cylinder_Forcing_Alphabet": (
        "src/number_compiler/arithmetic/carry/carry_monoid.py",
        "tests/arithmetic/fields/test_live_carry_projection.py",
    ),
    "Cylinder_Residue_Carry_SLP": (
        "src/number_compiler/arithmetic/automata/residue_carry_slp.py",
        "tests/arithmetic/automata/test_residue_carry_slp.py",
    ),
}


def _scope(text: str) -> str:
    return first_documentation_scope(text)


def _audited_theorems(text: str) -> tuple[str, ...]:
    names: list[str] = []
    clean = executable_text(text)
    for block in ml_cartouches(clean):
        block = re.sub(r'"(?:\\.|[^"\\])*"', '""', block)
        bindings = dict(
            re.findall(r"\bval\s+(\w+)\s*=\s*@\{thms?\s+(.*?)\}", block, re.DOTALL)
        )
        pattern = (
            r"\bval\s+_\s*=\s*if\s+null\s*\(\s*Thm_Deps\.all_oracles\s+"
            r"(@\{thms?\s+.*?\}|[A-Za-z]\w*)\s*\)\s*then\s*\(\s*\)\s*else\s+error\b"
        )
        for argument in re.findall(pattern, block, re.DOTALL):
            direct = re.fullmatch(r"@\{thms?\s+(.*?)\}", argument, re.DOTALL)
            body = direct.group(1) if direct is not None else bindings.get(argument, "")
            names.extend(re.findall(r"[A-Za-z][A-Za-z0-9_'.]*", body))
    return tuple(dict.fromkeys(names))


def _declarations(text: str) -> tuple[dict[str, object], ...]:
    """Lexical navigation inventory; Isabelle remains the authority on statements."""
    text = navigation_text(text)
    starts = unquoted_matches(
        re.compile(r"(?m)^(lemma|theorem|corollary)\s+([A-Za-z][A-Za-z0-9_']*)"),
        text,
    )
    rows: list[dict[str, object]] = []
    for index, match in enumerate(starts):
        end = starts[index + 1].start() if index + 1 < len(starts) else len(text)
        body = text[match.end() : end]
        proofs = unquoted_matches(re.compile(r"(?m)(?:^|\s)(?:by|proof)\s"), body)
        proof = proofs[0] if proofs else None
        statement = (
            body[: proof.start()] if proof is not None else body.split("\n\n", 1)[0]
        )
        rows.append(
            {
                "name": match.group(2),
                "line": text.count("\n", 0, match.start()) + 1,
                "statement_and_assumptions": statement.strip(),
            }
        )
    return tuple(rows)


def build_index() -> dict[str, object]:
    sessions = parse_sessions((ISABELLE / "ROOT").read_text())
    declared: dict[str, tuple[Path, tuple[str, ...], str, tuple[str, ...]]] = {}
    for path in sorted(ISABELLE.rglob("*.thy")):
        text = path.read_text()
        name, imports = parse_theory_header(text, path)
        if name in declared:
            raise ValueError(f"duplicate theory declaration: {name}")
        declared[name] = (path, imports, _scope(text), _audited_theorems(text))

    registered: dict[str, str] = {}
    for session in sessions:
        for name in session.theories:
            if name in registered:
                raise ValueError(
                    f"theory {name} registered in {registered[name]} and {session.name}"
                )
            path = ISABELLE / session.directory / f"{name}.thy"
            if not path.is_file():
                raise ValueError(f"{session.name}: missing registered theory {path}")
            registered[name] = session.name

    reverse: dict[str, list[str]] = {name: [] for name in declared}
    for source, (_, imports, _, _) in declared.items():
        for imported in imports:
            target = Path(imported.split(".")[-1]).name
            if target in reverse:
                reverse[target].append(source)

    reachable = set(registered)
    pending = list(registered)
    while pending:
        source = pending.pop()
        for imported in declared[source][1]:
            target = Path(imported.split(".")[-1]).name
            if target in declared and target not in reachable:
                reachable.add(target)
                pending.append(target)

    unreachable = sorted(set(declared) - reachable)
    if unreachable:
        raise ValueError(f"unregistered and unreachable theories: {unreachable}")
    missing_audits = sorted(name for name in registered if not declared[name][3])
    if missing_audits:
        raise ValueError(
            f"registered theories without an oracle audit: {missing_audits}"
        )
    for theory, paths in COUNTERPARTS.items():
        if theory not in declared:
            raise ValueError(f"counterpart mapping names unknown theory {theory}")
        missing = [path for path in paths if not (ROOT / path).is_file()]
        if missing:
            raise ValueError(f"{theory}: missing mapped counterparts {missing}")

    entries = []
    source_texts = {name: row[0].read_text() for name, row in declared.items()}
    token_uses: dict[str, set[str]] = {}
    for theory, contents in source_texts.items():
        contents = executable_text(contents)
        for token in set(re.findall(r"[A-Za-z][A-Za-z0-9_']*", contents)):
            token_uses.setdefault(token, set()).add(theory)
    for name in sorted(declared):
        path, imports, scope, audit = declared[name]
        text = source_texts[name]
        declarations = _declarations(text)
        uses = {}
        for declaration in declarations:
            theorem = str(declaration["name"])
            uses[theorem] = tuple(sorted(token_uses.get(theorem, set()) - {name}))
        entries.append(
            {
                "theory": name,
                "path": path.relative_to(ROOT).as_posix(),
                "session": registered.get(name),
                "imports": imports,
                "imported_by": sorted(reverse[name]),
                "oracle_audit_theorems": audit,
                "scope": scope,
                "declarations": declarations,
                "lexical_uses_including_ML_and_attributes": uses,
                "verification_command": (
                    f"isabelle build -d devtools/proofs/isabelle {registered[name]}"
                    if name in registered
                    else "build an importing session"
                ),
                "counterparts": COUNTERPARTS.get(name, ()),
            }
        )
    return {
        "schema_version": 1,
        "root": "devtools/proofs/isabelle/ROOT",
        "sessions": [
            {
                "session": session.name,
                "directory": session.directory.as_posix(),
                "parent": session.parent,
                "dependencies": session.dependencies,
                "theories": session.theories,
            }
            for session in sessions
        ],
        "theories": entries,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--json",
        type=Path,
        help="write the complete generated index; validation always runs",
    )
    options = parser.parse_args()
    index = build_index()
    if options.json is not None:
        options.json.write_text(json.dumps(index, indent=2) + "\n")
    sessions = index["sessions"]
    theories = index["theories"]
    if not isinstance(sessions, list) or not isinstance(theories, list):
        raise TypeError("proof index collections have invalid types")
    print(
        json.dumps(
            {
                "status": "PASS",
                "sessions": len(sessions),
                "theories": len(theories),
                "output": None if options.json is None else str(options.json),
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
