"""Generate a source-derived candidate certificate for semantic FutureCID.

This is an audit/certificate producer, not a branch classifier.  It builds
the finite boundary graph from the shared chart arithmetic, retains exact
terminal control and ordered N/Z slots, and computes a stable Moore map.  The
Isabelle instance must check the emitted map against its semantic provider;
none of the Python output is proof authority.

Occurrence quantities (phase, exponent advance, affine weight, terminal
endpoint, C1 counts and widths) are returned alongside the map and never used
as CID identity.  C1 low-phase/borrow observations are reported separately so
the checked theory can either prove them as projections or preserve the
occurrence data needed to reconstruct them.
"""

from __future__ import annotations

import base64
import json
from collections.abc import Callable, Mapping, Sequence
from dataclasses import dataclass
from pathlib import Path
from typing import Literal, TypeVar, cast

import devtools.verification.comma_semantic_future_artifact as future_artifact
from devtools.verification.comma_c1_audit import (
    C1OccurrencePayload,
    C1SeamObservation,
    CompletedMacroReturnAudit,
    c1_payloads,
)
from number_compiler.arithmetic.contracts.input_validation import (
    string_keyed_mapping,
)
from number_compiler.arithmetic.functions.finite_observer import (
    canonical_partition,
    class_members,
    map_partition_row,
    partition_equivalent,
    partition_quotient_rows,
)
from number_compiler.sequences.comma.boundary_chart import PERIOD
from number_compiler.sequences.comma.boundary_quotient import (
    BoundaryState,
    CompletedMacroReturn,
    construct_completed_return,
)
from number_compiler.sequences.comma.boundary_return import (
    validate_completed_macro_return,
)

Control = tuple[Literal["fork", "landmine"], int | None]
RawRow = tuple[int | None, int | None]
ClassRow = tuple[int | None, int | None]
_HolItem = TypeVar("_HolItem")


@dataclass(frozen=True, slots=True)
class FutureRefinementCollision:
    """A pair rejected from one provisional CID by ordered child behavior."""

    round_index: int
    provisional_class: int
    left_state: BoundaryState
    right_state: BoundaryState
    left_mapped_children: ClassRow
    right_mapped_children: ClassRow


@dataclass(frozen=True, slots=True)
class SeamProjectionCollision:
    """Counterexample to deriving the sampled C1 seam from a candidate CID."""

    cid: int
    left_state: BoundaryState
    right_state: BoundaryState
    left_seam: C1SeamObservation | None
    right_seam: C1SeamObservation | None


@dataclass(frozen=True, slots=True)
class SemanticFutureCandidate:
    states: tuple[BoundaryState, ...]
    controls: tuple[Control, ...]
    class_ids: tuple[int, ...]
    class_controls: tuple[Control, ...]
    class_children: tuple[ClassRow, ...]
    class_ranks: tuple[int | None, ...]
    occurrence_payloads: tuple[C1OccurrencePayload, ...]
    refinement_collisions: tuple[FutureRefinementCollision, ...]
    seam_projection_collision: SeamProjectionCollision | None
    refinement_rounds: int

    @property
    def seam_is_projected_from_cid(self) -> bool:
        return self.seam_projection_collision is None

    def certificate_record(self) -> dict[str, object]:
        """Return a deterministic, JSON-ready untrusted checker input."""
        packed_ids = future_artifact.encode_unsigned_varints(
            self.class_ids, max_value=_candidate_universe_size() - 1
        )
        return {
            "format": "comma-semantic-future-candidate-v1",
            "authority": "untrusted-source-derived-candidate",
            "state_universe": "kind=N,Z; a=2..9; residue=0..923; nested-order",
            "controls": [list(control) for control in self.class_controls],
            "class_of_state_varint_base64": base64.b64encode(packed_ids).decode(
                "ascii"
            ),
            "ordered_children": [list(row) for row in self.class_children],
            "class_rank_candidate": list(self.class_ranks),
            "refinement_rounds": self.refinement_rounds,
            "refinement_collision_witnesses": [
                {
                    "round": witness.round_index,
                    "provisional_class": witness.provisional_class,
                    "left_state": _state_record(witness.left_state),
                    "right_state": _state_record(witness.right_state),
                    "left_ordered_children": list(witness.left_mapped_children),
                    "right_ordered_children": list(witness.right_mapped_children),
                }
                for witness in self.refinement_collisions
            ],
            "seam_is_projected_from_cid": self.seam_is_projected_from_cid,
            "seam_projection_collision": (
                None
                if self.seam_projection_collision is None
                else {
                    "cid": self.seam_projection_collision.cid,
                    "left_state": _state_record(
                        self.seam_projection_collision.left_state
                    ),
                    "right_state": _state_record(
                        self.seam_projection_collision.right_state
                    ),
                    "left_seam": _seam_record(self.seam_projection_collision.left_seam),
                    "right_seam": _seam_record(
                        self.seam_projection_collision.right_seam
                    ),
                }
            ),
        }

    def runtime_candidate_record(self) -> dict[str, object]:
        """Return v2 provider data from the same values rendered into HOL."""
        return future_artifact.runtime_candidate_record(self.certificate_record())

    def runtime_candidate_bytes(self) -> bytes:
        """Return the provider's canonical bytes; this grants no authority."""
        return future_artifact.runtime_candidate_bytes(self.certificate_record())

    def runtime_candidate_sha256(self) -> str:
        """Content address the exact canonical provider candidate bytes."""
        return future_artifact.runtime_candidate_sha256(self.certificate_record())

    def isabelle_candidate_data(self) -> str:
        """Render the HOL tables from this candidate's exact class values."""
        return render_candidate_data_theory(
            self.class_ids,
            self.class_controls,
            self.class_children,
            self.class_ranks,
        )

    def occurrence_payload_record(self) -> dict[str, object]:
        """Return the exact occurrence evidence, separate from CID/rank data."""
        return {
            "format": "comma-semantic-future-occurrence-payload-v1",
            "authority": "untrusted-source-derived-occurrence-audit",
            "state_universe": "kind=N,Z; a=2..9; residue=0..923; nested-order",
            "occurrence_payloads": [
                {
                    "represented_exponent": item.represented_exponent,
                    "exponent_delta": item.exponent_delta,
                    "macro_weight": list(item.macro_weight),
                    "terminal_endpoint": list(item.terminal_endpoint),
                    "n_count": item.n_count,
                    "z_count": item.z_count,
                    "borrow_innovation": item.borrow_innovation,
                    "seam": _seam_record(item.seam),
                }
                for item in self.occurrence_payloads
            ],
        }


def _state_record(state: BoundaryState) -> list[object]:
    return [state.kind, state.a, state.exponent_residue]


def _candidate_universe_size() -> int:
    return len(("N", "Z")) * len(range(2, 10)) * PERIOD


def decode_unsigned_varints(
    payload: bytes, *, max_values: int, max_value: int
) -> tuple[int, ...]:
    """Decode and canonicalize the compact CID binding stream."""
    if type(payload) is not bytes:
        raise TypeError("candidate CID binding must be bytes")
    if (
        type(max_values) is not int
        or max_values < 0
        or type(max_value) is not int
        or max_value < 0
    ):
        raise ValueError("candidate CID decoder bounds must be nonnegative")
    max_bytes = max(1, (max_value.bit_length() + 6) // 7)
    if len(payload) > max_values * max_bytes:
        raise ValueError("candidate CID payload exceeds its bounded shape")
    values: list[int] = []
    value = 0
    shift = 0
    current_bytes = 0
    for byte in payload:
        current_bytes += 1
        if current_bytes > max_bytes:
            raise ValueError("candidate CID varint exceeds its bounded width")
        value |= (byte & 0x7F) << shift
        if byte & 0x80:
            shift += 7
            continue
        if value > max_value:
            raise ValueError("candidate CID value leaves its declared universe")
        values.append(value)
        if len(values) > max_values:
            raise ValueError("candidate CID payload has too many values")
        value = 0
        shift = 0
        current_bytes = 0
    if current_bytes != 0:
        raise ValueError("truncated candidate CID varint")
    decoded = tuple(values)
    if future_artifact.encode_unsigned_varints(decoded, max_value=max_value) != payload:
        raise ValueError("candidate CID varints are not canonically encoded")
    return decoded


def _validate_class_map(
    class_ids: tuple[object, ...], class_count: int
) -> tuple[int, ...]:
    if type(class_count) is not int or class_count <= 0:
        raise ValueError("candidate class table must be nonempty")
    source_size = _candidate_universe_size()
    if len(class_ids) != source_size:
        raise ValueError("candidate map does not cover the declared source universe")
    if class_count > source_size:
        raise ValueError("candidate class table exceeds the source universe")
    normalized: list[int] = []
    for cid in class_ids:
        if type(cid) is not int or not 0 <= cid < class_count:
            raise ValueError("candidate map contains an out-of-range CID")
        normalized.append(cid)
    dense_ids = tuple(normalized)
    class_members(dense_ids, class_count)
    return dense_ids


def _as_class_row(row: tuple[int | None, ...]) -> ClassRow:
    if len(row) != 2:
        raise AssertionError("candidate transition row changed its ordered arity")
    return row[0], row[1]


def validate_class_rows(
    controls: tuple[object, ...], children: tuple[object, ...]
) -> tuple[tuple[Control, ...], tuple[ClassRow, ...]]:
    if not controls or len(controls) != len(children):
        raise ValueError("candidate class controls and edges have different shapes")
    class_count = len(controls)
    normalized_controls: list[Control] = []
    normalized_children: list[ClassRow] = []
    for control_value, row_value in zip(controls, children, strict=True):
        if not isinstance(control_value, (tuple, list)):
            raise ValueError("candidate control is malformed")
        control: Sequence[object] = cast(Sequence[object], control_value)
        if len(control) != 2:
            raise ValueError("candidate control is malformed")
        kind_value, coefficient_value = control
        if kind_value == "fork":
            if type(coefficient_value) is not int or not 2 <= coefficient_value <= 9:
                raise ValueError("candidate fork lost its exact coefficient")
            kind: Literal["fork", "landmine"] = "fork"
            coefficient: int | None = coefficient_value
        elif kind_value == "landmine" and coefficient_value is None:
            kind = "landmine"
            coefficient = None
        else:
            raise ValueError("candidate control is neither Fork a nor Landmine")
        if not isinstance(row_value, (tuple, list)):
            raise ValueError("candidate did not retain both ordered edge slots")
        row: Sequence[object] = cast(Sequence[object], row_value)
        if len(row) != 2:
            raise ValueError("candidate did not retain both ordered edge slots")
        mapped: list[int | None] = []
        for target in row:
            if target is None:
                mapped.append(None)
            elif type(target) is int and 0 <= target < class_count:
                mapped.append(target)
            else:
                raise ValueError("candidate child class leaves its quotient")
        if kind == "landmine" and mapped != [None, None]:
            raise ValueError("landmine candidate row has children")
        if kind == "fork" and any(target is None for target in mapped):
            raise ValueError("fork candidate lost an ordered child")
        normalized_controls.append((kind, coefficient))
        normalized_children.append((mapped[0], mapped[1]))
    return tuple(normalized_controls), tuple(normalized_children)


def write_new(path: Path, content: str) -> None:
    """Write new evidence or generated theory data without replacing prior work."""
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("x", encoding="utf-8", newline="\n") as target:
        target.write(content)


def _seam_record(seam: C1SeamObservation | None) -> list[int] | None:
    if seam is None:
        return None
    return [
        seam.n_terminal_suffix,
        seam.z_terminal_suffix,
        seam.source_borrow,
        seam.target_borrow,
    ]


def _state_index(states: tuple[BoundaryState, ...]) -> dict[BoundaryState, int]:
    result = {state: index for index, state in enumerate(states)}
    if len(result) != len(states):
        raise AssertionError("boundary source enumeration contains duplicate states")
    return result


def _control(macro: CompletedMacroReturn) -> Control:
    if macro.outcome == "landmine":
        if macro.destination_a is not None or macro.ordered_children:
            raise AssertionError("landmine source row carries fork payload")
        return ("landmine", None)
    if macro.outcome != "fork" or macro.destination_a is None:
        raise AssertionError("boundary source row has no exact terminal control")
    if tuple(child.kind for child in macro.ordered_children) != ("N", "Z"):
        raise AssertionError("fork source row lost ordered N/Z children")
    if any(child.a != macro.destination_a for child in macro.ordered_children):
        raise AssertionError("fork control disagrees with its child constructors")
    return ("fork", macro.destination_a)


def _completed_macro_return(
    macro: CompletedMacroReturn,
) -> CompletedMacroReturnAudit:
    """Validate one sealed producer return and project its exact C1 header."""
    validate_completed_macro_return(macro)
    control = _control(macro)
    return CompletedMacroReturnAudit(
        macro.source,
        macro.exponent_delta,
        macro.weight,
        macro.endpoint,
        macro.ordered_children,
        control,
    )


def _rows(
    macros: tuple[CompletedMacroReturnAudit, ...],
    indices: dict[BoundaryState, int],
) -> tuple[RawRow, ...]:
    result: list[RawRow] = []
    for macro in macros:
        if not macro.ordered_children:
            result.append((None, None))
            continue
        if len(macro.ordered_children) != 2:
            raise AssertionError("source macro has an unexpected child arity")
        try:
            result.append(
                (
                    indices[macro.ordered_children[0]],
                    indices[macro.ordered_children[1]],
                )
            )
        except KeyError as exc:
            raise AssertionError(
                "source child left the declared boundary universe"
            ) from exc
    return tuple(result)


def refine_with_witnesses(
    rows: tuple[RawRow, ...],
    controls: tuple[Control, ...],
    states: tuple[BoundaryState, ...],
) -> tuple[tuple[int, ...], tuple[FutureRefinementCollision, ...], int]:
    """Refine exact-control blocks by mapped ordered children to a fixed point."""
    classes = canonical_partition(
        tuple(
            (control, tuple(target is not None for target in row))
            for control, row in zip(controls, rows, strict=True)
        )
    )
    witnesses: list[FutureRefinementCollision] = []
    round_index = 0
    while True:
        mapped = tuple(_as_class_row(map_partition_row(row, classes)) for row in rows)
        signatures = tuple(
            (classes[index], mapped[index]) for index in range(len(states))
        )
        refined = canonical_partition(signatures)
        old_groups = class_members(classes, max(classes, default=-1) + 1)
        for old_class, group in enumerate(old_groups):
            representative = group[0]
            for index in group[1:]:
                if mapped[representative] != mapped[index]:
                    witnesses.append(
                        FutureRefinementCollision(
                            round_index,
                            old_class,
                            states[representative],
                            states[index],
                            mapped[representative],
                            mapped[index],
                        )
                    )
                    # One auditable witness per split provisional class and
                    # refinement round is enough; remaining members are
                    # already covered by the exact signature comparison.
                    break
        round_index += 1
        if partition_equivalent(classes, refined):
            return refined, tuple(witnesses), round_index
        classes = refined


def _quotient_rows(
    rows: tuple[RawRow, ...],
    controls: tuple[Control, ...],
    class_ids: tuple[int, ...],
) -> tuple[tuple[Control, ...], tuple[ClassRow, ...]]:
    classes = max(class_ids, default=-1) + 1
    members = class_members(class_ids, classes)
    quotient_rows = partition_quotient_rows(rows, class_ids, classes)
    outputs: list[Control] = []
    child_rows: list[ClassRow] = []
    for cid, group in enumerate(members):
        representative = group[0]
        control = controls[representative]
        children = quotient_rows[cid]
        for index in group[1:]:
            if controls[index] != control:
                raise AssertionError("candidate CID merged distinct terminal controls")
        if len(children) != 2:
            raise AssertionError("candidate CID did not preserve both ordered slots")
        outputs.append(control)
        child_rows.append((children[0], children[1]))
    return tuple(outputs), tuple(child_rows)


def class_rank_candidate(
    controls: tuple[Control, ...], children: tuple[ClassRow, ...]
) -> tuple[int | None, ...]:
    """Derive and locally check least finite losing ranks on candidate CIDs."""
    controls, children = validate_class_rows(controls, children)
    if len(controls) != len(children):
        raise AssertionError("candidate controls and child rows have different sizes")
    ranks: list[int | None] = [0 if row == (None, None) else None for row in children]
    while True:
        newly: dict[int, int] = {}
        for cid, (control, row) in enumerate(zip(controls, children, strict=True)):
            if ranks[cid] is not None:
                continue
            if control[0] == "landmine":
                if row != (None, None):
                    raise AssertionError("candidate landmine has ordered children")
                newly[cid] = 0
                continue
            if control[0] != "fork" or None in row:
                raise AssertionError("candidate fork lost one of its ordered children")
            child_ranks = tuple(ranks[target] for target in row if target is not None)
            if len(child_ranks) == 2 and all(rank is not None for rank in child_ranks):
                known = tuple(rank for rank in child_ranks if rank is not None)
                newly[cid] = 1 + max(known)
        if not newly:
            break
        for cid, new_rank in newly.items():
            ranks[cid] = new_rank

    for cid, (control, row) in enumerate(zip(controls, children, strict=True)):
        rank = ranks[cid]
        if control[0] == "landmine":
            if rank is None or row != (None, None):
                raise AssertionError("candidate rank checker rejected a landmine row")
            continue
        child_ranks = tuple(ranks[target] for target in row if target is not None)
        if rank is None:
            if sum(child_rank is None for child_rank in child_ranks) != 1:
                raise AssertionError(
                    f"candidate CID {cid} has no unique unranked ordered child"
                )
        elif any(
            child_rank is None or child_rank >= rank for child_rank in child_ranks
        ):
            raise AssertionError(f"candidate CID {cid} violates strict rank descent")
    return tuple(ranks)


def reencode_candidate(
    input_path: Path,
    candidate_path: Path,
    occurrence_path: Path,
    isabelle_data_path: Path | None = None,
    checked_isabelle_data_path: Path | None = None,
) -> dict[str, object]:
    """Validate dimensions and compact a prior raw candidate without rebuilding it."""
    raw_source: object = json.loads(input_path.read_text(encoding="utf-8"))
    source_mapping = string_keyed_mapping(raw_source)
    if source_mapping is None:
        raise TypeError("candidate JSON root must be an object")
    source: dict[str, object] = dict(source_mapping)
    if source.get("format") != "comma-semantic-future-candidate-v1":
        raise ValueError("input is not a v1 semantic future candidate")

    def list_field(name: str) -> list[object]:
        value = source.get(name)
        if not isinstance(value, list):
            raise TypeError(f"candidate field {name!r} must be a list")
        return cast(list[object], value)

    states = list_field("states")
    class_ids = list_field("class_of_state")
    controls = list_field("controls")
    children = list_field("ordered_children")
    payloads = list_field("occurrence_payloads")
    refinement_witnesses = list_field("refinement_collision_witnesses")
    if len(states) != len(class_ids) or len(payloads) != len(states):
        raise ValueError("source map or occurrence payload has the wrong universe size")
    if len(states) != _candidate_universe_size():
        raise ValueError("candidate does not cover the declared source universe")
    if len(controls) != len(children):
        raise ValueError("class controls and ordered child rows have different sizes")
    expected_states = (
        [kind, a, residue]
        for kind in ("N", "Z")
        for a in range(2, 10)
        for residue in range(PERIOD)
    )
    if any(
        actual != expected
        for actual, expected in zip(states, expected_states, strict=True)
    ):
        raise ValueError("candidate source-state ordering is not canonical")
    class_count = len(controls)
    dense_ids = _validate_class_map(tuple(class_ids), class_count)
    max_cid = _candidate_universe_size() - 1
    packed_ids = future_artifact.encode_unsigned_varints(dense_ids, max_value=max_cid)
    if (
        decode_unsigned_varints(
            packed_ids, max_values=_candidate_universe_size(), max_value=max_cid
        )
        != dense_ids
    ):
        raise AssertionError("candidate CID binding failed its codec round trip")
    normalized_controls, normalized_children = validate_class_rows(
        tuple(controls), tuple(children)
    )
    rank_candidate = class_rank_candidate(normalized_controls, normalized_children)
    paths = [candidate_path.resolve(), occurrence_path.resolve()]
    if isabelle_data_path is not None:
        paths.append(isabelle_data_path.resolve())
    if len(set(paths)) != len(paths) or input_path.resolve() in paths:
        raise ValueError("candidate inputs and outputs must have distinct paths")
    if (
        checked_isabelle_data_path is not None
        and checked_isabelle_data_path.resolve() in paths
    ):
        raise ValueError("checked Isabelle data must be distinct from outputs")
    if any(path.exists() for path in paths):
        raise FileExistsError("candidate outputs must be new files")
    compact = future_artifact.runtime_candidate_record(
        {
            "format": "comma-semantic-future-candidate-v1",
            "authority": "untrusted-source-derived-candidate",
            "state_universe": "kind=N,Z; a=2..9; residue=0..923; nested-order",
            "class_of_state_varint_base64": base64.b64encode(packed_ids).decode(
                "ascii"
            ),
            "controls": [list(control) for control in normalized_controls],
            "ordered_children": [list(row) for row in normalized_children],
            "class_rank_candidate": list(rank_candidate),
            "refinement_rounds": source.get("refinement_rounds"),
            "refinement_collision_witnesses": refinement_witnesses,
            "seam_is_projected_from_cid": source.get("seam_is_projected_from_cid"),
            "seam_projection_collision": source.get("seam_projection_collision"),
        }
    )
    checked_runtime_sha256 = (
        None
        if checked_isabelle_data_path is None
        else verify_runtime_candidate_hol_data_binding(
            compact, checked_isabelle_data_path
        )
    )
    occurrence = {
        "format": "comma-semantic-future-occurrence-payload-v1",
        "authority": "untrusted-source-derived-occurrence-audit",
        "state_universe": compact["state_universe"],
        "occurrence_payloads": payloads,
    }
    write_new(
        candidate_path,
        future_artifact.canonical_candidate_bytes(compact).decode("ascii"),
    )
    write_new(
        occurrence_path,
        json.dumps(occurrence, sort_keys=True, separators=(",", ":")) + "\n",
    )
    if isabelle_data_path is not None:
        write_new(
            isabelle_data_path,
            render_candidate_data_theory(
                dense_ids,
                tuple(normalized_controls),
                tuple(normalized_children),
                rank_candidate,
            ),
        )
    candidate_bytes = candidate_path.stat().st_size
    occurrence_bytes = occurrence_path.stat().st_size
    isabelle_lines = (
        None
        if isabelle_data_path is None
        else len(isabelle_data_path.read_text(encoding="utf-8").splitlines())
    )
    return {
        "input": str(input_path),
        "candidate_output": str(candidate_path),
        "occurrence_output": str(occurrence_path),
        "isabelle_data_output": (
            None if isabelle_data_path is None else str(isabelle_data_path)
        ),
        "source_map_entries": len(dense_ids),
        "classes": class_count,
        "ranked_classes": sum(rank is not None for rank in rank_candidate),
        "class_rows": len(normalized_controls),
        "collision_witnesses": len(refinement_witnesses),
        "seam_projected_from_cid": source.get("seam_is_projected_from_cid"),
        "candidate_bytes": candidate_bytes,
        "candidate_sha256": future_artifact.canonical_candidate_sha256(compact),
        "checked_isabelle_data": (
            None
            if checked_isabelle_data_path is None
            else str(checked_isabelle_data_path)
        ),
        "checked_runtime_sha256": checked_runtime_sha256,
        "occurrence_bytes": occurrence_bytes,
        "isabelle_data_lines": isabelle_lines,
    }


def _hol_list_definition(
    name: str,
    hol_type: str,
    values: tuple[_HolItem, ...],
    render: Callable[[_HolItem], str],
) -> str:
    lines = [
        f'definition {name} :: "{hol_type}" where',
        f'  "{name} =',
        "    [",
    ]
    rendered = [render(value) for value in values]
    chunks = [rendered[index : index + 40] for index in range(0, len(rendered), 40)]
    for index, chunk in enumerate(chunks):
        suffix = "," if index + 1 < len(chunks) else ""
        lines.append("      " + ", ".join(chunk) + suffix)
    lines.append('    ]"')
    return "\n".join(lines)


def render_candidate_data_theory(
    class_ids: tuple[int, ...],
    controls: tuple[Control, ...],
    children: tuple[ClassRow, ...],
    ranks: tuple[int | None, ...],
) -> str:
    """Render reviewed compact candidate data, with no physical edge table."""
    if not (len(controls) == len(children) == len(ranks)):
        raise ValueError("candidate class data vectors have inconsistent lengths")

    def control_term(control: Control) -> str:
        if control[0] == "landmine":
            if control[1] is not None:
                raise ValueError("landmine candidate carries a fork coefficient")
            return "Comma_Future_Landmine"
        if type(control[1]) is not int:
            raise ValueError("fork candidate lost its exact coefficient")
        return f"Comma_Future_Fork {control[1]}"

    def child_term(value: int | None) -> str:
        return "None" if value is None else f"Some {value}"

    def child_pair_term(row: ClassRow) -> str:
        return f"({child_term(row[0])}, {child_term(row[1])})"

    def rank_term(value: int | None) -> str:
        return "None" if value is None else f"Some {value}"

    definitions = (
        _hol_list_definition(
            "comma_semantic_future_candidate_class_ids",
            "nat list",
            tuple(class_ids),
            str,
        ),
        _hol_list_definition(
            "comma_semantic_future_candidate_controls",
            "comma_future_control list",
            tuple(controls),
            control_term,
        ),
        _hol_list_definition(
            "comma_semantic_future_candidate_children",
            "(nat option \\<times> nat option) list",
            tuple(children),
            child_pair_term,
        ),
        _hol_list_definition(
            "comma_semantic_future_candidate_ranks",
            "nat option list",
            tuple(ranks),
            rank_term,
        ),
    )
    return (
        "theory Comma_Semantic_Future_Candidate_Data\n"
        "  imports Comma_Semantic_Graph_Instance.Comma_Semantic_Summary_Instance\n"
        "begin\n\n"
        "text \\<open>Untrusted, source-derived Moore candidate data.  The concrete\n"
        "semantic provider and the rank-row checker validate this map before\n"
        "any infinite-path theorem uses it.  The source-state binding is a CID\n"
        "map only; control, ordered child edges, and candidate ranks occur once\n"
        "per CID.  Occurrence weights and C1 payloads are stored separately.\n"
        "This theory contains no native rank table or source transition table.\n"
        "\\<close>\n\n" + "\n\n".join(definitions) + "\n\nend\n"
    )


def verify_runtime_candidate_hol_data_binding(
    record: Mapping[str, object], checked_data_path: Path
) -> str:
    """Validate and render a v2 candidate, then hash it only after HOL match.

    This is a development consistency check. It does not create kernel or
    runtime admission for the candidate.
    """
    from number_compiler.sequences.comma import future_provider

    def discard_validation_charge(_amount: int) -> None:
        return None

    bounded_record = future_provider.preflight_future_candidate(
        record, charge_work=discard_validation_charge
    )
    source_classes, parsed_classes = future_provider.validate_record(
        bounded_record, charge_work=discard_validation_charge
    )
    control_records: list[Control] = []
    for row in parsed_classes:
        if row.control.kind == "fork":
            control_kind: Literal["fork", "landmine"] = "fork"
        elif row.control.kind == "landmine":
            control_kind = "landmine"
        else:
            raise ValueError("validated candidate contains an unknown control kind")
        control_records.append((control_kind, row.control.fork_coefficient))
    controls = tuple(control_records)
    children = tuple(row.ordered_children for row in parsed_classes)
    ranks = tuple(row.rank for row in parsed_classes)
    generated_text = render_candidate_data_theory(
        source_classes, controls, children, ranks
    )
    return future_artifact.runtime_candidate_sha256_after_hol_match(
        bounded_record, generated_text, checked_data_path
    )


def _seam_collision(
    class_ids: tuple[int, ...],
    states: tuple[BoundaryState, ...],
    payloads: tuple[C1OccurrencePayload, ...],
) -> SeamProjectionCollision | None:
    representatives: dict[int, int] = {}
    for index, cid in enumerate(class_ids):
        first = representatives.setdefault(cid, index)
        if payloads[first].seam != payloads[index].seam:
            return SeamProjectionCollision(
                cid,
                states[first],
                states[index],
                payloads[first].seam,
                payloads[index].seam,
            )
    return None


def build_semantic_future_candidate() -> SemanticFutureCandidate:
    """Construct the exact-control Moore candidate without count assertions.

    The returned CID is a candidate map only.  A concrete Isabelle instance
    must check each map, control, and ordered-child equation against its
    provider before using it in a rank check.
    """
    states = tuple(
        BoundaryState(kind, a, residue)
        for kind in ("N", "Z")
        for a in range(2, 10)
        for residue in range(PERIOD)
    )
    indices = _state_index(states)
    # The same canonical chart walk publishes only a sealed terminal header;
    # it does not build fragment arrays or indexed prefixes for this audit.
    macros = tuple(
        _completed_macro_return(construct_completed_return(state, grouped_near=True))
        for state in states
    )
    controls = tuple(macro.control for macro in macros)
    rows = _rows(macros, indices)
    payloads = c1_payloads(states, macros, indices)
    class_ids, witnesses, rounds = refine_with_witnesses(rows, controls, states)
    class_controls, class_children = _quotient_rows(rows, controls, class_ids)
    class_ranks = class_rank_candidate(class_controls, class_children)
    return SemanticFutureCandidate(
        states,
        controls,
        class_ids,
        class_controls,
        class_children,
        class_ranks,
        payloads,
        witnesses,
        _seam_collision(class_ids, states, payloads),
        rounds,
    )


__all__ = [
    "C1OccurrencePayload",
    "C1SeamObservation",
    "FutureRefinementCollision",
    "SeamProjectionCollision",
    "SemanticFutureCandidate",
    "build_semantic_future_candidate",
]


def main() -> None:
    """Run the semantic FutureCID candidate command line."""
    from devtools.verification.comma_semantic_future_candidate_cli import (
        main as run_cli,
    )

    run_cli()


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(main))
