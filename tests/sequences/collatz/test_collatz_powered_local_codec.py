"""Adversarial checks for the bounded Collatz spatial action carrier."""

from __future__ import annotations

from dataclasses import fields
from itertools import product
from typing import TYPE_CHECKING, Never, cast

import pytest

from number_compiler.arithmetic.automata.symmetry_powering import ActionTransform
from number_compiler.arithmetic.contracts.scoped_handles import (
    ActionProgramID,
    ArenaHandle,
    ArenaToken,
    ExactSource,
)
from number_compiler.arithmetic.contracts.semantic_identity import SemanticIdentity
from number_compiler.arithmetic.contracts.source_geometry import SourceGeometry
from number_compiler.arithmetic.functions.finite_function_types import (
    BOOL,
    FunctionSignature,
)
from number_compiler.arithmetic.functions.semantic_functions import (
    SemanticFunctionArena,
)
from number_compiler.hashlife.actions.diamond_actions import PortSignatureID
from number_compiler.hashlife.actions.field_actions import (
    CoordinateOutputMorphismID,
    FieldGeometry,
    FieldGeometryArena,
    FieldGeometryID,
)
from number_compiler.hashlife.execution.field_images import (
    SourceCellArena,
    SourceCellID,
    SourceForestID,
)
from number_compiler.hashlife.execution.field_transfer import (
    FieldTransferCandidate,
    FieldTransferExecutor,
)
from number_compiler.hashlife.execution.field_transfers import FieldTransferArena
from number_compiler.hashlife.interfaces.diamond_quotient import (
    COMPONENT_ROLES,
    DiamondQuotientArena,
    MacroComponents,
    MacroInterface,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz.field_action import (
    CollatzCocyclePrograms,
    CollatzDefectArena,
    CollatzFieldActionArena,
    CollatzFieldActionID,
    ProgramRole,
)
from number_compiler.sequences.collatz.local_transfer import (
    CollatzPoweredLocalTransferAdapter,
)
from number_compiler.sequences.collatz.powered_local_codec import (
    CollatzLocalAction,
    CollatzLocalActionID,
    CollatzPoweredLocalCodec,
)
from tests.support.local_codec_assertions import assert_publication_refused

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.field_transfer import (
        FieldTransferApplication,
    )


def _codec(
    digits: tuple[int, ...] = (0, 1, 2, 3),
) -> tuple[CollatzPoweredLocalCodec, SourceCellArena]:
    ledger = ResourceLedger(max_nodes=10_000, max_cache_entries=10_000)
    geometry = SourceGeometry(
        ledger, ExactSource(digits, 4, "collatz", blank=0, extent=len(digits))
    )
    geometry.span(digits, 0, len(digits))
    sources = SourceCellArena(geometry)
    return CollatzPoweredLocalCodec(sources), sources


def _word_action(
    codec: CollatzPoweredLocalCodec, word: tuple[int, ...]
) -> CollatzLocalActionID:
    result = codec.leaf(word[0])
    for symbol in word[1:]:
        result = codec.compose(result, codec.leaf(symbol))
    return result


def _binary_codec(
    digits: tuple[int, ...],
    *,
    extent: int | None = None,
) -> tuple[CollatzPoweredLocalCodec, SourceCellArena, SourceForestID]:
    ledger = ResourceLedger(max_nodes=10_000, max_cache_entries=10_000)
    size = len(digits) if extent is None else extent
    geometry = SourceGeometry(
        ledger, ExactSource(digits, 2, "collatz", blank=2, extent=size)
    )
    geometry.span(digits, 2, size)
    sources = SourceCellArena(geometry)
    forest = sources.forest(0, size)
    return CollatzPoweredLocalCodec(sources), sources, forest


def _forged(reference: CollatzLocalActionID, **changes: object) -> CollatzLocalActionID:
    result = object.__new__(CollatzLocalActionID)
    for field in fields(reference):
        object.__setattr__(
            result, field.name, changes.get(field.name, getattr(reference, field.name))
        )
    return result


@pytest.mark.parametrize("word", tuple(product(range(4), repeat=3)))
def test_collatz_local_actions_match_exact_three_carry_scans(
    word: tuple[int, ...],
) -> None:
    codec, _ = _codec()
    action = _word_action(codec, word)
    for reverse in (False, True):
        for incoming in range(3):
            expected = incoming
            for symbol in tuple(reversed(word)) if reverse else word:
                expected = (3 * symbol + expected) // 4
            assert codec.apply(action, incoming, reverse=reverse) == expected


def test_collatz_local_spatial_composition_is_associative() -> None:
    codec, _ = _codec()
    a, b, c = (codec.leaf(symbol) for symbol in (1, 2, 3))
    assert codec.compose(codec.compose(a, b), c) == codec.compose(
        a, codec.compose(b, c)
    )


def test_collatz_local_mirror_is_canonical_geometric_alias() -> None:
    codec, _ = _codec()
    word = (0, 1, 3, 2)
    action = _word_action(codec, word)
    mirrored = codec.transformed(action, ActionTransform.MIRROR)
    reverse_word = _word_action(codec, tuple(reversed(word)))
    assert mirrored == reverse_word
    assert codec.transformed(mirrored, ActionTransform.MIRROR) == action
    assert codec.metrics().mirror_alias_hits > 0


def test_collatz_source_action_hits_canonical_parent_before_child_work() -> None:
    codec, sources = _codec((0,) * 8)
    first = sources.intern(0, 2)
    same_semantic_parent = sources.intern(4, 2)
    assert first == same_semantic_parent
    action = codec.source_action(first)
    before = codec.metrics()
    assert codec.source_action(same_semantic_parent) == action
    assert codec.metrics() == before


def test_collatz_local_codec_stores_are_independently_inventoried() -> None:
    from number_compiler.resources.metric_collection import collect_ledger_metrics

    codec, sources = _codec()
    codec.source_action(sources.intern(0, 2))
    rows = [
        row for row in codec.ledger.inventory() if row.role.startswith("collatz_local_")
    ]
    assert {
        "collatz_local_action",
        "collatz_local_action_interner",
        "collatz_local_action_composition",
        "collatz_local_leaf_binding",
        "collatz_local_source_binding",
    } <= {row.role for row in rows}
    assert all(row.observed_entries == row.entries for row in rows)
    assert all(row.payloads_registered and not row.evictable for row in rows)
    actions = [row for row in rows if row.role == "collatz_local_action"]
    assert len(actions) == 1 and actions[0].observed_nodes == actions[0].nodes
    assert collect_ledger_metrics(codec.ledger).algebraic_component_nodes == (
        codec.metrics().action_count
    )


def test_collatz_source_forest_action_covers_every_root_without_id_aliasing() -> None:
    digits = (3, 0, 1, 2, 1, 0)
    codec, sources = _codec(digits)
    forest = sources.forest(0, len(digits))
    result = codec.source_action(forest)
    expected = _word_action(codec, digits)
    assert result == expected
    # Cell and forest identities are independently allocated.  Their integer
    # payloads may coincide, so the occurrence cache must include the sort.
    cell = sources.intern(0, 2)
    codec.source_action(cell)
    assert cell in codec._source_actions
    assert forest in codec._source_actions
    assert all(
        type(key) in (SourceCellID, SourceForestID) for key in codec._source_actions
    )


def test_collatz_binary_source_morphism_pairs_aligned_radix4_symbols() -> None:
    bits = (1, 0, 0, 1, 1)
    codec, _sources, forest = _binary_codec(bits)
    result = codec.radix4_source_action(forest)
    expected = _word_action(codec, (1, 2, 1))
    assert result == expected
    assert forest in codec._binary_source_actions
    assert forest not in codec._source_actions


def test_collatz_binary_source_morphism_maps_padding_blank_to_zero() -> None:
    codec, sources, forest = _binary_codec((1,), extent=4)
    result = codec.radix4_source_action(forest)
    expected = _word_action(codec, (1, 0))
    assert result == expected
    before = codec.metrics(), codec.ledger.snapshot()
    assert codec.radix4_source_action(forest) == result
    assert (codec.metrics(), codec.ledger.snapshot()) == before
    foreign = SourceForestID(ArenaToken("foreign"), forest.kind, forest.local_id)
    with pytest.raises(ValueError):
        codec.radix4_source_action(foreign)
    assert sources.binding_extent(forest) == 4


def test_collatz_binary_source_morphism_skips_canonical_blank_subtrees() -> None:
    codec, _sources, forest = _binary_codec((1,), extent=1 << 10)
    codec.radix4_source_action(forest)
    counters = codec.ledger.snapshot().counters
    assert counters["collatz_radix4_source_morphism_compilations"] == 1
    assert counters["source_leaf_visits"] <= 2 * (1 << 10).bit_length()


def test_collatz_spatial_cache_keys_retain_scoped_action_handles() -> None:
    codec, _ = _codec()
    left, right = codec.leaf(1), codec.leaf(2)
    codec.compose(left, right)
    assert codec._compose
    assert all(
        type(key) is tuple
        and len(key) == 2
        and all(type(item) is CollatzLocalActionID for item in key)
        for key in codec._compose
    )


def test_collatz_source_bindings_validate_owner_before_warm_lookup() -> None:
    codec, sources = _codec((3, 0, 1, 2, 1, 0))
    cell = sources.intern(0, 2)
    forest = sources.forest(0, 6)
    codec.source_action(cell)
    codec.source_action(forest)
    before = codec.metrics(), codec.ledger.snapshot()
    with pytest.raises(ValueError):
        codec.source_action(
            SourceCellID(ArenaToken("foreign"), cell.kind, cell.local_id)
        )
    with pytest.raises(ValueError):
        codec.source_action(
            SourceForestID(ArenaToken("foreign"), forest.kind, forest.local_id)
        )
    assert (codec.metrics(), codec.ledger.snapshot()) == before


def test_collatz_local_handles_reject_wrong_sort_foreign_and_integer_aliases() -> None:
    codec, _ = _codec()
    action = codec.leaf(2)
    other, _ = _codec()
    foreign = other.leaf(2)
    before = codec.metrics(), codec.ledger.snapshot()
    with pytest.raises(TypeError):
        codec.resolve(
            cast(
                CollatzLocalActionID,
                ArenaHandle(action.owner, action.kind, action.local_id),
            )
        )
    for malformed in (
        foreign,
        _forged(action, local_id=True),
        _forged(action, local_id=0.0),
        _forged(action, owner=ArenaToken("foreign")),
        _forged(action, kind="other"),
    ):
        with pytest.raises((TypeError, ValueError)):
            codec.resolve(malformed)
    for state in (True, 0.0):
        with pytest.raises(ValueError):
            codec.apply(action, cast(int, state))
    assert (codec.metrics(), codec.ledger.snapshot()) == before


def test_collatz_local_nodes_cannot_retain_exact_future_payloads() -> None:
    codec, sources = _codec()
    root = sources.intern(0, 2)
    record = codec.resolve(codec.source_action(root))
    assert tuple(field.name for field in fields(CollatzLocalAction)) == (
        "forward",
        "reverse",
    )
    assert not hasattr(record, "__dict__")
    for forbidden in (
        "digits",
        "tile",
        "span",
        "output",
        "carry_tape",
        "tail",
        "offset",
        "proof_state",
    ):
        assert not hasattr(record, forbidden)
    assert all(len(mapping) == 3 for mapping in (record.forward, record.reverse))


def test_collatz_local_public_inputs_require_exact_types() -> None:
    codec, sources = _codec()
    source = sources.intern(0, 2)
    action = codec.source_action(source)
    for symbol in (True, 1.0):
        with pytest.raises(ValueError):
            codec.leaf(cast(int, symbol))
    with pytest.raises(ValueError):
        codec.transformed(action, ActionTransform.CONJUGATE)
    with pytest.raises(TypeError):
        codec.source_action(
            cast(
                SourceForestID,
                ArenaHandle(source.owner, source.kind, source.local_id),
            )
        )


@pytest.mark.accounting
def test_collatz_local_codec_rejects_leaf_and_parent_publication_atomically() -> None:
    codec, _ = _codec((1, 2))
    ledger = codec.ledger
    assert_publication_refused(
        ledger,
        (codec._nodes, codec._keys, codec._leaf_actions, codec._compose),
        lambda: codec.leaf(3),
    )

    codec, _ = _codec((1, 2))
    ledger = codec.ledger
    left, right = codec.leaf(1), codec.leaf(2)
    assert_publication_refused(
        ledger,
        (codec._nodes, codec._keys, codec._compose),
        lambda: codec.compose(left, right),
    )


class _SymbolicPrograms:
    """Canonical handle-only algebra for transfer wiring tests."""

    def __init__(self) -> None:
        self.owner = ArenaToken("collatz-local-test-programs")
        self._roles = (
            "root",
            "affine",
            "output",
            "physical-tick",
            "valuation",
            "frame",
        )

    def identity(self, role: ProgramRole) -> ActionProgramID:
        if role not in self._roles:
            raise ValueError(role)
        return ActionProgramID(self.owner, "symbolic-" + role, 0)

    def validate(self, role: ProgramRole, reference: ActionProgramID) -> int:
        reference.validate(self.owner, "symbolic-" + role, size=1)
        return reference.local_id

    def semantic_identity(
        self,
        role: ProgramRole,
        reference: ActionProgramID,
    ) -> SemanticIdentity:
        self.validate(role, reference)
        return SemanticIdentity("", ("collatz-local-test-program-v1", role))

    def composed_semantic_identity(
        self,
        role: ProgramRole,
        before: ActionProgramID,
        after: ActionProgramID,
    ) -> SemanticIdentity:
        self.validate(role, before)
        self.validate(role, after)
        return SemanticIdentity("", ("collatz-local-test-program-v1", role))

    def compose(
        self,
        role: ProgramRole,
        before: ActionProgramID,
        after: ActionProgramID,
    ) -> ActionProgramID:
        self.validate(role, before)
        self.validate(role, after)
        return self.identity(role)


def _transfer_fixture(
    *, forest: bool = False, mismatched_output: bool = False
) -> tuple[
    FieldTransferApplication,
    CollatzPoweredLocalTransferAdapter,
    CollatzPoweredLocalCodec,
    list[tuple[object, ...]],
]:
    ledger = ResourceLedger(max_nodes=10_000, max_cache_entries=10_000)
    digits = (1, 0, 2, 0)
    source_geometry = SourceGeometry(
        ledger, ExactSource(digits, 4, "collatz", blank=0, extent=4)
    )
    source_geometry.span(digits, 0, 4)
    sources = SourceCellArena(source_geometry)
    source = sources.forest(0, 4) if forest else sources.intern(0, 2)
    codec = CollatzPoweredLocalCodec(sources)
    programs = _SymbolicPrograms()
    defects = CollatzDefectArena(((0,),), identity=0, ledger=ledger)
    actions = CollatzFieldActionArena(
        programs, defects, padic_precision=4, ledger=ledger
    )
    action = actions.identity

    functions = SemanticFunctionArena(ledger)
    quotients = DiamondQuotientArena(functions)
    signature_shape = FunctionSignature((), BOOL)
    zero = functions.atom(signature_shape, 0)
    one = functions.atom(signature_shape, 1)
    signature = quotients.intern_interface(
        MacroInterface(
            SemanticIdentity("collatz-local-transfer-test-v1", ("collatz",)),
            (),
            (BOOL,) * len(COMPONENT_ROLES),
            one,
        )
    )
    interface = quotients.intern(
        signature,
        MacroComponents(*(zero for _ in COMPONENT_ROLES)),
    )
    geometries = FieldGeometryArena(ledger)
    geometry = geometries.intern(FieldGeometry(2))
    port_owner = ArenaToken("collatz-local-test-port")
    incoming = ArenaHandle(port_owner, "collatz-local-test-port", 0)
    compile_calls: list[tuple[object, ...]] = []

    def compile_complete(
        selected_action: CollatzFieldActionID,
        local_action: CollatzLocalActionID,
        output_program: ActionProgramID,
        cocycles: CollatzCocyclePrograms,
        selected_geometry: FieldGeometryID,
        selected_signature: PortSignatureID,
    ) -> FieldTransferCandidate:
        assert type(local_action) is CollatzLocalActionID
        assert type(output_program) is ActionProgramID
        assert type(cocycles) is CollatzCocyclePrograms
        compile_calls.append(
            (
                selected_action,
                local_action,
                output_program,
                cocycles,
                selected_geometry,
                selected_signature,
            )
        )
        output = actions.coordinate_output(selected_action)
        if mismatched_output:
            output = CoordinateOutputMorphismID(
                output.owner,
                output.kind,
                output.local_id + 1,
            )
        return FieldTransferCandidate(
            interface,
            output,
            4,
        )

    def validate_port(value: ArenaHandle) -> None:
        value.validate(port_owner, "collatz-local-test-port", size=1)

    def validate_output(value: CoordinateOutputMorphismID) -> None:
        actions.output_program(value)

    adapter = CollatzPoweredLocalTransferAdapter(
        actions,
        codec,
        quotients,
        compile_complete=compile_complete,
        validate_port=validate_port,
        point=lambda _transfer, _source, _incoming, coordinate: coordinate & 1,
        width=lambda _transfer, _source, _incoming: 4,
        validate_output=(lambda _value: None) if mismatched_output else None,
        expected_output=actions.coordinate_output(action),
    )
    transfers = FieldTransferArena(
        ledger,
        sources,
        geometries,
        quotients,
        action_owner=actions.owner,
        output_owner=actions.output_owner,
        action_validate=actions.validate_action,
        output_validate=validate_output,
        action_kind=actions.action_kind,
        output_kind=actions.output_kind,
    )
    executor = FieldTransferExecutor(transfers, adapter)
    application = executor.application(action, source, geometry, signature, incoming)
    return application, adapter, codec, compile_calls


def test_collatz_local_codec_drives_shared_field_transfer_application() -> None:
    application, _adapter, codec, compile_calls = _transfer_fixture()
    assert application.point(3) == 1
    assert application.active_width() == 4
    assert len(compile_calls) == 1
    before = codec.metrics()
    assert application.point(2) == 0
    assert len(compile_calls) == 1
    assert codec.metrics() == before


def test_collatz_complete_transfer_cannot_alias_another_output_morphism() -> None:
    application, _adapter, _codec, _calls = _transfer_fixture(
        mismatched_output=True,
    )
    with pytest.raises(ValueError, match="another output morphism"):
        application.point(0)
    assert application.retained_entries() == 0


def test_collatz_local_codec_drives_full_source_forest_transfer() -> None:
    application, _adapter, codec, compile_calls = _transfer_fixture(forest=True)
    assert application.point(3) == 1
    assert application.active_width() == 4
    assert len(compile_calls) == 1
    assert application.source in codec._source_actions


def test_collatz_transfer_path_never_calls_proof_generic_or_whole_word_routes(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    application, _adapter, _codec, _calls = _transfer_fixture()

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("retired Collatz execution route was called")

    monkeypatch.setattr(
        "devtools.verification.collatz_spacetime.CollatzCausalSpacetimeEngine.advance",
        forbidden,
    )
    monkeypatch.setattr(
        "devtools.verification.collatz_spacetime.CollatzCausalSpacetimeEngine.advance_power",
        forbidden,
    )
    monkeypatch.setattr(
        "devtools.verification.collatz_spacetime.CollatzCausalSpacetimeEngine.advance_event_power",
        forbidden,
    )
    monkeypatch.setattr(
        "number_compiler.hashlife.execution.continuations.diamond_runtime.DiamondRuntime.execute",
        forbidden,
    )
    monkeypatch.setattr(
        "devtools.verification.collatz_c4_reference.CollatzC4ReferenceApplication._apply_machine",
        forbidden,
    )
    assert application.point(1) == 1
    assert application.active_width() == 4
    counters = application.ledger.counters
    assert counters.get("proof_machine_applications", 0) == 0
    assert counters.get("whole_word_sweeps", 0) == 0
    assert counters.get("sequential_generation_advances", 0) == 0
