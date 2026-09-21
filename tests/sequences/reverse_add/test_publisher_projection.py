from __future__ import annotations

from dataclasses import replace

import pytest

from devtools.proofs.oracles.reverse_publisher import (
    ReversePublisherProjection,
    build_reverse_publisher_projection,
)
from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken, ExactSource
from number_compiler.arithmetic.contracts.source_geometry import SourceGeometry
from number_compiler.arithmetic.contracts.temporal_family import _issue_certificate
from number_compiler.arithmetic.polynomials.twisted_observer import (
    first_mirror_obstruction,
)
from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.actions.lazy_compiler import LazyCompiler
from number_compiler.hashlife.observation.hashlife_projection import HashLifeBlockIndex
from number_compiler.projection.digit_terminal import DigitNormalizeBlockEffect
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.reverse_add.compilation import compile_reverse_pair_power
from number_compiler.sequences.reverse_add.power import (
    ReverseAddPoweredTerm,
    pair_field_from_integer,
)
from tests.support.reverse_higher_interface import _direct_step


def _reference_publisher(term: ReverseAddPoweredTerm) -> ReversePublisherProjection:
    """Construct the retired publisher only as a bounded differential oracle."""
    if term.generation < 1:
        raise AssertionError("publisher reference requires a positive generation")
    ledger = term._ledger
    compiler = LazyCompiler(ledger)
    terminal = compiler.atom(DigitNormalizeBlockEffect(term.base))
    effect = terminal
    if term.generation > 1:
        pair_power = compile_reverse_pair_power(
            compiler, term.base, term.generation - 1
        )
        if pair_power.root is None:
            raise AssertionError("positive pair exponent without powered effect")
        effect = compiler.compose(pair_power.root, terminal)
    source = pair_field_from_integer(term.seed, term.base)
    blank = 2 * term.base - 1
    source_geometry = SourceGeometry(
        ledger,
        ExactSource(
            source,
            term.base,
            "reverse-add",
            blank,
            term.maximum_width,
            blank,
        ),
    )
    source_geometry.span(source, blank, term.maximum_width)
    certificate = _issue_certificate(
        effect,
        "reverse-add",
        term.generation - 1,
        ledger=ledger,
    )
    return build_reverse_publisher_projection(
        source,
        logical_extent=term.maximum_width,
        source_geometry=source_geometry,
        ledger=ledger,
        effect=effect,
        compiler=compiler,
        certificate=certificate,
    )


def _literal(seed: int, generations: int) -> tuple[int, ...]:
    value = seed
    for _ in range(generations):
        value += int(str(value)[::-1])
    return tuple(map(int, reversed(str(value))))


@pytest.mark.parametrize("generation", range(1, 17))
def test_source_bound_publisher_matches_literal_196(generation: int) -> None:
    term = ReverseAddPoweredTerm(196, generation)
    expected = _literal(196, generation)
    publisher = _reference_publisher(term)
    assert type(publisher) is ReversePublisherProjection
    source = pair_field_from_integer(term.seed, term.base)
    publisher.sources.source.require_source(source, 2 * term.base - 1)
    assert publisher.macro.source_extent == len(source)
    assert publisher.macro.width == term.maximum_width
    assert tuple(publisher.iter_active()) == expected
    assert publisher.active_width() == len(expected)


def test_publisher_defers_reachable_image_until_first_output_demand() -> None:
    term = ReverseAddPoweredTerm(196, 32)
    publisher = _reference_publisher(term)
    assert type(publisher) is ReversePublisherProjection
    assert publisher._macro is None
    assert publisher._image_binding is None
    assert term._ledger.counters.get("higher_concrete_operation_evaluations", 0) == 0
    assert term._ledger.counters.get("higher_action_continuation_requests", 0) == 0
    report = term.behavior_metrics()
    assert publisher._macro is None
    assert report.bounded_temporal_runtime_cutover_complete == 0
    assert report.bounded_temporal_runtime_cutover_blocker == (
        "reverse_cylinder_pullback_unconstructed"
    )

    publisher.validate_execution()
    assert publisher._macro is None
    assert publisher.point(0) == _literal(196, 32)[0]
    assert publisher._macro is not None
    assert publisher._image_binding == (
        publisher._macro.interface,
        publisher._macro.output,
    )


def test_reference_publisher_rejects_coordinated_action_substitution_without_work() -> (
    None
):
    term = ReverseAddPoweredTerm(196, 8)
    publisher = _reference_publisher(term)
    assert type(publisher) is ReversePublisherProjection
    publisher.action = publisher.actions.identity
    publisher._binding = (
        publisher.source,
        publisher.action,
        publisher.source_local_action,
        publisher._source_ports,
        publisher.program,
        publisher.output_encoding,
    )
    before = term._ledger.snapshot()
    with pytest.raises(ValueError, match="canonical action was changed"):
        publisher.validate_execution()
    assert publisher._macro is None
    assert term._ledger.snapshot() == before


def test_pending_publisher_rejects_changed_source_before_image_construction() -> None:
    publisher = _reference_publisher(ReverseAddPoweredTerm(196, 8))
    assert type(publisher) is ReversePublisherProjection
    original = publisher.source
    publisher.source = publisher.sources.forest(0, 1)
    try:
        with pytest.raises(ValueError, match="binding was changed"):
            publisher.point(0)
        assert publisher._macro is None
        assert publisher._image_binding is None
    finally:
        publisher.source = original


def test_pending_publisher_rejects_coordinated_action_and_schema_mutation() -> None:
    publisher = _reference_publisher(ReverseAddPoweredTerm(196, 8))
    foreign = _reference_publisher(ReverseAddPoweredTerm(89, 8))
    assert type(publisher) is type(foreign) is ReversePublisherProjection
    original_action, original_binding = publisher.action, publisher._binding
    original_schema = publisher._schema
    before = publisher.ledger.snapshot()
    try:
        publisher.action = publisher.actions.identity
        publisher._binding = (
            publisher.source,
            publisher.action,
            publisher.source_local_action,
            publisher._source_ports,
            publisher.program,
            publisher.output_encoding,
        )
        with pytest.raises(ValueError, match="canonical action was changed"):
            publisher.validate_execution()
        assert publisher._macro is None
        assert publisher.ledger.snapshot() == before

        publisher.action, publisher._binding = original_action, original_binding
        publisher._schema = foreign._schema
        with pytest.raises(ValueError, match="action schema was changed"):
            publisher.validate_execution()
        assert publisher._macro is None
        assert publisher.ledger.snapshot() == before
    finally:
        publisher.action, publisher._binding = original_action, original_binding
        publisher._schema = original_schema


def test_failed_lazy_image_demand_is_terminal_and_auditable(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from devtools.experiments.reverse_add.higher_interface import (
        ReverseHigherInterfaceCompiler,
    )
    from devtools.experiments.reverse_add.temporal_payload_audit import (
        audit_reverse_temporal_experiment,
    )

    publisher = _reference_publisher(ReverseAddPoweredTerm(196, 8))
    assert type(publisher) is ReversePublisherProjection

    def fail(*_args: object, **_kwargs: object) -> object:
        raise RuntimeError("injected image-construction failure")

    monkeypatch.setattr(ReverseHigherInterfaceCompiler, "compile", fail)
    with pytest.raises(RuntimeError, match="injected image-construction failure"):
        publisher.point(0)
    assert publisher._macro is None
    assert publisher._image_binding is None
    assert publisher._image_failure is not None
    assert not audit_reverse_temporal_experiment(publisher.ledger).invalid
    before = publisher.ledger.snapshot()
    with pytest.raises(RuntimeError, match="previously failed"):
        publisher.point(0)
    assert publisher.ledger.snapshot() == before
    publisher.close()
    with pytest.raises(ValueError, match="closed reverse publisher"):
        publisher.point(0)


def test_publisher_rejects_foreign_source_and_action_before_observation() -> None:
    first = _reference_publisher(ReverseAddPoweredTerm(196, 8))
    second = _reference_publisher(ReverseAddPoweredTerm(89, 8))
    assert type(first) is type(second) is ReversePublisherProjection
    original_source, original_action = first.source, first.action
    try:
        first.source = first.sources.forest(0, 1)
        with pytest.raises(ValueError, match="binding was changed"):
            first.point(0)
        first.source = second.source
        with pytest.raises(ValueError, match="different arena"):
            first.point(0)
        first.source = original_source
        first.action = first.actions.identity
        with pytest.raises(ValueError, match="binding was changed"):
            first.point(0)
        first.action = replace(
            original_action,
            owner=ArenaToken("foreign-reverse-action"),
        )
        with pytest.raises(ValueError, match="different arena"):
            first.point(0)
        first.action = FieldCellActionID(
            original_action.owner,
            "proof-machine-state",
            original_action.local_id,
        )
        with pytest.raises(ValueError, match="node kind"):
            first.point(0)
    finally:
        first.source, first.action = original_source, original_action


def test_publisher_rejects_an_alternate_same_compiler_operator() -> None:
    publisher = _reference_publisher(ReverseAddPoweredTerm(196, 8))
    assert type(publisher) is ReversePublisherProjection
    original = publisher.effect
    try:
        publisher.effect = publisher.compiler.atom(BaseBlockEffect(10))
        with pytest.raises(ValueError, match="operator binding was changed"):
            publisher.point(0)
    finally:
        publisher.effect = original


def test_direct_publisher_rejects_unissued_mismatched_and_foreign_certificates_before_allocation() -> (
    None
):
    ledger = ResourceLedger()
    compiler = LazyCompiler(ledger)
    effect = compile_reverse_pair_power(compiler, 10, 3).root
    foreign_effect = compile_reverse_pair_power(compiler, 10, 2).root
    assert effect is not None and foreign_effect is not None
    source = (7, 18, 7)
    geometry = SourceGeometry(
        ledger,
        ExactSource(source, 10, "reverse-add", 19, 6, 19),
    )
    geometry.span(source, 19, 6)
    certificate = _issue_certificate(
        effect, "reverse-add", 3, ledger=ledger, output_encoding="pair"
    )
    foreign = _issue_certificate(
        foreign_effect, "reverse-add", 2, ledger=ledger, output_encoding="pair"
    )
    invalid = (
        replace(certificate, _issuer=object()),
        replace(certificate, output_encoding="digits"),
        foreign,
    )
    before = ledger.snapshot()
    for rejected in invalid:
        with pytest.raises(ValueError):
            build_reverse_publisher_projection(
                source,
                logical_extent=6,
                source_geometry=geometry,
                ledger=ledger,
                effect=effect,
                compiler=compiler,
                certificate=rejected,
            )
        assert ledger.snapshot() == before


def test_publisher_rejects_replaced_certificate_after_publication() -> None:
    term = ReverseAddPoweredTerm(196, 8)
    publisher = _reference_publisher(term)
    assert type(publisher) is ReversePublisherProjection
    original = publisher.certificate
    try:
        publisher.certificate = replace(original, _issuer=object())
        before = publisher.ledger.snapshot()
        assert publisher.ledger.snapshot() == before
        with pytest.raises(ValueError, match="certificate binding was changed"):
            publisher.point(0)
    finally:
        publisher.certificate = original


def test_pair_output_certificate_does_not_append_terminal_normalization() -> None:
    ledger = ResourceLedger()
    compiler = LazyCompiler(ledger)
    effect = compile_reverse_pair_power(compiler, 10, 3).root
    assert effect is not None
    source = (7, 18, 7)
    index = HashLifeBlockIndex(
        effect,
        source,
        logical_length=6,
        certificate=_issue_certificate(
            effect,
            "reverse-add",
            3,
            ledger=ledger,
            output_encoding="pair",
        ),
        ledger=ledger,
        compiler=compiler,
    )
    certificate = index._certificate
    if certificate is None:
        raise AssertionError("missing pair certificate")
    publisher = build_reverse_publisher_projection(
        source,
        logical_extent=6,
        source_geometry=index._source_geometry,
        ledger=ledger,
        effect=effect,
        compiler=compiler,
        certificate=certificate,
    )
    assert type(publisher) is ReversePublisherProjection
    assert publisher.output_encoding == "pair"
    expected: tuple[int, ...] = source + (19, 19, 19)
    for _ in range(3):
        expected = _direct_step(expected, 10)
    assert tuple(index.direct_powered_point(i) for i in range(6)) == expected


def test_publisher_uses_reachable_image_for_point_width_and_mirror(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    term = ReverseAddPoweredTerm(196, 12)
    publisher = _reference_publisher(term)
    assert type(publisher) is ReversePublisherProjection
    visits = publisher.ledger.counters.get("output_morphism_visits", 0)
    assert publisher.point(2) == _literal(196, 12)[2]
    assert publisher.ledger.counters["output_morphism_visits"] > visits
    assert term.digit(2) == _literal(196, 12)[2]
    assert term.width() == len(_literal(196, 12))

    def forbidden(*_args: object, **_kwargs: object) -> object:
        raise AssertionError("mirror observation attempted endpoint completion")

    monkeypatch.setattr(ReverseAddPoweredTerm, "digits", forbidden)
    obstruction = term.mirror_obstruction()
    assert obstruction is not None
    assert term.metrics().completed_result_entries > 0


@pytest.mark.parametrize("seed,generation", ((1, 1), (89, 7), (196, 12), (999, 9)))
def test_recursive_fold_matches_independent_literal_sheets(
    seed: int, generation: int
) -> None:
    term = ReverseAddPoweredTerm(seed, generation)
    expected = _literal(seed, generation)
    observed = term.mirror_obstruction()
    reference = first_mirror_obstruction(
        len(expected), expected.__getitem__, first_width=1
    )
    assert observed == reference
    publisher = _reference_publisher(term)
    assert type(publisher) is ReversePublisherProjection
    assert publisher.macro.width == term.maximum_width
    source = pair_field_from_integer(term.seed, term.base)
    publisher.sources.source.require_source(source, 2 * term.base - 1)
    assert publisher.macro.source_extent == len(source)
    assert publisher.mirror_obstruction() == reference
    assert (
        publisher.ledger.counters.get("reverse_publisher_cylinder_node_evaluations", 0)
        > 0
    )


def test_reference_publisher_does_not_exempt_higher_continuation_work() -> None:
    term = ReverseAddPoweredTerm(196, 8)
    _reference_publisher(term).point(0)
    report = term.behavior_metrics()
    assert term.metrics().higher_action_continuation_requests > 0
    assert report.bounded_temporal_runtime_cutover_complete == 0
    assert report.bounded_temporal_runtime_cutover_blocker == (
        "reverse_cylinder_pullback_unconstructed"
    )


def test_publisher_preserves_budget_refusal() -> None:
    from number_compiler.arithmetic.contracts.block_effect import (
        BlockContextBudgetExceeded,
    )

    term = ReverseAddPoweredTerm(
        196,
        32,
        max_context_nodes=16,
        max_cache_entries=16,
    )
    with pytest.raises(BlockContextBudgetExceeded):
        _reference_publisher(term)
