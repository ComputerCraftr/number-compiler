"""Independent numeric-alias and original-source authority admission probes."""

from typing import Never, TypedDict, cast

import pytest

from number_compiler.api.number_api import NumberCompiler
from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.arithmetic.contracts.exact_tree_context import (
    OriginalSourceConstruction,
)
from number_compiler.arithmetic.contracts.scoped_handles import ExactSource
from number_compiler.arithmetic.contracts.source_geometry import SourceGeometry
from number_compiler.hashlife.observation.hashlife_projection import HashLifeBlockIndex
from number_compiler.resources.ledger import OwnedMemo, ResourceLedger, ResourceScope
from number_compiler.sequences.collatz.block_power import (
    CollatzPhysicalBlockEffect,
    PoweredCollatzTerm,
    power_collatz_physical_effect,
)
from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm


class _OwnerArguments(TypedDict):
    name: str
    role: str
    scope: ResourceScope


BAD = (True, False, 0.0, 1.0, float("nan"), float("inf"), "1")


def forbidden(*args: object, **kwargs: object) -> Never:
    raise AssertionError("invalid input reached source or endpoint execution")


@pytest.mark.parametrize("value", BAD)
@pytest.mark.parametrize("operation", ("reserve", "release", "capacity", "tighten"))
def test_resource_quantities_reject_numeric_aliases_atomically(
    value: object, operation: str
) -> None:
    value = cast(int, value)
    ledger = ResourceLedger()
    owner = ledger.register("valid", "query_memo")
    ledger.reserve(owner, entries=2, nodes=2)
    before = ledger.snapshot()
    for dimension in ("entries", "nodes"):
        with pytest.raises((TypeError, ValueError)):
            if operation == "reserve":
                ledger.reserve(owner, **{dimension: value})
            elif operation == "release":
                ledger.release(owner, **{dimension: value})
            elif operation == "capacity":
                ledger.check_store_capacity(
                    owner,
                    value if dimension == "entries" else 0,
                    value if dimension == "nodes" else 0,
                )
            else:
                ledger.tighten_limits(
                    value if dimension == "nodes" else None,
                    value if dimension == "entries" else None,
                )
        assert ledger.snapshot() == before
        assert ledger.max_nodes is ledger.max_cache_entries is None


@pytest.mark.parametrize("value", BAD + (-1, 2))
def test_resource_owner_aliases_reject_even_when_integer_accounts_exist(
    value: object,
) -> None:
    value = cast(int, value)
    ledger = ResourceLedger()
    ledger.register("zero", "query_memo")
    ledger.register("one", "query_memo")
    before = ledger.snapshot()
    for operation in (ledger.reserve, ledger.release, ledger.mark_disposed):
        with pytest.raises((TypeError, ValueError)):
            operation(value)
        assert ledger.snapshot() == before
    with pytest.raises((TypeError, ValueError)):
        ledger.reserve_many(((0, 1, 1), (value, 0, 0)))
    assert ledger.snapshot() == before


@pytest.mark.parametrize("value", BAD)
@pytest.mark.parametrize("factory", ("dict", "list", "memo"))
def test_factory_node_quantity_rejects_before_container_registration(
    value: object, factory: str
) -> None:
    value = cast(int, value)
    ledger = ResourceLedger()
    owner = ledger.register("factory", "query_memo")
    before = ledger.snapshot()
    with pytest.raises((TypeError, ValueError)):
        if factory == "dict":
            ledger.make_dict(owner, nodes_per_entry=value)
        elif factory == "list":
            ledger.make_list(owner, nodes_per_entry=value)
        else:
            OwnedMemo(ledger, owner, nodes_per_entry=value)
    assert ledger.snapshot() == before
    assert tuple(ledger.iter_containers()) == ()


@pytest.mark.parametrize("value", (0, 1, 0.0, float("nan"), "yes"))
def test_factory_append_only_flag_requires_an_actual_boolean(value: object) -> None:
    value = cast(bool, value)
    ledger = ResourceLedger()
    owner = ledger.register("canonical", "canonical_action")
    before = ledger.snapshot()
    with pytest.raises((TypeError, ValueError)):
        ledger.make_list(owner, append_only=value)
    assert ledger.snapshot() == before


@pytest.mark.parametrize("field", ("name", "role", "scope"))
@pytest.mark.parametrize("value", (True, 1.0))
def test_resource_metadata_cannot_alias_string_owner_names(
    field: str, value: bool | float
) -> None:
    ledger = ResourceLedger()
    before = ledger.snapshot()
    arguments = dict(name="valid", role="query_memo", scope="ENGINE_OWNED")
    arguments[field] = cast(str, value)
    with pytest.raises((TypeError, ValueError)):
        ledger.register(**cast(_OwnerArguments, arguments))
    assert ledger.snapshot() == before


@pytest.mark.parametrize("warm", (False, True))
@pytest.mark.parametrize("target", ("geometry", "index", "construct"))
def test_forged_equal_source_authority_rejects_before_any_retention(
    warm: bool, target: str
) -> None:
    source = ExactSource((1, 0), 2, blank=3, extent=2, alphabet_size=3)
    authority_source = ExactSource((1, 0), 2, blank=3, extent=2, alphabet_size=3)
    authority = OriginalSourceConstruction(authority_source)
    ledger = ResourceLedger()
    geometry = None
    if target == "construct" or warm:
        geometry = SourceGeometry(ledger, source, authority)
        if warm:
            geometry.span(source.digits, source.blank, 2)
    object.__setattr__(authority_source, "digits", (True, 0.0))
    assert authority_source == source  # The original equality-only admission bug.
    before = ledger.snapshot()
    with pytest.raises((TypeError, ValueError)):
        if target == "geometry":
            SourceGeometry(ledger, source, authority)
        elif target == "index":
            HashLifeBlockIndex(
                BaseBlockEffect(2),
                source.digits,
                logical_length=2,
                ledger=ledger,
                source_construction=authority,
                max_cache_entries=100_000,
            )
        else:
            authority.construct(
                cast("SourceGeometry", geometry), source.digits, source.blank, 2
            )
    assert ledger.snapshot() == before
    assert ledger.max_cache_entries is None


@pytest.mark.parametrize("value", BAD)
def test_original_authority_constructor_revalidates_forged_source(
    value: object,
) -> None:
    source = ExactSource((1,), 2, blank=2, extent=1)
    object.__setattr__(source, "digits", (value,))
    with pytest.raises((TypeError, ValueError)):
        OriginalSourceConstruction(source)


@pytest.mark.parametrize("value", BAD)
@pytest.mark.parametrize("family", ("reverse", "collatz"))
@pytest.mark.parametrize("field", ("seed", "steps", "budget"))
def test_public_constructor_aliases_reject_before_source_work(
    value: object, family: str, field: str, monkeypatch: pytest.MonkeyPatch
) -> None:
    value = cast(int, value)
    module = (
        "number_compiler.sequences.reverse_add.power"
        if family == "reverse"
        else "number_compiler.sequences.collatz.block_power"
    )
    monkeypatch.setattr(module + ".digits_lsd", forbidden)
    constructor = ReverseAddPoweredTerm if family == "reverse" else PoweredCollatzTerm
    arguments = dict(max_cache_entries=value) if field == "budget" else {}
    with pytest.raises((TypeError, ValueError)):
        constructor(
            value if field == "seed" else 1,
            value if field == "steps" else 0,
            **arguments,
        )


@pytest.mark.parametrize("value", BAD)
def test_standalone_collatz_power_rejects_step_aliases_before_compilation(
    value: object, monkeypatch: pytest.MonkeyPatch
) -> None:
    value = cast(int, value)
    monkeypatch.setattr(
        "number_compiler.sequences.collatz.block_power.LazyCompiler", forbidden
    )
    with pytest.raises((TypeError, ValueError)):
        power_collatz_physical_effect(value)


@pytest.mark.parametrize("value", BAD)
@pytest.mark.parametrize(
    "method",
    ("advance-state", "advance-symbol", "emit-left", "emit-symbol", "emit-right"),
)
def test_collatz_kernel_rejects_numeric_aliases_at_public_boundary(
    value: object, method: str
) -> None:
    value = cast(int, value)
    from number_compiler.arithmetic.contracts.block_effect import BoundarySide

    effect = CollatzPhysicalBlockEffect()
    with pytest.raises((TypeError, ValueError)):
        if method == "advance-state":
            effect.advance(BoundarySide.LEFT, value, 0)
        elif method == "advance-symbol":
            effect.advance(BoundarySide.LEFT, 0, value)
        elif method == "emit-left":
            effect.emit(value, 0, 0)
        elif method == "emit-symbol":
            effect.emit(0, value, 0)
        else:
            effect.emit(0, 0, value)


@pytest.mark.parametrize("method", ("initial", "universe", "advance"))
def test_collatz_kernel_rejects_integer_aliases_for_boundary_side(method: str) -> None:
    effect = CollatzPhysicalBlockEffect()
    with pytest.raises(TypeError, match="exact enum"):
        if method == "initial":
            effect.initial(True)  # type: ignore[arg-type]
        elif method == "universe":
            effect.boundary_universe(0)  # type: ignore[arg-type]
        else:
            effect.advance(0, 0, 0)  # type: ignore[arg-type]


@pytest.mark.parametrize("warm", (False, True))
@pytest.mark.parametrize("family", ("reverse", "collatz"))
def test_public_digit_aliases_reject_before_zero_or_warm_lookup(
    warm: bool, family: str, monkeypatch: pytest.MonkeyPatch
) -> None:
    constructor = ReverseAddPoweredTerm if family == "reverse" else PoweredCollatzTerm
    term = constructor(1, int(warm))
    if warm:
        term.digit(0)
    monkeypatch.setattr(constructor, "_point_index", forbidden)
    for value in BAD:
        before = term._ledger.snapshot()
        with pytest.raises(TypeError):
            term.digit(cast(int, value))
        assert term._ledger.snapshot() == before


@pytest.mark.parametrize("value", BAD)
@pytest.mark.parametrize("field", ("index", "seed", "base", "radix"))
def test_number_compiler_rejects_aliases_before_powered_construction(
    value: object, field: str, monkeypatch: pytest.MonkeyPatch
) -> None:
    value = cast(int, value)
    monkeypatch.setattr(
        "number_compiler.sequences.reverse_add.power.ReverseAddPoweredTerm", forbidden
    )
    monkeypatch.setattr("number_compiler.sequences.collatz.block_power.PoweredCollatzTerm", forbidden)
    kwargs = dict(seed=1, base=2, radix=2)
    if field != "index":
        kwargs[field] = value
    with pytest.raises((TypeError, ValueError)):
        NumberCompiler().project_nth(
            "collatz" if field == "radix" else "reverse-add",
            value if field == "index" else 0,
            **kwargs,
        )


def test_valid_zero_positive_sources_and_integer_coordinate_errors_remain_supported() -> (
    None
):
    for term, expected in (
        (ReverseAddPoweredTerm(0, 0), 0),
        (ReverseAddPoweredTerm(12, 1), 3),
        (PoweredCollatzTerm(1, 0), 1),
        (PoweredCollatzTerm(1, 1), 0),
    ):
        assert term.digit(0) == expected
        for coordinate in (-1, term.maximum_width + 1):
            with pytest.raises(IndexError):
                term.digit(coordinate)
