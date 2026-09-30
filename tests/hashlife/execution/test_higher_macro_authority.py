from __future__ import annotations

from tests.support.assertions import assert_rejected_atomically

from typing import Never

import pytest

from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
from number_compiler.hashlife.execution.continuations.higher_macro_composer import (
    SourceBoundHigherMacro,
    _MacroBindingKey,
)
from number_compiler.hashlife.execution.field_images import SourceForestID
from tests.support.reverse_higher_runtime import (
    _fixture,
    _macro_composer,
    _compiled_macro_fixture,
)


def test_reverse_macro_probes_the_source_parent_before_descending(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    (
        _actions,
        primitive,
        semantics,
        _runtime,
        interfaces,
        compiler,
        sources,
        binding,
        outputs,
        composer,
        expected,
    ) = _compiled_macro_fixture((7, 18, 7, 19, 19, 19, 19, 19))
    visits = semantics.ledger.counters.get("source_leaf_visits", 0)

    def forbidden(_source: object) -> Never:
        raise AssertionError("warm source parent descended into its children")

    monkeypatch.setattr(composer, "_cell", forbidden)
    assert composer.compile(binding) == expected
    assert semantics.ledger.counters.get("source_leaf_visits", 0) == visits
    assert semantics.ledger.counters["higher_spatial_forest_early_hits"] == 1


def test_reverse_macro_rejects_foreign_source_before_warm_binding_probe() -> None:
    (
        _actions,
        primitive,
        semantics,
        _runtime,
        interfaces,
        compiler,
        sources,
        binding,
    ) = _fixture((7, 18, 7, 19, 19, 19, 19, 19))
    outputs, composer = _macro_composer(
        semantics, interfaces, sources, primitive, compiler
    )
    composer.compile(binding)

    class PoisonedBindings(dict[_MacroBindingKey, SourceBoundHigherMacro]):
        def get(self, _key: object, _default: object = None) -> Never:
            raise AssertionError("invalid source reached the warm binding cache")

    composer._bindings = PoisonedBindings(composer._bindings)
    foreign = SourceForestID(
        ArenaToken("foreign-source"), binding.kind, binding.local_id
    )
    assert_rejected_atomically(
        semantics.ledger,
        lambda: composer.compile(foreign),
        ValueError,
        match="different arena",
    )


@pytest.mark.parametrize(
    ("field", "replacement"),
    (
        ("action", "identity"),
        ("local_interface", None),
        ("left", "right"),
        ("symbol", "left"),
        ("right", "left"),
        ("blank", 19.0),
        ("kernel_digest", "foreign-kernel"),
        ("source_backed_temporal", 0),
        ("morphism_sort", None),
    ),
)
def test_spatial_warm_binding_rejects_changed_consumer_declaration(
    field: str, replacement: object, monkeypatch: pytest.MonkeyPatch
) -> None:
    (
        actions,
        primitive,
        semantics,
        _runtime,
        interfaces,
        compiler,
        sources,
        binding,
        outputs,
        composer,
        macro,
    ) = _compiled_macro_fixture((7, 18, 7, 19))
    changed = (
        actions.identity
        if replacement == "identity"
        else getattr(composer, replacement)
        if replacement in ("left", "right")
        else replacement
    )
    before = semantics.ledger.snapshot()
    with monkeypatch.context() as patch:
        patch.setattr(composer, field, changed)
        with pytest.raises(ValueError, match="declaration"):
            composer.compile(binding)
        assert semantics.ledger.snapshot() == before
    assert composer.compile(binding) is macro


def test_spatial_declaration_seal_blocks_coordinated_key_and_composer_mutation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    (
        _actions,
        primitive,
        semantics,
        _runtime,
        interfaces,
        compiler,
        sources,
        binding,
        outputs,
        composer,
        macro,
    ) = _compiled_macro_fixture((7, 18, 7, 19))
    with monkeypatch.context() as patch:
        patch.setattr(composer, "blank", 0)
        object.__setattr__(composer._declaration, "blank", 0)
        with pytest.raises(ValueError, match="declaration"):
            composer.compile(binding)
        with pytest.raises(ValueError, match="declaration"):
            composer.validate_binding(binding, macro)
        with pytest.raises(ValueError, match="declaration"):
            composer.bind_symbol_expression(
                semantics.symbol(primitive, 7), source_extent=1
            )
        with pytest.raises(ValueError, match="declaration"):
            composer.combine(macro, macro)


def test_spatial_binding_store_replacement_fails_before_warm_lookup() -> None:
    _actions, primitive, semantics, _runtime, interfaces, compiler, sources, binding = (
        _fixture((7, 18, 7, 19))
    )
    outputs, composer = _macro_composer(
        semantics, interfaces, sources, primitive, compiler
    )
    composer.compile(binding)
    composer._bindings = dict(composer._bindings)
    with pytest.raises(ValueError, match="authority"):
        composer.compile(binding)


def test_spatial_provider_binding_checks_source_action_and_output_together() -> None:
    (
        actions,
        primitive,
        semantics,
        _runtime,
        interfaces,
        compiler,
        sources,
        binding,
        outputs,
        composer,
        full,
    ) = _compiled_macro_fixture((7, 18, 7, 19, 19, 19, 19, 19))
    short_source = sources.forest(0, 4)
    short = composer.compile(short_source)
    assert full.output != short.output
    composer.validate_provider_binding(full.output, binding, primitive)
    composer.validate_provider_binding(short.output, short_source, primitive)
    with pytest.raises(ValueError, match="bound source output"):
        composer.validate_provider_binding(full.output, short_source, primitive)
    with pytest.raises(ValueError, match="consumer action"):
        composer.validate_provider_binding(full.output, binding, actions.identity)
