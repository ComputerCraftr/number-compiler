"""Ownership inventory starts from live objects independently of registration."""

from __future__ import annotations

import ast
import gc
import weakref
from collections.abc import Callable, Iterator, Mapping, MutableSequence
from types import MappingProxyType, SimpleNamespace
from typing import Any, ClassVar

import pytest

from devtools.paths import repository_root
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.ownership import audit_execution_ownership
from number_compiler.resources.stores import LedgerDict
from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm
from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm
from tests.support.production_ast import ProductionASTGraph


@pytest.mark.parametrize("factory", [dict, list, set])
def test_unregistered_mutable_attribute_is_visible_without_any_callback(
    factory: Callable[[], object],
) -> None:
    ledger = ResourceLedger()
    root = SimpleOwner()
    ledger.register_execution_root(root)
    root.hidden = factory()
    report = audit_execution_ownership(ledger)
    assert report.unregistered_containers == 1
    assert report.violations[0].path.endswith(".hidden")


class SimpleOwner:
    hidden: object
    callback: object
    memo: LedgerDict[object, object]
    proxy: Mapping[object, object]
    suspended: Iterator[object]
    weak_helper: object
    _data: object


def test_helper_return_nested_object_and_closure_do_not_hide_unowned_stores() -> None:
    ledger = ResourceLedger()
    root = SimpleOwner()
    ledger.register_execution_root(root)

    def helper() -> list[int]:
        return [1]

    root.hidden = SimpleNamespace(returned=helper())
    captured = {"future": 1}
    root.callback = lambda: captured.get("future")
    report = audit_execution_ownership(ledger)
    assert report.unregistered_containers == 2
    assert any("returned" in item.path for item in report.violations)
    assert any("closure" in item.path for item in report.violations)


def test_registered_bare_store_still_fails_factory_provenance() -> None:
    ledger = ResourceLedger()
    root = SimpleOwner()
    root.hidden = {}
    ledger.register_execution_root(root)
    ledger.register_container(ledger.register("manual", "query_memo"), root.hidden)
    report = audit_execution_ownership(ledger)
    assert report.unregistered_containers == 1
    assert "factory" in report.violations[0].reason


def test_factory_store_passes_and_proxy_values_are_traversed() -> None:
    ledger = ResourceLedger()
    root = SimpleOwner()
    ledger.register_execution_root(root)
    owner = ledger.register("query", "query_memo")
    root.memo = ledger.make_dict(owner)
    ledger.reserve(owner, entries=1)
    root.memo[0] = "bounded summary"
    assert audit_execution_ownership(ledger).unregistered_containers == 0
    root.proxy = MappingProxyType(root.memo)
    assert audit_execution_ownership(ledger).unregistered_containers == 0
    root.proxy = MappingProxyType({"nested": SimpleNamespace(hidden=[])})
    report = audit_execution_ownership(ledger)
    assert report.unregistered_containers == 2
    assert any(item.path.endswith(".hidden") for item in report.violations)


def test_cached_callable_and_class_level_store_are_not_ownership_exceptions() -> None:
    from functools import lru_cache

    class Owner:
        hidden: ClassVar[dict[object, object]] = {}
        method: object
        function: object

    Owner.method = lru_cache()(lambda self, value: value)
    root = Owner()
    root.function = lru_cache()(lambda value: value)
    ledger = ResourceLedger()
    ledger.register_execution_root(root)
    assert audit_execution_ownership(ledger).unregistered_containers == 3


def test_execution_root_registry_is_weak_and_factory_writes_are_seen() -> None:
    ledger = ResourceLedger()
    root = SimpleOwner()
    ledger.register_execution_root(root)
    saved = weakref.ref(root)
    del root
    gc.collect()
    assert saved() is None and tuple(ledger.iter_execution_roots()) == ()


def test_collatz_source_image_graph_is_collectable_after_term_lifetime() -> None:
    term = PoweredCollatzTerm(27, 4)
    term.digit(0)
    ledger = term._ledger
    workspace = term._source_image()
    scheduler = workspace.scheduler
    saved = tuple(
        weakref.ref(item)
        for item in (
            ledger,
            workspace,
            scheduler,
        )
    )

    del scheduler, workspace, term, ledger
    gc.collect()

    assert all(reference() is None for reference in saved)


@pytest.mark.parametrize("kind", ["reverse", "collatz"])
def test_actual_public_graph_is_factory_owned_before_and_after_compilation(
    kind: str,
) -> None:
    term = (
        ReverseAddPoweredTerm(196, 4)
        if kind == "reverse"
        else PoweredCollatzTerm(27, 4)
    )
    before = audit_execution_ownership(term._ledger)
    assert before.roots >= 1
    assert not before.violations
    term.digit(0)
    after = audit_execution_ownership(term._ledger)
    assert after.observed_mutable_containers > before.observed_mutable_containers
    assert not after.violations
    # This store is deliberately absent from all ledger payload callbacks.
    workspace = (
        term._source_workspace()
        if isinstance(term, ReverseAddPoweredTerm)
        else term._source_image()
    )
    workspace.__setattr__("hidden_late_cache", {"unaccounted": 1})
    assert audit_execution_ownership(term._ledger).unregistered_containers == 1


def test_reverse_source_workspace_cleans_later_owners_after_failed_dispose(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    term = ReverseAddPoweredTerm(196, 2)
    term.digit(0)
    workspace = term._source_workspace()
    adapter_type = type(workspace.adapter)
    original = adapter_type.dispose

    def fail_after_dispose(adapter: Any) -> None:
        original(adapter)
        raise RuntimeError("injected adapter close failure")

    monkeypatch.setattr(adapter_type, "dispose", fail_after_dispose)
    with pytest.raises(RuntimeError, match="injected adapter close failure"):
        workspace.dispose()
    with pytest.raises(ValueError, match="disposed reverse action arena"):
        workspace.actions.node(workspace.root_action)
    assert all(
        account.disposed
        for account in term._ledger.inventory()
        if account.name.startswith("reverse-source-")
    )


_BARE_CONSTRUCTORS = {
    "dict",
    "list",
    "set",
    "OrderedDict",
    "defaultdict",
    "WeakKeyDictionary",
    "WeakValueDictionary",
}
_RUNTIME_CACHE_DECORATORS = {"cache", "lru_cache", "cached_property"}


def _name(expression: ast.expr) -> str:
    if isinstance(expression, ast.Name):
        return expression.id
    if isinstance(expression, ast.Attribute):
        return expression.attr
    return ""


def _persistent_store_violations(tree: ast.Module, classes: set[str]) -> list[int]:
    if not classes:
        return []
    violations = []
    for cls in ast.walk(tree):
        if not isinstance(cls, ast.ClassDef) or cls.name not in classes:
            continue
        for method in cls.body:
            if isinstance(method, (ast.FunctionDef, ast.AsyncFunctionDef)):
                for decorator in method.decorator_list:
                    target = (
                        decorator.func if isinstance(decorator, ast.Call) else decorator
                    )
                    if _name(target) in _RUNTIME_CACHE_DECORATORS:
                        violations.append(decorator.lineno)
            for node in ast.walk(method):
                if isinstance(node, ast.Assign):
                    targets, value = node.targets, node.value
                elif isinstance(node, ast.AnnAssign) and node.value is not None:
                    targets, value = [node.target], node.value
                else:
                    continue
                persistent = any(
                    isinstance(target, ast.Attribute)
                    and isinstance(target.value, ast.Name)
                    and target.value.id in ("self", "cls")
                    for assignment in targets
                    for target in ast.walk(assignment)
                )
                persistent |= node in cls.body
                if not persistent:
                    continue
                if any(
                    isinstance(
                        part,
                        (
                            ast.Dict,
                            ast.List,
                            ast.Set,
                            ast.DictComp,
                            ast.ListComp,
                            ast.SetComp,
                        ),
                    )
                    or isinstance(part, ast.Call)
                    and _name(part.func) in _BARE_CONSTRUCTORS
                    for part in ast.walk(value)
                ):
                    violations.append(node.lineno)
    return violations


def test_structural_gate_distinguishes_retained_stores_from_transient_locals() -> None:
    valid_tree = ast.parse(
        "class Owner:\n"
        " def f(self):\n"
        "  transient = {}\n"
        "  self.memo = ledger.make_dict(owner)\n"
    )
    assert _persistent_store_violations(valid_tree, {"Owner"}) == []
    direct_store_tree = ast.parse("class Owner:\n def f(self):\n  self.memo = {}\n")
    assert _persistent_store_violations(direct_store_tree, {"Owner"})
    cached_method_tree = ast.parse(
        "class Owner:\n @lru_cache(None)\n def f(self): pass\n"
    )
    assert _persistent_store_violations(cached_method_tree, {"Owner"})


def test_execution_owners_allocate_persistent_stores_only_through_factories(
    production_ast_graph: ProductionASTGraph,
) -> None:
    root = repository_root() / "src/number_compiler"
    violations: dict[str, list[int]] = {}
    examined = 0
    for source_root in (root, repository_root() / "devtools" / "verification"):
        for path, tree in production_ast_graph.under(source_root).items():
            classes = set()
            for node in ast.walk(tree):
                if not isinstance(node, ast.ClassDef):
                    continue
                constructors = [
                    child
                    for child in node.body
                    if isinstance(child, ast.FunctionDef) and child.name == "__init__"
                ]
                if any(
                    isinstance(call, ast.Call)
                    and isinstance(call.func, ast.Attribute)
                    and call.func.attr
                    in {
                        "register",
                        "register_execution_root",
                        "make_dict",
                        "make_list",
                        "make_set",
                    }
                    for constructor in constructors
                    for call in ast.walk(constructor)
                ):
                    classes.add(node.name)
            examined += len(classes)
            rows = _persistent_store_violations(tree, classes)
            if rows:
                violations[str(path.relative_to(repository_root()))] = rows
    assert examined > 0
    assert not violations, violations


def test_direct_store_class_construction_cannot_forge_factory_provenance() -> None:
    from number_compiler.resources.stores import LedgerDict

    ledger = ResourceLedger()
    root = SimpleOwner()
    ledger.register_execution_root(root)
    owner = ledger.register("forged", "query_memo")
    root.memo = LedgerDict(ledger, owner, 0)
    ledger.register_container(owner, root.memo, payloads=root.memo.items)
    report = audit_execution_ownership(ledger)
    # Neither the forged wrapper nor its backing store earns an exemption.
    assert report.unregistered_containers == 2
    assert "factory" in report.violations[0].reason


def test_read_only_proxy_cannot_disguise_an_externally_mutable_cache() -> None:
    ledger = ResourceLedger()
    root = SimpleOwner()
    ledger.register_execution_root(root)
    external: dict[object, object] = {"cached": 1}
    root.proxy = MappingProxyType(external)
    before = audit_execution_ownership(ledger)
    assert before.unregistered_containers == 1
    assert before.violations[0].path.endswith(".backing")
    external["warmed"] = 2
    assert root.proxy["warmed"] == 2
    assert audit_execution_ownership(ledger).unregistered_containers == 1
    proxy_tree = ast.parse(
        "class Owner:\n def f(self):\n  self.memo = MappingProxyType({})\n"
    )
    assert _persistent_store_violations(proxy_tree, {"Owner"})


def test_builtin_callback_and_partial_cannot_hide_mutable_stores() -> None:
    from functools import partial

    root = SimpleOwner()
    ledger = ResourceLedger()
    ledger.register_execution_root(root)
    hidden = {0: 1}
    root.callback = hidden.get
    assert audit_execution_ownership(ledger).unregistered_containers == 1
    root.callback = partial(hidden.get, 0)
    report = audit_execution_ownership(ledger)
    assert any(item.path.endswith(".__self__") for item in report.violations)


def test_suspended_generator_and_weak_helper_do_not_hide_mutable_stores() -> None:
    root = SimpleOwner()
    ledger = ResourceLedger()
    ledger.register_execution_root(root)
    helper = SimpleNamespace(hidden=[])

    def suspended(value: object) -> Iterator[object]:
        yield value

    root.suspended = suspended(helper)
    assert audit_execution_ownership(ledger).unregistered_containers == 1
    weak_helper = SimpleOwner()
    weak_helper.hidden = {}
    root.weak_helper = weakref.ref(weak_helper)
    assert audit_execution_ownership(ledger).unregistered_containers == 2


def test_private_data_name_is_not_a_general_ownership_exemption() -> None:
    ledger = ResourceLedger()
    root = SimpleOwner()
    root._data = {}
    ledger.register_execution_root(root)
    report = audit_execution_ownership(ledger)
    assert report.unregistered_containers == 1
    assert report.violations[0].path.endswith("._data")


def test_ledger_unknown_attributes_and_callback_only_caches_are_audited() -> None:
    ledger = ResourceLedger()
    ledger.__setattr__("hidden_cache", {})
    assert audit_execution_ownership(ledger).unregistered_containers == 1
    delattr(ledger, "hidden_cache")
    owner = ledger.register("callback", "query_memo")
    memo: LedgerDict[object, object] = ledger.make_dict(owner)
    captured = {"invisible": 1}
    ledger.register_container(owner, memo, payloads=lambda: captured.values())
    report = audit_execution_ownership(ledger)
    assert report.unregistered_containers == 1
    assert "closure" in report.violations[0].path


def test_factory_sequence_contents_remain_audited_with_private_backing_exempt() -> None:
    ledger = ResourceLedger()
    owner = ledger.register("sequence", "action_program")
    values: MutableSequence[dict[str, int]] = ledger.make_list(owner)
    ledger.reserve(owner, entries=1, nodes=1)
    values.append({"hidden": 1})
    report = audit_execution_ownership(ledger)
    assert report.unregistered_containers == 1
    assert report.violations[0].path.endswith("[0]")
