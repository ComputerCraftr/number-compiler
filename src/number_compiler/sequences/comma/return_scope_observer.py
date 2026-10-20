"""Explicit scope materialization for legacy comma return observers.

The powered quotient owns canonical MDD columns and occurrence labels. This
module converts those columns to congruence scopes only when a legacy scope
observer requests them; production template construction does not import it.
"""

from __future__ import annotations

from math import lcm
from typing import TypeAlias

from number_compiler.sequences.comma.return_mdd import (
    _mdd_cardinality,
    canonical_return_template,
)
from number_compiler.sequences.comma.return_scopes import (
    CanonicalReturnTemplate,
    ReturnColumnKey,
    ReturnMDDPartition,
    ReturnScope,
    WorkCharge,
    scope_column_key,
    scopes_from_key,
    validate_scopes,
)

ReturnPartition: TypeAlias = tuple[tuple[int, tuple[ReturnScope, ...]], ...]
TemplateColumn: TypeAlias = tuple[ReturnColumnKey, int, tuple[ReturnScope, ...]]


def _legacy_rebase_result(
    original_labels: tuple[int, ...],
    template: CanonicalReturnTemplate,
    charge: WorkCharge | None,
) -> tuple[
    ReturnPartition,
    int,
    int,
    int,
    tuple[ReturnColumnKey, ...],
    tuple[TemplateColumn, ...],
]:
    """Materialize historical scope observations at this explicit boundary."""
    forward_shift = (-template.return_shift) % 924
    template_columns = tuple(
        (key, label, scopes_from_key(key, charge))
        for key, label in zip(template.columns, template.labels, strict=True)
    )
    scopes_by_label = {label: scopes for _, label, scopes in template_columns}
    best_partition = tuple((label, scopes_by_label[label]) for label in original_labels)
    return (
        best_partition,
        forward_shift,
        template.candidate_count,
        template.shifted_nodes,
        template.columns,
        template_columns,
    )


def canonical_mdd_partition_rebase(
    partition: ReturnMDDPartition,
    *,
    charge: WorkCharge | None = None,
) -> tuple[
    ReturnPartition,
    int,
    int,
    int,
    tuple[ReturnColumnKey, ...],
    tuple[TemplateColumn, ...],
]:
    """Normalize an MDD partition and explicitly materialize all its scopes."""
    template = canonical_return_template(partition, charge=charge)
    return _legacy_rebase_result(
        tuple(label for label, _ in partition.columns), template, charge
    )


def canonical_partition_rebase(
    partition: ReturnPartition,
    *,
    charge: WorkCharge | None = None,
) -> tuple[
    ReturnPartition,
    int,
    int,
    int,
    tuple[ReturnColumnKey, ...],
    tuple[TemplateColumn, ...],
]:
    """Canonicalize caller-supplied scopes, for regression/audit consumers."""
    if type(partition) is not tuple or not partition:
        raise ValueError("comma return partition must be a nonempty tuple")
    columns: list[tuple[int, ReturnColumnKey]] = []
    labels: set[int] = set()
    cardinality_memo: dict[tuple[int, ReturnColumnKey], int] = {}
    period = 1
    for label, scopes in partition:
        if type(label) is not int or label in labels:
            raise ValueError("comma return labels must be distinct exact integers")
        labels.add(label)
        validated = validate_scopes(scopes)
        key = scope_column_key(validated, charge=charge)
        if _mdd_cardinality(key, charge, cardinality_memo) == 0:
            raise ValueError("comma output column must have nonempty admitted support")
        columns.append((label, key))
        for scope_period, _ in validated:
            period = lcm(period, scope_period)
    template = canonical_return_template(
        ReturnMDDPartition(period, tuple(columns)), charge=charge
    )
    return _legacy_rebase_result(tuple(label for label, _ in columns), template, charge)


__all__ = ["canonical_mdd_partition_rebase", "canonical_partition_rebase"]
