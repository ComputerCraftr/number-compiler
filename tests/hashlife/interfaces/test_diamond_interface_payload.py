"""Universal admission certificates are proven against actual primitive domains."""

from dataclasses import replace

import pytest

from number_compiler.hashlife.interfaces.diamond_boundary_expr import (
    StateSort,
    SymbolSort,
)
from number_compiler.hashlife.interfaces.diamond_finite_admission import (
    FiniteInterfaceCertificate,
)
from number_compiler.resources.metric_collection import collect_ledger_metrics
from number_compiler.resources.stores import LedgerList
from tests.support.diamond_continuation_payload import populated


@pytest.mark.parametrize("symbol_target", (False, True))
def test_actual_interface_certificate_and_constant_function_are_valid(
    symbol_target: bool,
) -> None:
    runtime, action, _, _, _, _ = populated()
    source = StateSort(action, 0)
    target = runtime.higher.expressions.symbol_sort(action) if symbol_target else source
    domain = (
        target.blank + 1
        if isinstance(target, SymbolSort)
        else runtime.kernel(action).left_count
    )
    function = runtime.kernels.constant(domain, 0)
    runtime.primitive_continuations.admission.validate(source, target, function)
    before = runtime.ledger.snapshot()
    assert collect_ledger_metrics(runtime.ledger).representation_boundary_complete == 1
    assert runtime.ledger.snapshot() == before


@pytest.mark.parametrize(
    "failure",
    ("wrong-size", "boolean-size", "unallocated-function", "unowned-certificate"),
)
def test_interface_record_cannot_self_certify_its_domain_or_owner(failure: str) -> None:
    runtime, _, _, _, _, _ = populated()
    admission = runtime.primitive_continuations.admission
    key, certificate = next(iter(admission.memo.items()))
    if failure == "wrong-size":
        admission.memo[key] = replace(
            certificate, input_size=certificate.input_size + 1
        )
    elif failure == "boolean-size":
        admission.memo[key] = replace(certificate, output_size=True)
    elif failure == "unallocated-function":
        function = replace(key.function, local_id=len(runtime.kernels._expressions))
        admission.memo[replace(key, function=function)] = certificate
    else:
        owner = runtime.ledger.register("fake-interface-certificate", "query_memo")
        records: LedgerList[object]
        records = runtime.ledger.make_list(owner)
        runtime.ledger.reserve(owner, entries=1, nodes=1)
        records.append(
            FiniteInterfaceCertificate(certificate.input_size, certificate.output_size)
        )
    before = runtime.ledger.snapshot()
    assert collect_ledger_metrics(runtime.ledger).forbidden_future_payloads > 0
    assert runtime.ledger.snapshot() == before
