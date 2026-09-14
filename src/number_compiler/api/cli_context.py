"""One query owner for a term and its explicitly requested observations."""

from __future__ import annotations

from dataclasses import asdict
from typing import TYPE_CHECKING, Any

from number_compiler.api.cli_requests import QueryRequest
from number_compiler.api.cli_render import _metrics_json
from number_compiler.api.number_api import (
    AntihydraTermPayload, NumberCompiler, PoweredCollatzTermPayload,
    PoweredReverseAddTermPayload, ProjectedNumberTerm,
)
if TYPE_CHECKING:
    from number_compiler.api.cylinder_observation import CollatzObservationContext


def _events_context(seed: int, events: int, *, max_events: int,
                    max_digits: int) -> CollatzObservationContext:
    from number_compiler.api.cylinder_observation import CollatzObservationContext

    return CollatzObservationContext(seed, events, max_events=max_events, max_digits=max_digits)



class QueryContext:
    def __init__(self, request: QueryRequest, compiler: NumberCompiler) -> None:
        self.request = request
        self.compiler = compiler
        self._term: ProjectedNumberTerm | None = None
        self._events: CollatzObservationContext | None = None
        self._special: dict[str, Any] | None = None
        self._info: dict[str, Any] = {}

    def admit_observation_extents(self) -> None:
        """Reject descriptor bounds before any endpoint rendering or observation."""
        q = self.request
        if "mirror" in q.info:
            payload = self.term.payload
            assert isinstance(payload, PoweredReverseAddTermPayload)
            if payload.term.maximum_width > q.max_digits:
                raise ValueError("mirror target exceeds digit budget")
        if q.family == "collatz" and q.selector == "nth" and "clock" in q.info:
            collatz = self.term.payload
            assert isinstance(collatz, PoweredCollatzTermPayload)
            if q.index and collatz.term.maximum_width > q.max_digits:
                raise ValueError("physical clock target exceeds digit budget")

    @property
    def term(self) -> ProjectedNumberTerm:
        if self.request.selector != "nth":
            raise ValueError("event/certificate requests do not select an ordinary term")
        if self._term is None:
            q = self.request
            if q.family == "antihydra":
                self._term = self.compiler.project_nth(
                    q.family, q.index, max_steps=q.max_steps, max_state_bits=q.max_state_bits)
            elif q.family == "prime":
                self._term = self.compiler.project_nth(
                    q.family,
                    q.index,
                    start=q.start,
                    max_prime_states=q.max_prime_states,
                    max_prime_work=q.max_prime_work,
                    max_prime_stages=q.max_prime_stages,
                )
            else:
                self._term = self.compiler.project_nth(
                    q.family, q.index, seed=q.seed, base=q.base, radix=q.radix, start=q.start)
        return self._term

    def information(self) -> dict[str, Any]:
        # Metrics observe the finished query, regardless of --info ordering.
        for name in self.request.info:
            if name != "metrics" and name not in self._info:
                alias = ({"tape": "twisted", "twisted": "tape",
                          "mahler": "hensel", "hensel": "mahler"}.get(name)
                         if self.request.family == "antihydra" else None)
                if alias is not None and alias in self._info:
                    # These names select exactly the same demanded observation
                    # with the same parameters in this query. Reuse only the
                    # finished packet; it never authorizes a successor action.
                    packet = dict(self._info[alias])
                    packet["kind"] = name
                    payload = self.term.payload
                    assert isinstance(payload, AntihydraTermPayload)
                    payload.term.engine.count("query_observer_reuses")
                    if "work_counters" in packet:
                        packet["work_counters"] = dict(payload.term.ledger.counters)
                    self._info[name] = packet
                else:
                    self._info[name] = self._observe(name)
        if "metrics" in self.request.info and "metrics" not in self._info:
            self._info["metrics"] = _metrics_json(self.term)
        return {name: self._info[name] for name in self.request.info}

    def _observe(self, name: str) -> dict[str, Any]:
        q = self.request
        if q.family == "antihydra":
            return self._antihydra(name)
        if q.selector == "events":
            from number_compiler.api.cylinder_observation import observe_collatz

            assert q.seed is not None
            if self._events is None:
                self._events = _events_context(
                    q.seed, q.index, max_events=q.max_events, max_digits=q.max_digits)
            return observe_collatz(
                q.seed, q.index, kind=name, modulus=q.modulus, width=q.width,
                sign=q.sign, precision=q.precision, target=q.target, s_weight=q.s_weight,
                z_weight=q.z_weight, max_events=q.max_events, max_digits=q.max_digits,
                _context=self._events)
        if name == "clock" and q.family == "collatz":
            from number_compiler.api.cylinder_observation import observe_physical_clock

            payload = self.term.payload
            assert isinstance(payload, PoweredCollatzTermPayload)
            assert q.seed is not None
            return observe_physical_clock(q.seed, q.index, max_ticks=q.max_events,
                                          max_digits=q.max_digits, _term=payload.term)
        if name == "mirror":
            from number_compiler.api.cylinder_observation import observe_mirror

            reverse = self.term.payload
            assert isinstance(reverse, PoweredReverseAddTermPayload)
            result = observe_mirror(reverse.term.seed, q.index, base=q.base,
                                    first_width=q.width, max_digits=q.max_digits,
                                    _term=reverse.term)
            result["family"] = q.family
            return result
        if name == "root":
            from number_compiler.api.cylinder_observation import observe_etale_root

            assert q.defect is not None
            return observe_etale_root(q.family, q.index, q.defect, max_digits=q.max_digits)
        if name in {"primality", "factor"}:
            return self._special_observation(name)
        raise ValueError("observation has no admitted family handler")

    def _special_observation(self, name: str) -> dict[str, Any]:
        q = self.request
        if self._special is None:
            from number_compiler.api.sequence_compiler import CanonicalSequenceCompiler

            resolution = CanonicalSequenceCompiler().resolve_special_theorem(
                q.family, q.index, collect_etale_factor="factor" in q.info,
                max_factor_products=q.max_factor_products, max_candidate_bits=q.max_candidate_bits)
            failure = resolution.source_guard.failure_bit
            status = "unknown" if failure is None else "composite" if failure else "prime"
            self._special = {
                "family": q.family, "index": q.index, "status": status,
                "decided": resolution.decided, "method": resolution.projection_method,
                "factor_query_status": resolution.factor_query_status,
                "certificate": None if resolution.primality is None else asdict(resolution.primality),
                "factor_witness": resolution.factor_witness,
                "factor_target": {"family": q.family, "parameter": q.index},
                "factor_proof": "proper-coefficient-gcd" if resolution.factor_witness is not None else None,
                "factor_expression": None if resolution.composite_exponent_factor is None else
                    f"2^{resolution.composite_exponent_factor.exponent}-1",
                "etale_ring_multiplications": resolution.etale_ring_multiplications,
            }
        if name == "primality":
            return dict(self._special)
        packet = dict(self._special)
        packet["status"] = (
            "available" if packet["factor_witness"] is not None or packet["factor_expression"] is not None
            else "not_applicable" if packet["status"] == "prime" else "not_found")
        packet["scope"] = "conditional checked factor output; no factor found does not establish primality"
        return packet

    def _antihydra(self, name: str) -> dict[str, Any]:
        q = self.request
        payload = self.term.payload
        assert isinstance(payload, AntihydraTermPayload)
        if name in {"ledger", "modular"}:
            result = payload.term.result()
            centered_odd = (result.returns + result.balance) // 3
            value = ({"h": result.h, "ledger": result.balance, "minimum_ledger": result.minimum,
                      "first_failure_index": result.first_failure_index,
                      "centered_odd_events": centered_odd,
                      "odd_a_steps": result.returns-centered_odd} if name == "ledger" else
                     {"h": result.h % q.modulus, "modulus": q.modulus})
            return {"family": "antihydra", "kind": name, "value": value,
                    "scope": "total arithmetic iteration", "requested_returns": q.index,
                    "completed_returns": result.returns, "nonhalting_certified": False,
                    **payload.power_metrics()}
        from number_compiler.api.antihydra_observation import observe_run

        return observe_run(
            payload.term.physical_run(), kind=name, modulus=q.modulus, width=q.width,
            sign=q.sign, precision=q.precision, time_width=q.time_width,
            time_sign=q.time_sign, max_observer_terms=q.max_observer_terms)


def information_unresolved(info: dict[str, Any]) -> bool:
    return any(isinstance(packet, dict) and packet.get("status") in {"unknown", "unavailable"}
               for packet in info.values())
