"""Consumer-relative residual transport with an exact factor-through gate.

Residual IDs are canonical finite functions of the admitted context. A
transition includes the next observation AND every updated context component.
The gate examines 19 primitive source cofactors, not a product of context
valuations. It cannot certify an unprovided whole-field continuation profile.
"""

from __future__ import annotations

from collections.abc import Mapping

from number_compiler.arithmetic.functions.finite_function_types import (
    BOOL,
    AtomSort,
    FinitePort,
    FunctionSignature,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.hashlife.interfaces.semantic_bits import (
    BitFunctionArena,
    FactoredFunctionID,
)
from number_compiler.resources.ledger import OwnedMemo
from number_compiler.resources.payload_contracts import PayloadAuditStoreBinding
from number_compiler.sequences.reverse_add.active_output import (
    CARRY_ACTION,
    PAIR,
    ReverseActiveOutputArena,
)


class ResidualSuccessorConflict(ValueError):
    """Two source atoms share a residual but require different successors."""

    def __init__(self, first: int, second: int) -> None:
        self.witness = first, second
        super().__init__(
            f"residual successor separates source symbols {first} and {second}"
        )


_EdgeKey = tuple[FactoredFunctionID, FactoredFunctionID, FinitePort, FactoredFunctionID]


class ReverseContextualResidualArena:
    """Source-free successor mappings for explicitly admitted local profiles."""

    def __init__(self, bits: BitFunctionArena) -> None:
        if type(bits) is not BitFunctionArena:
            raise TypeError("residuals require an owned finite-function arena")
        self.bits, self.ledger = bits, bits.ledger
        self.output = ReverseActiveOutputArena(bits)
        self.ledger.register_execution_root(self)
        owner = self.ledger.register(
            f"reverse-contextual-residual-{self.ledger.owner_count}", "query_memo"
        )
        self._successors: OwnedMemo[_EdgeKey, FactoredFunctionID] = OwnedMemo(
            self.ledger, owner, nodes_per_entry=8, evictable=True
        )
        self._audit_successors = self._successors._data
        from number_compiler.sequences.reverse_add.contextual_residual_audit import (
            audit_reverse_contextual_residual,
        )

        self.ledger.register_payload_audit_contract(
            self,
            "reverse_add",
            (PayloadAuditStoreBinding(owner, "_audit_successors", "query_memo"),),
            audit_reverse_contextual_residual,
        )

    def carry_prefix(
        self, domains: tuple[FactoredFunctionID, ...]
    ) -> FactoredFunctionID:
        """Derive physical carry-in from the existing domain actions and C0=0."""
        carry = self.bits.constant(FunctionSignature((), BOOL), 0)
        for domain in domains:
            carry = self.output.carry_apply(domain, carry)
        return carry

    def no_growth(
        self,
        symbol: FactoredFunctionID,
        forward_domains: tuple[FactoredFunctionID, ...],
        mirrored_domains: tuple[FactoredFunctionID, ...],
    ) -> FactoredFunctionID:
        return self.output.resolve(
            self.output.pair(
                symbol,
                self.carry_prefix(forward_domains),
                symbol,
                self.carry_prefix(mirrored_domains),
            )
        )

    def growth_edge(self, symbol: FactoredFunctionID) -> FactoredFunctionID:
        zero = self.bits.constant(FunctionSignature((), BOOL), 0)
        one = self.bits.constant(FunctionSignature((), PAIR), 1)
        return self.output.resolve(self.output.pair(symbol, zero, one, zero))

    def growth_interior(
        self,
        symbol: FactoredFunctionID,
        adjacent: FactoredFunctionID,
        forward_domains: tuple[FactoredFunctionID, ...],
        mirrored_domains: tuple[FactoredFunctionID, ...],
    ) -> FactoredFunctionID:
        return self.output.resolve(
            self.output.pair(
                symbol,
                self.carry_prefix(forward_domains),
                adjacent,
                self.carry_prefix(mirrored_domains),
            )
        )

    def domain(self, value: FactoredFunctionID) -> FactoredFunctionID:
        return self.output.carry_action(self.output.intern(value))

    def profile(
        self,
        observation: FactoredFunctionID,
        context: tuple[FactoredFunctionID, ...],
        admissible: FactoredFunctionID,
        *,
        frame: str,
    ) -> FactoredFunctionID:
        """Context, growth and alignment observations belong in the same record.

        Frame names are relative stencil roles, not absolute source positions.
        No independent carry-in is introduced; derive it with carry_prefix.
        """
        if frame not in ("same-coordinate", "growth-edge", "growth-interior"):
            raise ValueError("unknown reverse residual alignment")
        if self.bits.resolve(observation).signature.output != CARRY_ACTION:
            raise ValueError("carry residual requires a CarryFn observation")
        # Validate all components before any publication.
        if type(context) is not tuple or len(context) > 7:
            raise ValueError("residual profile has too many context components")
        fields = (observation, *context)
        for value in fields:
            self.bits.resolve(value)
        if self.bits.resolve(admissible).signature.output != BOOL:
            raise ValueError("residual profile requires an admissibility predicate")
        packed = self.bits.bundle(fields, name=f"reverse-residual:{frame}")
        return self.bits.restrict(packed, admissible)

    def pullback(
        self,
        target_profile: FactoredFunctionID,
        replacements: Mapping[PortVariable, FactoredFunctionID],
    ) -> FactoredFunctionID:
        """Substitute output and updated context functions together, then reduce."""
        return self.bits.substitute(target_profile, replacements)

    def _cofactors(
        self, function: FactoredFunctionID, source: FinitePort
    ) -> tuple[FactoredFunctionID, ...]:
        node = self.bits.resolve(function)
        if (
            type(source) is not FinitePort
            or source.cardinality != 19
            or source not in node.signature.inputs
        ):
            raise ValueError(
                "reverse residual requires its declared 19-value source port"
            )
        return tuple(
            self.bits.substitute(
                function,
                {
                    source.variable: self.bits.constant(
                        FunctionSignature((), PAIR), value
                    )
                },
            )
            for value in range(19)
        )

    def residual(
        self, profile: FactoredFunctionID, source: FinitePort, symbol: int
    ) -> FactoredFunctionID:
        if type(symbol) is not int or not 0 <= symbol < 19:
            raise ValueError("residual binding requires a primitive pair symbol")
        node = self.bits.resolve(profile)
        if (
            type(source) is not FinitePort
            or source.cardinality != 19
            or source not in node.signature.inputs
        ):
            raise ValueError("residual source port belongs to another profile")
        return self.bits.substitute(
            profile,
            {source.variable: self.bits.constant(FunctionSignature((), PAIR), symbol)},
        )

    def _rows(
        self,
        before: FactoredFunctionID,
        after: FactoredFunctionID,
        source: FinitePort,
    ) -> tuple[tuple[FactoredFunctionID, ...], tuple[FactoredFunctionID, ...]]:
        a, b = self.bits.resolve(before), self.bits.resolve(after)
        if a.signature.inputs != b.signature.inputs:
            raise ValueError(
                "successor must include the complete pulled-back context profile"
            )
        if a.valid != b.valid:
            raise ValueError(
                "successor changes the admitted domain; restrict its transported profile"
            )
        return self._cofactors(before, source), self._cofactors(after, source)

    def certify(
        self,
        before: FactoredFunctionID,
        after: FactoredFunctionID,
        source: FinitePort,
    ) -> int:
        """Publish only if successor, context AND admissibility factor through."""
        current, successor = self._rows(before, after, source)
        mapping: dict[FactoredFunctionID, tuple[int, FactoredFunctionID]] = {}
        for symbol, (a, b) in enumerate(zip(current, successor, strict=True)):
            old = mapping.setdefault(a, (symbol, b))
            if old[1] != b:
                self.ledger.bump("reverse_residual_successor_conflicts")
                raise ResidualSuccessorConflict(old[0], symbol)
        pending = {
            (before, after, source, a): b
            for a, (_, b) in mapping.items()
            if (before, after, source, a) not in self._successors
        }
        self.ledger.reserve(
            self._successors.owner, entries=len(pending), nodes=8 * len(pending)
        )
        self._successors._data.update(pending)
        self.ledger.bump("reverse_residual_transports_certified")
        return len(mapping)

    def advance(
        self,
        before: FactoredFunctionID,
        after: FactoredFunctionID,
        source: FinitePort,
        residual: FactoredFunctionID,
    ) -> FactoredFunctionID:
        """Advance from a residual ID; no source symbol, carry scan or output emit."""
        for function in (before, after, residual):
            self.bits.resolve(function)
        if type(source) is not FinitePort:
            raise TypeError("residual transport requires a typed source port")
        source.__post_init__()
        if (
            source.cardinality != 19
            or source not in self.bits.resolve(before).signature.inputs
        ):
            raise ValueError("residual transport has another source profile")
        found = self._successors.get((before, after, source, residual))
        if found is None:
            raise ValueError("no certified successor for this residual and context")
        self.bits.resolve(found)
        self.ledger.bump("reverse_residual_successor_hits")
        return found

    def refine(
        self,
        before: FactoredFunctionID,
        after: FactoredFunctionID,
        source: FinitePort,
    ) -> FactoredFunctionID:
        """Coarsest joint cofactor partition for this one declared successor.

        Refine before binding/discarding the source. It cannot recover a value
        from an already coarsened residual, and makes no infinite-horizon claim.
        """
        current, successor = self._rows(before, after, source)
        classes: dict[tuple[FactoredFunctionID, FactoredFunctionID], int] = {}
        labels = []
        for pair in zip(current, successor, strict=True):
            labels.append(classes.setdefault(pair, len(classes)))
        variable = self.bits.variable(
            self.bits.resolve(before).signature.inputs, source, PAIR
        )
        sort = AtomSort(
            f"reverse-residual-refinement:{before.local_id}:{after.local_id}",
            len(classes),
        )
        refined = self.bits.map_atoms(variable, sort, tuple(labels))
        refined = self.bits.restrict(refined, self.bits.domain_predicate(before))
        self.certify(refined, before, source)
        self.certify(refined, after, source)
        return refined

    def compile_chain(
        self, profiles: tuple[FactoredFunctionID, ...], source: FinitePort
    ) -> tuple[FactoredFunctionID, ...]:
        """Close a declared finite continuation by backward residual refinement.

        All profiles are pulled back to the same relative source/context ports.
        Refine before source binding; forward execution then needs only IDs.
        """
        if type(profiles) is not tuple or not 1 <= len(profiles) <= 64:
            raise ValueError("residual continuation requires one to 64 profiles")
        for profile in profiles:
            self._rows(profiles[0], profile, source)
        closed = [profiles[-1]]
        for profile in reversed(profiles[:-1]):
            closed.append(self.refine(profile, closed[-1], source))
        return tuple(reversed(closed))
