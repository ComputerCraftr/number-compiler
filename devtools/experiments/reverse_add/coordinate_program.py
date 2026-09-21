"""Typed source-independent coordinate programs for reverse/add.

The program algebra records only the number of pair transitions and whether a
terminal digit normalization follows them.  It therefore canonicalizes every
parent before publication without flattening a temporal recipe.  Exact source
binding belongs to the shared higher field runtime, never to the program
identity.
"""

from __future__ import annotations

from collections.abc import Hashable, MutableMapping, MutableSequence
from dataclasses import dataclass

from number_compiler.arithmetic.contracts.canonical_payload import (
    validate_bounded_semantic_key,
)
from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
from number_compiler.hashlife.actions.field_actions import CoordinateOutputMorphismID
from number_compiler.resources.ledger import ResourceLedger


@dataclass(frozen=True, slots=True)
class ReverseCoordinateProgram:
    """Canonical temporal coordinate morphism, with no source observations."""

    base: int
    pair_steps: int
    normalized: bool
    atom: Hashable | None = None

    def __post_init__(self) -> None:
        if type(self.base) is not int or self.base < 2:
            raise ValueError("reverse coordinate program requires a radix")
        if type(self.pair_steps) is not int or self.pair_steps < 0:
            raise ValueError("reverse coordinate steps must be nonnegative")
        if type(self.normalized) is not bool:
            raise TypeError("reverse coordinate normalization must be Boolean")
        if self.atom is not None and (self.pair_steps or self.normalized):
            raise ValueError(
                "compatibility atoms cannot masquerade as executable programs"
            )

    @property
    def executable(self) -> bool:
        return self.atom is None


@dataclass(frozen=True, slots=True)
class ReverseCoordinateProgramMetrics:
    programs: int
    compose_requests: int
    compose_hits: int
    compose_evaluations: int
    executable_compilations: int


class ReverseCoordinateProgramArena:
    """Canonical typed output algebra shared by every source occurrence."""

    _KIND = "coordinate-output-morphism"

    def __init__(self, base: int, ledger: ResourceLedger) -> None:
        if type(base) is not int or base < 2 or type(ledger) is not ResourceLedger:
            raise ValueError(
                "reverse coordinate arena requires a radix and index ledger"
            )
        self.base, self.ledger = base, ledger
        self.owner = ArenaToken("reverse-coordinate-programs")
        self.ledger.register_execution_root(self)
        prefix = f"reverse-coordinate-{len(ledger.inventory())}"
        self._node_owner = ledger.register(prefix + "-nodes", "reverse_output_morphism")
        self._key_owner = ledger.register(
            prefix + "-interner", "reverse_output_interner"
        )
        self._compose_owner = ledger.register(
            prefix + "-compose", "reverse_output_composition"
        )
        self._nodes: MutableSequence[ReverseCoordinateProgram] = ledger.make_list(
            self._node_owner
        )
        self._keys: MutableMapping[ReverseCoordinateProgram, int] = ledger.make_dict(
            self._key_owner
        )
        self._compose: MutableMapping[
            tuple[CoordinateOutputMorphismID, CoordinateOutputMorphismID],
            CoordinateOutputMorphismID,
        ] = ledger.make_dict(self._compose_owner)
        ledger.register_container(
            self._compose_owner,
            self._compose,
            payloads=self._compose.items,
            composition_count=lambda: len(self._compose),
        )
        self.compose_requests = self.compose_hits = self.compose_evaluations = 0
        self.executable_compilations = 0
        self.identity = self.intern(ReverseCoordinateProgram(base, 0, False))
        self.primitive = self.intern(ReverseCoordinateProgram(base, 1, False))
        self.terminal = self.intern(ReverseCoordinateProgram(base, 0, True))

    def _handle(self, local_id: int) -> CoordinateOutputMorphismID:
        return CoordinateOutputMorphismID(self.owner, self._KIND, local_id)

    def resolve(
        self, reference: CoordinateOutputMorphismID
    ) -> ReverseCoordinateProgram:
        if type(reference) is not CoordinateOutputMorphismID:
            raise TypeError("expected a reverse coordinate-program ID")
        reference.validate(self.owner, self._KIND, size=len(self._nodes))
        return self._nodes[reference.local_id]

    def intern(self, program: ReverseCoordinateProgram) -> CoordinateOutputMorphismID:
        if type(program) is not ReverseCoordinateProgram or program.base != self.base:
            raise ValueError("coordinate program belongs to another reverse arena")
        program.__post_init__()
        found = self._keys.get(program)
        if found is not None:
            return self._handle(found)
        self.ledger.reserve_many(((self._node_owner, 1, 1), (self._key_owner, 1, 0)))
        local_id = len(self._nodes)
        self._nodes.append(program)
        self._keys[program] = local_id
        return self._handle(local_id)

    def atom(self, key: Hashable) -> CoordinateOutputMorphismID:
        if not isinstance(key, Hashable):
            raise TypeError(
                "compatibility output atoms require typed immutable semantics"
            )
        validate_bounded_semantic_key(key, max_units=256)
        return self.intern(ReverseCoordinateProgram(self.base, 0, False, key))

    def compose(
        self,
        before: CoordinateOutputMorphismID,
        after: CoordinateOutputMorphismID,
    ) -> CoordinateOutputMorphismID:
        first, second = self.resolve(before), self.resolve(after)
        self.compose_requests += 1
        key = before, after
        found = self._compose.get(key)
        if found is not None:
            self.compose_hits += 1
            return found
        if not first.executable or not second.executable:
            raise ValueError(
                "compatibility output atoms have no executable composition law"
            )
        if first.normalized and (second.pair_steps or second.normalized):
            raise ValueError(
                "pair evolution cannot follow terminal digit normalization"
            )
        result = self.intern(
            ReverseCoordinateProgram(
                self.base,
                first.pair_steps + second.pair_steps,
                first.normalized or second.normalized,
            )
        )
        self.ledger.reserve(self._compose_owner, entries=1)
        self._compose[key] = result
        self.compose_evaluations += 1
        return result

    def power(
        self, primitive: CoordinateOutputMorphismID, exponent: int
    ) -> CoordinateOutputMorphismID:
        node = self.resolve(primitive)
        if not node.executable or node.normalized:
            raise ValueError("only an executable pair program can be powered")
        if type(exponent) is not int or exponent < 0:
            raise ValueError("reverse coordinate exponent must be nonnegative")
        return self.intern(
            ReverseCoordinateProgram(
                self.base,
                node.pair_steps * exponent,
                False,
            )
        )

    def output(self, pair_steps: int) -> CoordinateOutputMorphismID:
        return self.compose(self.power(self.primitive, pair_steps), self.terminal)

    def metrics(self) -> ReverseCoordinateProgramMetrics:
        return ReverseCoordinateProgramMetrics(
            len(self._nodes),
            self.compose_requests,
            self.compose_hits,
            self.compose_evaluations,
            self.executable_compilations,
        )


__all__ = [
    "ReverseCoordinateProgram",
    "ReverseCoordinateProgramArena",
    "ReverseCoordinateProgramMetrics",
]
