"""Authority tokens for source-checked ordered parity tape composition."""

from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING

from number_compiler.sequences.collatz.dyadic_terminal_cocycle import (
    DyadicTerminalFieldAction,
)

if TYPE_CHECKING:
    from number_compiler.sequences.collatz.parity_carry_tape import ParityCarryTape


_PARITY_BINDING_ISSUER = object()


@dataclass(frozen=True, slots=True)
class _ParityTapeShape:
    kind: str
    word: tuple[int, ...]
    child_ids: tuple[int, ...]
    repetitions: int
    steps: int
    odds: int
    concat_height: int
    traversal_depth: int


def _shallow_tape_shape(tape: ParityCarryTape) -> _ParityTapeShape:
    """Capture root fields needed to reject replacement/mutation without a walk."""
    return _ParityTapeShape(
        kind=tape.kind,
        word=tape.word,
        child_ids=tuple(id(child) for child in tape.children),
        repetitions=tape.repetitions,
        steps=tape.steps,
        odds=tape.odds,
        concat_height=tape.height,
        traversal_depth=tape.traversal_depth,
    )


@dataclass(frozen=True, slots=True, init=False)
class ParityTapeActionBinding:
    """Bind one already-certified tape root to its exact issued affine action.

    Issuance follows a cold fold or a checked producer path. Revalidation is
    constant-time and identity-sensitive, so warm adjacent joins detect a
    replaced tape without traversing its historical SLP.
    """

    tape: ParityCarryTape
    action: DyadicTerminalFieldAction
    action_coefficients: tuple[int, ...]
    tape_shape: _ParityTapeShape
    issuer: object

    @classmethod
    def _seal_after_validation(
        cls, tape: ParityCarryTape, action: DyadicTerminalFieldAction
    ) -> ParityTapeActionBinding:
        """Create the shared token shape after one of the checked paths succeeds."""
        binding = object.__new__(cls)
        for name, value in (
            ("tape", tape),
            ("action", action),
            ("action_coefficients", action.coefficient_snapshot()),
            ("tape_shape", _shallow_tape_shape(tape)),
            ("issuer", _PARITY_BINDING_ISSUER),
        ):
            object.__setattr__(binding, name, value)
        return binding

    @classmethod
    def issue_from_fold(
        cls, tape: ParityCarryTape, action: DyadicTerminalFieldAction
    ) -> ParityTapeActionBinding:
        from number_compiler.sequences.collatz.parity_carry_tape import (
            ParityCarryTape,
        )

        if (
            type(tape) is not ParityCarryTape
            or type(action) is not DyadicTerminalFieldAction
            or not action.producer_issued
            or action.steps != tape.steps
        ):
            raise ValueError("parity binding requires an issued same-span action")
        folded_action = tape.action()
        if folded_action.coefficient_snapshot() != action.coefficient_snapshot():
            raise ValueError("parity binding action does not match the full tape fold")
        return cls._seal_after_validation(tape, action)

    @classmethod
    def issue_from_composition(
        cls,
        tape: ParityCarryTape,
        action: DyadicTerminalFieldAction,
        composition: JoinedParityComposition,
    ) -> ParityTapeActionBinding:
        if type(composition) is not JoinedParityComposition:
            raise ValueError("composed parity binding requires its exact proof token")
        composition.verify(tape, action)
        return cls._seal_after_validation(tape, action)

    def verify(self, tape: ParityCarryTape, action: DyadicTerminalFieldAction) -> None:
        from number_compiler.sequences.collatz.parity_carry_tape import (
            ParityCarryTape,
        )

        if (
            type(self) is not ParityTapeActionBinding
            or self.issuer is not _PARITY_BINDING_ISSUER
            or type(tape) is not ParityCarryTape
            or self.tape is not tape
            or self.tape_shape != _shallow_tape_shape(tape)
            or type(action) is not DyadicTerminalFieldAction
            or self.action is not action
            or not action.producer_issued
            or action.steps != tape.steps
            or action.coefficient_snapshot() != self.action_coefficients
        ):
            raise ValueError("parity tape no longer matches its issued action")


_JOIN_TAPE_CERT_ISSUER = object()


@dataclass(frozen=True, slots=True, init=False)
class JoinedParityComposition:
    """Construction-only proof that a joined tape composes two checked parents."""

    root: ParityCarryTape
    left: ParityCarryTape
    right: ParityCarryTape
    left_binding: ParityTapeActionBinding
    right_binding: ParityTapeActionBinding
    root_shape: _ParityTapeShape
    issuer: object

    @classmethod
    def issue(
        cls,
        left: ParityCarryTape,
        left_binding: ParityTapeActionBinding,
        right: ParityCarryTape,
        right_binding: ParityTapeActionBinding,
    ) -> JoinedParityComposition:
        from number_compiler.sequences.collatz.parity_carry_tape import (
            ParityCarryTape,
        )

        if (
            type(left_binding) is not ParityTapeActionBinding
            or type(right_binding) is not ParityTapeActionBinding
        ):
            raise ValueError("joined parity token requires checked parent bindings")
        left_binding.verify(left, left_binding.action)
        right_binding.verify(right, right_binding.action)
        # The token itself constructs its root from these exact ordered
        # parents. Callers cannot pair arbitrary same-length/same-odds tape
        # roots with a separately supplied aggregate action.
        root = ParityCarryTape.sequence((left, right))
        proof = object.__new__(cls)
        for name, value in (
            ("root", root),
            ("left", left),
            ("right", right),
            ("left_binding", left_binding),
            ("right_binding", right_binding),
            ("root_shape", _shallow_tape_shape(root)),
            ("issuer", _JOIN_TAPE_CERT_ISSUER),
        ):
            object.__setattr__(proof, name, value)
        return proof

    def verify(
        self,
        root: ParityCarryTape,
        action: DyadicTerminalFieldAction,
    ) -> None:
        from number_compiler.sequences.collatz.parity_carry_tape import (
            ParityCarryTape,
        )

        if (
            type(self) is not JoinedParityComposition
            or self.issuer is not _JOIN_TAPE_CERT_ISSUER
            or self.root is not root
            or type(action) is not DyadicTerminalFieldAction
            or not action.producer_issued
            or type(self.left) is not ParityCarryTape
            or type(self.right) is not ParityCarryTape
            or self.root_shape != _shallow_tape_shape(root)
            or root.steps != self.left.steps + self.right.steps
            or root.odds != self.left.odds + self.right.odds
        ):
            raise ValueError("composed parity tape lost its issued root structure")
        self.left_binding.verify(self.left, self.left_binding.action)
        self.right_binding.verify(self.right, self.right_binding.action)
        if (
            self.left_binding.action.then(
                self.right_binding.action
            ).coefficient_snapshot()
            != action.coefficient_snapshot()
        ):
            raise ValueError("composed parity tape differs from its issued action")


__all__ = ["JoinedParityComposition", "ParityTapeActionBinding"]
