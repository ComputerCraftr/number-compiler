"""Source-authoritative Mahler future cylinders and joint 2/5/10 carry ports.

This is a *finite-word* exact quotient, not an all-time Z-number proof.
An action owns the original integer-source residue and the complete half-open
fractional guard.  A two-carry NC15 Boolean counter is a demanded interior
port of that same authenticated action, never an independent selector.

D' = (3**L * D + J) / 2**L;  t' = (3**L * t - J) / 2**L.
The high fiber k in D = residue + 2**L*k is persistent across CONCAT/REPEAT.
"""

from __future__ import annotations

from collections.abc import Iterator
from dataclasses import dataclass, field
from typing import Final, cast
from weakref import ReferenceType, ref

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.contracts.input_validation import is_exact_object_tuple
from number_compiler.arithmetic.fields.boolean_counter import (
    BinaryBooleanCarryAction,
)
from number_compiler.arithmetic.fields.consumer_pullback import (
    ExactRational as Q,
)
from number_compiler.arithmetic.fields.consumer_pullback import (
    HalfOpenInterval as Interval,
)
from number_compiler.arithmetic.fields.integer_congruence import exact_modular_power
from number_compiler.arithmetic.fields.morphism_core import balanced_fold, binary_power
from number_compiler.arithmetic.fields.two_adic import v2_positive
from number_compiler.arithmetic.fields.walsh import WalshH5
from number_compiler.sequences.antihydra.mahler_source_actions import (
    MAX_MAHLER_SOURCE_EXTENT,
    MahlerSourceBoundSafetyAction,
)

_ZERO, _HALF, _THIRD = Q(0), Q(1, 2), Q(1, 3)
MAHLER_JOINT_FUTURE_KIND: Final[str] = "mahler-joint-future-v1"
_MAHLER_WINDOW_ISSUER = object()


@dataclass(frozen=True, slots=True)
class _MahlerWindowProvenance:
    issuer: object
    record: ReferenceType[object]
    snapshot: tuple[object, ...]


@dataclass(frozen=True, slots=True, init=False, weakref_slot=True)
class MahlerJointInteriorWindow:
    """One *concrete source*-authenticated next-bit and multiradix window.

    The counter covers 3D+epsilon in `bits+1` LSD positions, so its low
    `bits` emitted, shifted positions give the exact next integer suffix.
    The modulo-five arm is transported through inverse(2, 5**places).
    CRT then reconstructs the corresponding base-ten interior suffix.
    """

    source: int
    source_endpoint: int
    epsilon: int
    next_source: int
    bits: int
    decimal_places: int
    source_binary: int
    addend_binary: int
    emitted_binary: int
    next_binary: int
    next_five: int
    next_decimal: int
    source_decimal: int
    binary_difference_borrows: int
    decimal_difference_borrows: int
    generate_mask: int
    propagate_mask: int
    xor_mask: int
    counter: BinaryBooleanCarryAction
    fraction_authenticated: bool
    next_fraction: Q | None
    next_branch_safe: bool | None
    _issuer: object = field(init=False, repr=False, compare=False)

    def __init__(self) -> None:
        raise TypeError("Mahler interior windows require checked source issuance")

    @classmethod
    def from_checked_source_window(
        cls,
        source: int,
        source_endpoint: int,
        epsilon: int,
        next_source: int,
        bits: int,
        decimal_places: int,
        source_binary: int,
        addend_binary: int,
        emitted_binary: int,
        next_binary: int,
        next_five: int,
        next_decimal: int,
        source_decimal: int,
        binary_difference_borrows: int,
        decimal_difference_borrows: int,
        generate_mask: int,
        propagate_mask: int,
        xor_mask: int,
        counter: BinaryBooleanCarryAction,
        fraction_authenticated: bool,
        next_fraction: Q | None,
        next_branch_safe: bool | None,
    ) -> MahlerJointInteriorWindow:
        """Issue the immutable output of the checked source-window builder.

        The caller must first authenticate the integer source and establish
        each radix/carry equation represented by these fields.
        """
        result = object.__new__(cls)
        values = (
            source,
            source_endpoint,
            epsilon,
            next_source,
            bits,
            decimal_places,
            source_binary,
            addend_binary,
            emitted_binary,
            next_binary,
            next_five,
            next_decimal,
            source_decimal,
            binary_difference_borrows,
            decimal_difference_borrows,
            generate_mask,
            propagate_mask,
            xor_mask,
            counter,
            fraction_authenticated,
            next_fraction,
            next_branch_safe,
        )
        names = (
            "source",
            "source_endpoint",
            "epsilon",
            "next_source",
            "bits",
            "decimal_places",
            "source_binary",
            "addend_binary",
            "emitted_binary",
            "next_binary",
            "next_five",
            "next_decimal",
            "source_decimal",
            "binary_difference_borrows",
            "decimal_difference_borrows",
            "generate_mask",
            "propagate_mask",
            "xor_mask",
            "counter",
            "fraction_authenticated",
            "next_fraction",
            "next_branch_safe",
        )
        for name, value in zip(names, values, strict=True):
            object.__setattr__(result, name, value)
        # ``source_window`` is the canonical checked builder. Retrieval
        # authenticates this complete typed publication snapshot and does not
        # replay its finite carry/CRT construction on every warm hit.
        object.__setattr__(
            result,
            "_issuer",
            _MahlerWindowProvenance(
                _MAHLER_WINDOW_ISSUER, ref(result), result._snapshot()
            ),
        )
        result.verify_issued()
        return result

    def _snapshot(self) -> tuple[object, ...]:
        def scalar(value: object) -> tuple[object, ...]:
            return type(value), value

        def scalar_tuple(value: object) -> tuple[object, ...]:
            if not is_exact_object_tuple(value):
                return (type(value),)
            return type(value), tuple(scalar(item) for item in value)

        def harmonic(value: object) -> tuple[object, ...]:
            if type(value) is not WalshH5:
                return (type(value),)
            return (
                type(value),
                scalar(value.length_mod6),
                scalar(value.phi2),
                scalar(value.phi3_a),
                scalar(value.phi3_b),
            )

        fraction = self.next_fraction
        if fraction is None:
            fraction_snapshot = scalar(fraction)
        elif type(fraction) is Q:
            fraction_snapshot = (
                type(fraction),
                scalar(fraction.numerator),
                scalar(fraction.denominator),
            )
        else:
            fraction_snapshot = (type(fraction),)

        counter = self.counter
        counter_snapshot: tuple[object, ...]
        if type(counter) is not BinaryBooleanCarryAction:
            counter_snapshot = (type(counter),)
        else:
            counter_structure = counter.structural_snapshot()
            harmonics = counter.harmonics
            harmonic_snapshot = (
                (type(harmonics), tuple(harmonic(item) for item in harmonics))
                if type(harmonics) is tuple
                else (type(harmonics),)
            )
            counter_snapshot = (
                type(counter),
                scalar(counter.modulus),
                scalar(counter.length),
                scalar_tuple(counter.next_carries),
                scalar_tuple(counter.deltas),
                harmonic_snapshot,
                scalar_tuple(counter_structure[5]),
                scalar_tuple(counter_structure[6]),
            )
        return (
            type(self),
            *(
                scalar(getattr(self, name))
                for name in (
                    "source",
                    "source_endpoint",
                    "epsilon",
                    "next_source",
                    "bits",
                    "decimal_places",
                    "source_binary",
                    "addend_binary",
                    "emitted_binary",
                    "next_binary",
                    "next_five",
                    "next_decimal",
                    "source_decimal",
                    "binary_difference_borrows",
                    "decimal_difference_borrows",
                    "generate_mask",
                    "propagate_mask",
                    "xor_mask",
                    "fraction_authenticated",
                    "next_branch_safe",
                )
            ),
            fraction_snapshot,
            (id(counter), counter_snapshot),
        )

    def verify_issued(self) -> None:
        """Authenticate this publication without replaying its finite proof."""
        issuer = getattr(self, "_issuer", None)
        if (
            type(self) is not MahlerJointInteriorWindow
            or type(issuer) is not _MahlerWindowProvenance
            or issuer.issuer is not _MAHLER_WINDOW_ISSUER
            or issuer.record() is not self
        ):
            raise ValueError("Mahler interior window has no source issuer")
        # Every scalar in this frozen descriptor is paired with its exact
        # ``type`` tag, so tuple equality is already type-sensitive here.
        if issuer.snapshot != self._snapshot():
            raise ValueError("Mahler interior window publication seal is invalid")


@dataclass(frozen=True, slots=True)
class MahlerJointFiberWindow:
    """Finite high-fiber cylinder that fixes all demanded interior outputs.

    With D = residue + 2**extent*k, all k congruent to `fiber_residue`
    modulo `fiber_modulus` have identical successor binary/carry/CRT windows.
    This is a demanded-precision quotient, not a global finite ActionID.
    """

    fiber_residue: int
    fiber_modulus: int
    window: MahlerJointInteriorWindow


@dataclass(frozen=True, slots=True)
class MahlerJointSuccessor:
    epsilon: int
    high_fiber_parity: int
    action: MahlerJointFutureAction


@dataclass(frozen=True, slots=True)
class MahlerJointFutureAction:
    """Exact finite future language for all source fibers and safe fractions.

    Equal identifiers are sound only for the *full* action including source
    residue, guard, innovation and min-plus action; no fixed-digit observation
    alone is promoted into a global future Moore class.
    """

    extent: int = 0
    residue: int = 0
    innovation: int = 0
    guard: Interval = field(default_factory=Interval)
    safety: MahlerSourceBoundSafetyAction = field(
        default_factory=MahlerSourceBoundSafetyAction
    )
    _gain: int | None = field(default=None, init=False, repr=False)

    def __post_init__(self) -> None:
        if type(self.extent) is not int or self.extent < 0:
            raise ValueError("negative/nonintegral Mahler source extent")
        if self.extent > MAX_MAHLER_SOURCE_EXTENT:
            raise BlockContextBudgetExceeded("Mahler source extent exceeds hard limit")
        if type(self.residue) is not int or type(self.innovation) is not int:
            raise TypeError("Mahler source coefficients must be integers")
        if type(self.guard) is not Interval:
            raise TypeError("Mahler guard must be an exact interval")
        if type(self.safety) is not MahlerSourceBoundSafetyAction:
            raise TypeError("Mahler min-plus action must be exact")
        self.safety.__post_init__()
        q = 1 << self.extent
        p = self._gain
        if p is None:
            p = 3**self.extent
            object.__setattr__(self, "_gain", p)
        elif type(p) is not int or p < q:
            raise ValueError("Mahler source gain is not a positive integer multiplier")
        if (
            not 0 <= self.residue < q
            or not 0 <= self.innovation <= p - q
            or (p * self.residue + self.innovation) % q
        ):
            raise ValueError("Mahler source cylinder and affine action disagree")
        if (
            self.safety.extent != self.extent
            or self.safety.offset_hat != -12 * self.innovation
        ):
            raise ValueError("Mahler source and safety offset disagree")
        if self.guard.lower < _ZERO or self.guard.upper > _HALF:
            raise ValueError("Mahler fractional guard lies outside its source cell")
        if not self.extent and (
            self.residue or self.innovation or self.guard != Interval()
        ):
            raise ValueError("empty temporal word must carry the identity source")

    @property
    def source_modulus(self) -> int:
        return 1 << self.extent

    @property
    def gain(self) -> int:
        assert self._gain is not None
        return self._gain

    @property
    def endpoint_residue(self) -> int:
        return (self.gain * self.residue + self.innovation) // self.source_modulus

    @property
    def semantic_id(self) -> tuple[object, ...]:
        """Lossless guarded future-action ID, *not* a claimed finite index."""
        return (
            MAHLER_JOINT_FUTURE_KIND,
            self.extent,
            self.residue,
            self.innovation,
            self.guard,
            self.safety,
            self.gain,
        )

    @classmethod
    def bit(cls, epsilon: int) -> MahlerJointFutureAction:
        if type(epsilon) is not int or epsilon not in (0, 1):
            raise ValueError("Mahler next branch is exactly one Boolean bit")
        return cls.with_gain(
            1,
            epsilon,
            epsilon,
            Interval(_ZERO, _THIRD) if epsilon == 0 else Interval(_THIRD, _HALF),
            MahlerSourceBoundSafetyAction.one_bit(epsilon),
            3,
        )

    @classmethod
    def zero_run(
        cls,
        length: int,
        *,
        max_extent: int = MAX_MAHLER_SOURCE_EXTENT,
    ) -> MahlerJointFutureAction:
        """Issue the closed form for ``length`` consecutive zero parities.

        A zero run has source residue 0 modulo ``2**length``, innovation 0,
        and fractional guard ``[0, 2**(length-1)/3**length)``.  The repeated
        safety cap remains 9/4, so its normalized numerator is ``9*2**length``.
        This is the same source, fractional and min-plus action as binary
        composition of ``bit(0)``; it avoids rebuilding each intermediate
        prefix when a valuation has already selected a long run.
        """
        if type(length) is not int or length < 0:
            raise ValueError("Mahler zero-run length must be a natural integer")
        if type(max_extent) is not int or max_extent < 1:
            raise ValueError("positive Mahler width budget required")
        if length > min(max_extent, MAX_MAHLER_SOURCE_EXTENT):
            raise BlockContextBudgetExceeded(
                "Mahler zero run exceeds the source width budget"
            )
        if length == 0:
            return cls()
        gain = 3**length
        modulus = 1 << length
        guard = Interval(_ZERO, Q(1 << (length - 1), gain))
        safety = MahlerSourceBoundSafetyAction(length, 0, 9 * modulus)
        return cls.with_gain(length, 0, 0, guard, safety, gain)

    @classmethod
    def with_gain(
        cls,
        extent: int,
        residue: int,
        innovation: int,
        guard: Interval,
        safety: MahlerSourceBoundSafetyAction,
        gain: int,
    ) -> MahlerJointFutureAction:
        """Build from exact coefficients already composed or source-issued."""
        result = object.__new__(cls)
        object.__setattr__(result, "extent", extent)
        object.__setattr__(result, "residue", residue)
        object.__setattr__(result, "innovation", innovation)
        object.__setattr__(result, "guard", guard)
        object.__setattr__(result, "safety", safety)
        object.__setattr__(result, "_gain", gain)
        result.__post_init__()
        return result

    @classmethod
    def from_source_prefix(
        cls, source: int, length: int, *, max_steps: int = 256
    ) -> MahlerJointFutureAction:
        """Build the exact finite future cylinder for a *supplied* source.

        Exact source-selected parity runs are composed in closed form. This
        stays separate from generic CONCAT/REPEAT because each run is admitted
        by the supplied source; it does not define a global selector.
        """
        if type(source) is not int or source < 0:
            raise ValueError("a nonnegative exact integer source is required")
        if type(length) is not int or length < 0:
            raise ValueError("source prefix length must be a natural integer")
        if (
            type(max_steps) is not int
            or max_steps < 0
            or length > max_steps
            or length > MAX_MAHLER_SOURCE_EXTENT
        ):
            raise BlockContextBudgetExceeded("source prefix discovery exceeds budget")
        current = source

        def source_runs() -> Iterator[MahlerJointFutureAction]:
            nonlocal current
            remaining = length
            # The source selects maximal even runs and odd-to-odd event
            # blocks. Consecutive odd symbols remain separate events. Each
            # block is clipped to the requested horizon; no next parity is
            # inferred. Admission and physical advancement happen before the
            # step enters the ordered composition fold.
            while remaining:
                if current & 1:
                    exponent = v2_positive(3 * current + 1)
                    run_length = min(exponent, remaining)
                    step = cls.bit(1).then(
                        cls.zero_run(run_length - 1, max_extent=max_steps)
                    )
                else:
                    run_length = (
                        remaining
                        if current == 0
                        else min(v2_positive(current), remaining)
                    )
                    step = cls.zero_run(run_length, max_extent=max_steps)
                if not step.integer_admits(current):
                    raise ArithmeticError("source-selected parity run lost its inlet")
                current = step.endpoint(current)
                remaining -= run_length
                yield step

        result = balanced_fold(
            source_runs(),
            identity=cls(),
            compose=lambda prefix, step: prefix.then(step),
        )
        if not result.integer_admits(source) or result.endpoint(source) != current:
            raise ArithmeticError("source prefix and future cylinder disagree")
        return result

    @classmethod
    def from_root_seven_transfer(
        cls,
        extent: int,
        endpoint_h: int,
        safety: MahlerSourceBoundSafetyAction,
    ) -> MahlerJointFutureAction:
        """Build the bounded canonical h=8/centered-D=7 finite word.

        This utility checks the supplied endpoint and safety against bounded
        source-selected discovery. Production observers use the admitted
        workspace transfer below and do not call this constructor.
        """
        if (
            type(extent) is not int
            or extent < 0
            or type(endpoint_h) is not int
            or endpoint_h < 1
        ):
            raise ValueError("invalid admitted source-8 transfer")
        if extent > MAX_MAHLER_SOURCE_EXTENT:
            raise BlockContextBudgetExceeded("source-8 extent exceeds hard limit")
        if extent > 256:
            raise BlockContextBudgetExceeded(
                "canonical source-8 discovery exceeds its literal step budget"
            )
        # Bound an untrusted endpoint before any source or coefficient work.
        if endpoint_h.bit_length() > extent + 4:
            raise ValueError("source-8 endpoint exceeds its finite word bound")
        if type(safety) is not MahlerSourceBoundSafetyAction or safety.extent != extent:
            raise ValueError("source-8 safety has another temporal extent")
        safety.__post_init__()
        result = cls.from_source_prefix(7, extent, max_steps=256)
        if result.endpoint(7) + 1 != endpoint_h or result.safety != safety:
            raise ValueError("source-8 endpoint/safety differs from its canonical word")
        return result

    @classmethod
    def from_admitted_root_workspace(
        cls,
        workspace: object,
        endpoint_h: int,
        safety: MahlerSourceBoundSafetyAction,
        transfer: object,
    ) -> MahlerJointFutureAction:
        """Reuse the exact gain from an already authenticated source image.

        This collaborator path is called only after the owning arithmetic
        result validates its workspace. The transfer must be the exact root
        summary object, so an arbitrary integer gain cannot issue a selector.
        """
        from number_compiler.arithmetic.fields.skew_transfer import SkewTransfer
        from number_compiler.sequences.antihydra.arithmetic_images import (
            ANTIHYDRA_ARITHMETIC_LAW,
            AntihydraArithmeticImageWorkspace,
        )

        if (
            type(workspace) is not AntihydraArithmeticImageWorkspace
            or type(transfer) is not SkewTransfer
            or type(endpoint_h) is not int
            or endpoint_h < 1
            or workspace.seed != 8
            or workspace.law != ANTIHYDRA_ARITHMETIC_LAW
            or workspace.returns < 0
            or workspace.returns > MAX_MAHLER_SOURCE_EXTENT
        ):
            raise ValueError("root future action requires an admitted arithmetic owner")
        admitted_transfer = cast(SkewTransfer[int], transfer)
        extent = workspace.returns
        if type(safety) is not MahlerSourceBoundSafetyAction or safety.extent != extent:
            raise ValueError("root safety belongs to another arithmetic extent")
        safety.__post_init__()
        workspace.validate_payload(workspace.root_payload)
        root_summary = workspace.image_node(workspace.root_payload).summary
        if (
            admitted_transfer is not root_summary.transfer
            or root_summary.width != extent
        ):
            raise ValueError("root gain is detached from the admitted image")
        endpoint_limit_bits = (
            max(
                admitted_transfer.upper.bit_length() + 4,
                abs(admitted_transfer.offset).bit_length(),
            )
            + 1
        )
        if endpoint_h.bit_length() > endpoint_limit_bits:
            raise ValueError("root endpoint exceeds its admitted transfer bound")
        q, p = 1 << extent, admitted_transfer.upper
        if admitted_transfer.lower != q or p < q:
            raise ValueError("admitted root transfer has another dyadic extent")
        endpoint, remainder = divmod(8 * p + admitted_transfer.offset, q)
        if remainder or endpoint != endpoint_h:
            raise ValueError("root endpoint differs from its admitted transfer")
        innovation = p + admitted_transfer.offset - q
        if extent == 0:
            if safety != MahlerSourceBoundSafetyAction():
                raise ValueError("zero-extent root action is not the identity")
            return cls()
        if (
            safety.offset_hat != -12 * innovation
            or safety.cap_hat != 6 * p - 12 * innovation
        ):
            raise ValueError("root safety differs from its admitted arithmetic gain")
        residue = (-innovation * pow(p, -1, q)) % q
        if residue != 7 % q or innovation < 0:
            raise ValueError("admitted root action contradicts centered source seven")
        guard = cls.bit(1).guard if extent == 1 else Interval(_ZERO, _ZERO)
        result = cls.with_gain(
            extent,
            residue,
            innovation,
            guard,
            safety,
            p,
        )
        if result.endpoint(7) != endpoint_h - 1:
            raise ArithmeticError("admitted root endpoint is not source-authenticated")
        return result

    def then(self, after: MahlerJointFutureAction) -> MahlerJointFutureAction:
        """Pull back source *and* fraction guards before composing coefficients."""
        if type(after) is not MahlerJointFutureAction:
            raise TypeError("Mahler future composition requires another joint action")
        if self.extent + after.extent > MAX_MAHLER_SOURCE_EXTENT:
            raise BlockContextBudgetExceeded(
                "Mahler composition exceeds hard extent limit"
            )
        if self.extent == 0:
            return after
        if after.extent == 0:
            return self
        # For source D=r+2**a*k the first endpoint is e+3**a*k.
        # Its next source residue requires k congruent to a unique value.
        inv = pow(self.gain, -1, after.source_modulus)
        k = ((after.residue - self.endpoint_residue) * inv) % after.source_modulus
        residue = self.residue + self.source_modulus * k
        innovation = (
            after.gain * self.innovation + self.source_modulus * after.innovation
        )
        # The fractional map is increasing: t'=(3**a*t-Ja)/2**a.
        pullback = (
            Interval(
                (Q(self.source_modulus) * after.guard.lower + Q(self.innovation))
                / Q(self.gain),
                (Q(self.source_modulus) * after.guard.upper + Q(self.innovation))
                / Q(self.gain),
            )
            if not after.guard.empty
            else Interval(_ZERO, _ZERO)
        )
        guard = self.guard.intersect(pullback)
        return MahlerJointFutureAction.with_gain(
            self.extent + after.extent,
            residue,
            innovation,
            guard,
            self.safety.then_with_authenticated_gain(after.safety, after.gain),
            self.gain * after.gain,
        )

    def power(
        self, repetitions: int, *, max_extent: int = MAX_MAHLER_SOURCE_EXTENT
    ) -> MahlerJointFutureAction:
        """Square an exact finite supplied block *with its complete pullbacks*."""
        if type(repetitions) is not int or repetitions < 0:
            raise ValueError("Mahler repeat count must be a natural integer")
        if type(max_extent) is not int or max_extent < 1:
            raise ValueError("positive Mahler width budget required")
        if self.extent * repetitions > min(max_extent, MAX_MAHLER_SOURCE_EXTENT):
            raise BlockContextBudgetExceeded(
                "source-bound repeat exceeds its bit budget"
            )
        return binary_power(
            self,
            repetitions,
            identity=MahlerJointFutureAction(),
            compose=MahlerJointFutureAction.then,
        ).value

    @classmethod
    def event(
        cls,
        exponent: int,
        *,
        max_extent: int = MAX_MAHLER_SOURCE_EXTENT,
    ) -> MahlerJointFutureAction:
        """Any q>=1 maximal source event 0**(q-1)1, without q replayed bits."""
        if type(exponent) is not int or exponent < 1:
            raise ValueError("Mahler event exponent must be positive")
        if type(max_extent) is not int or max_extent < 1:
            raise ValueError("positive Mahler width budget required")
        if exponent > min(max_extent, MAX_MAHLER_SOURCE_EXTENT):
            raise BlockContextBudgetExceeded(
                "Mahler event exceeds the source width budget"
            )
        return cls.zero_run(exponent - 1, max_extent=max_extent).then(cls.bit(1))

    def then_event(
        self,
        exponent: int,
        *,
        max_extent: int = MAX_MAHLER_SOURCE_EXTENT,
    ) -> MahlerJointFutureAction:
        if type(exponent) is not int or exponent < 1:
            raise ValueError("Mahler event exponent must be positive")
        if type(max_extent) is not int or max_extent < 1:
            raise ValueError("positive Mahler width budget required")
        if self.extent + exponent > min(max_extent, MAX_MAHLER_SOURCE_EXTENT):
            raise BlockContextBudgetExceeded("Mahler future event exceeds width budget")
        return self.then(self.event(exponent, max_extent=max_extent))

    def successor_branches(self) -> tuple[MahlerJointSuccessor, ...]:
        """Both source-parity classes, refined by strict fractional admission.

        If D=residue+2**L*k, then D' = endpoint_residue+3**L*k,
        so the next epsilon is (endpoint_residue+k) mod 2. Only fractions
        in each returned child's exact half-open guard are admitted.
        """
        result: list[MahlerJointSuccessor] = []
        for epsilon in (0, 1):
            child = self.then(self.bit(epsilon))
            if not child.guard.empty:
                parity = epsilon ^ (self.endpoint_residue & 1)
                if child.residue != self.residue + self.source_modulus * parity:
                    raise ArithmeticError("future source high-fiber pivot disagrees")
                result.append(MahlerJointSuccessor(epsilon, parity, child))
        return tuple(result)

    def integer_admits(self, source: int) -> bool:
        return (
            type(source) is int
            and source >= 0
            and source % self.source_modulus == self.residue
        )

    def admits(self, source: int, fraction: Q) -> bool:
        return (
            self.integer_admits(source)
            and type(fraction) is Q
            and self.guard.contains(fraction)
        )

    def endpoint(self, source: int) -> int:
        if not self.integer_admits(source):
            raise ValueError("Mahler endpoint requires the exact original source fiber")
        return self.endpoint_residue + self.gain * (source >> self.extent)

    def fraction_endpoint(self, fraction: Q) -> Q:
        if type(fraction) is not Q or not self.guard.contains(fraction):
            raise ValueError("Mahler fractional endpoint requires an admitted interval")
        return (Q(self.gain) * fraction - Q(self.innovation)) / Q(self.source_modulus)

    def apply(self, source: int, fraction: Q) -> tuple[int, Q]:
        if not self.admits(source, fraction):
            raise ValueError("source and fractional guard do not authorize this word")
        return self.endpoint(source), self.fraction_endpoint(fraction)

    def five_adic_affine(self, places: int) -> tuple[int, int, int]:
        """Exact full temporal action modulo 5**places, not merely a sidecar.

        The homogeneous multiplier 3/2 is a unit in Z/(5**places); every
        source in the original 2-adic cylinder follows this affine law.
        """
        if type(places) is not int or not 1 <= places <= 4096:
            raise ValueError("5-adic demand must have positive bounded precision")
        modulus = 5**places
        inverse = exact_modular_power(2, -self.extent, modulus)
        return (
            (self.gain * inverse) % modulus,
            (self.innovation * inverse) % modulus,
            modulus,
        )

    def source_window(
        self,
        source: int,
        *,
        bits: int = 16,
        decimal_places: int = 4,
        fraction: Q | None = None,
    ) -> MahlerJointInteriorWindow:
        """Demand real bit/carry/CRT evidence from *this same* original source.

        Fermat's NC15 two-carry action is reused for the actual source operands
        D+(2*D+epsilon).  This cannot turn arbitrary low windows into an
        all-depth source- or fractional-safety certificate.
        """
        if not self.integer_admits(source):
            raise ValueError("binary/decimal interior demand lost its source guard")
        if fraction is not None and not self.admits(source, fraction):
            raise ValueError("interior demand lost its strict fractional guard")
        if (
            type(bits) is not int
            or type(decimal_places) is not int
            or not 1 <= decimal_places <= bits <= 4096
        ):
            raise ValueError("joint interior window must use bounded exact positions")
        current = self.endpoint(source)
        epsilon = current & 1
        limb = 1 << (bits + 1)
        a = current % limb
        b = (2 * current + epsilon) % limb
        counter = BinaryBooleanCarryAction.from_words(a, b, bits + 1, limb)
        _carry_out, emitted, xor_mask = counter.apply_words(0)
        next_source = (3 * current + epsilon) // 2
        next_binary = emitted >> 1
        if next_binary != next_source % (1 << bits):
            raise ArithmeticError("two-carry binary output contradicts source shift")
        modulus_5 = 5**decimal_places
        next_five: int = (
            (3 * (current % modulus_5) + epsilon)
            * exact_modular_power(2, -1, modulus_5)
        ) % modulus_5
        if next_five != next_source % modulus_5:
            raise ArithmeticError("5-adic affine arm disagrees with source")
        modulus_2 = 1 << decimal_places
        r2 = next_binary % modulus_2
        next_decimal: int = r2 + modulus_2 * (
            ((next_five - r2) * exact_modular_power(modulus_2, -1, modulus_5))
            % modulus_5
        )
        if next_decimal != next_source % (10**decimal_places):
            raise ArithmeticError("joint CRT reconstruction disagrees with source")
        next_fraction = None if fraction is None else self.fraction_endpoint(fraction)
        next_branch_safe = (
            None
            if next_fraction is None
            else self.bit(epsilon).guard.contains(next_fraction)
        )
        source_decimal = current % (10**decimal_places)
        binary_borrows = decimal_borrows = 0
        carry = 0
        for i in range(bits):
            out_bit = (next_binary >> i) & 1
            in_bit = (current >> i) & 1
            carry = int(out_bit < in_bit + carry)
            binary_borrows |= carry << i
        carry = 0
        decimal_in: int = source_decimal
        decimal_out: int = next_decimal
        for i in range(decimal_places):
            old_digit: int = decimal_in % 10
            new_digit: int = decimal_out % 10
            carry = int(new_digit < old_digit + carry)
            decimal_borrows |= carry << i
            decimal_in //= 10
            decimal_out //= 10
        return MahlerJointInteriorWindow.from_checked_source_window(
            source,
            current,
            epsilon,
            next_source,
            bits,
            decimal_places,
            a,
            b,
            emitted,
            next_binary,
            next_five,
            next_decimal,
            source_decimal,
            binary_borrows,
            decimal_borrows,
            a & b,
            a ^ b,
            xor_mask,
            counter,
            fraction is not None,
            next_fraction,
            next_branch_safe,
        )

    def interior_fiber_window(
        self, high_fiber: int, *, bits: int = 16, decimal_places: int = 4
    ) -> MahlerJointFiberWindow:
        """Quotient *all* high fibers sharing the demanded radix-2/5 suffix.

        One extra binary input bit is necessary for the final division by 2.
        The 5-primary clock only needs the demanded 5**places class. Keeping
        their CRT product certifies the binary XOR/carry/borrow, F5 and decimal
        outputs for arbitrary unmaterialized high bits.
        """
        fiber_residue, fiber_modulus = self.interior_fiber_class(
            high_fiber, bits=bits, decimal_places=decimal_places
        )
        representative = self.residue + self.source_modulus * fiber_residue
        return MahlerJointFiberWindow(
            fiber_residue,
            fiber_modulus,
            self.source_window(
                representative, bits=bits, decimal_places=decimal_places
            ),
        )

    def interior_fiber_class(
        self, high_fiber: int, *, bits: int = 16, decimal_places: int = 4
    ) -> tuple[int, int]:
        """Return the demanded-precision high-fiber residue and modulus.

        The source-aware caller can attach this exact class to an already
        computed output packet without repeating its binary/decimal window.
        """
        if type(high_fiber) is not int or high_fiber < 0:
            raise ValueError("a natural exact high fiber is required")
        if (
            type(bits) is not int
            or type(decimal_places) is not int
            or not 1 <= decimal_places <= bits <= 4096
        ):
            raise ValueError("interior fiber query exceeds exact position bounds")
        modulus = (1 << (bits + 1)) * 5**decimal_places
        residue = high_fiber % modulus
        return residue, modulus

    def max_fixed_word_repetitions(self, positive_source: int) -> int:
        """Exact source-side upper bound; does not prove fractional survival.

        q**n | H(D), H=(3**L-2**L)*D+J for n identical clauses.
        An all-time source loop is impossible for any *positive* D.
        """
        if type(positive_source) is not int or positive_source < 1:
            raise ValueError(
                "fixed-word obstruction requires a positive integer source"
            )
        if self.extent < 1:
            raise ValueError("fixed-word obstruction needs a nonempty clause")
        if not self.integer_admits(positive_source):
            raise ValueError(
                "fixed-word obstruction requires the admitted source cylinder"
            )
        h = (self.gain - self.source_modulus) * positive_source + self.innovation
        valuation = (h & -h).bit_length() - 1
        return valuation // self.extent


__all__ = (
    "MahlerJointFiberWindow",
    "MahlerJointFutureAction",
    "MahlerJointInteriorWindow",
    "MahlerJointSuccessor",
)
