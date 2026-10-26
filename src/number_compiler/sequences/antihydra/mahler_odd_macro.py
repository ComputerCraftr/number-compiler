"""NC16 source-bound odd-to-odd Mahler/Antihydra macro quotient.

This is the *ledger* barrier, not Mahler's strict fractional Z-number
predicate. The accelerated variable is x=3*(h-1) at an odd centered seam:

    a = v2(x+1), x' = 3**a * ((x+1)//2**a), n' = n+a,
    C' = C+3-a, q = 2**n * (x+1).

The exact failure condition is 2**(3*i+4) | q, equivalently
v2(x+1)>=C+4 for C=3*i-n. This identifies the first *ledger* barrier
without constructing q or enumerating the a physical return bits.

The full temporal word is 1,0**(a-1), *not* the older 0**(q-1),1 event.
A further endpoint-parity bit is retained in the pointed source congruence:
a source that follows the word but ends even is NOT an odd-to-odd return.

All CONCAT/REPEAT actions retain exact original-source/fractional guards,
minimum-prefix ledger safety and a pointed odd endpoint. Derived radix and
harmonic observations never authorize unobserved future source events.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Final
from weakref import ReferenceType, ref

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.contracts.input_validation import is_object_dictionary
from number_compiler.arithmetic.fields.consumer_pullback import (
    ExactRational,
    HalfOpenInterval,
)
from number_compiler.arithmetic.fields.integer_congruence import exact_modular_power
from number_compiler.arithmetic.fields.morphism_core import binary_power
from number_compiler.arithmetic.fields.three_power_radix import (
    ThreePowerRadixOrbit,
    triple_residue,
)
from number_compiler.arithmetic.fields.two_adic import v2_positive
from number_compiler.arithmetic.fields.walsh import walsh64_mod5
from number_compiler.sequences.antihydra.mahler_joint_future import (
    MahlerJointFutureAction,
)
from number_compiler.sequences.antihydra.mahler_source_actions import (
    MahlerSourceBoundSafetyAction,
)

_ODD_TO_ODD_ACTION_TAG: Final[str] = "mahler-odd-to-odd-nc16-v1"
_ODD_ACTION_ISSUER = object()


@dataclass(frozen=True, slots=True)
class _OddActionProvenance:
    issuer: object
    record: ReferenceType[object]
    snapshot: tuple[object, ...]


def _validate_q_port_demand(places: int, walsh: bool, prime_radices: bool) -> None:
    if type(places) is not int or not 1 <= places <= 64:
        raise ValueError("q digit demand must be in 1..64")
    if type(walsh) is not bool or type(prime_radices) is not bool:
        raise TypeError("q harmonic demand flags must be Boolean")


def _exact_joint_snapshot(joint: object) -> tuple[object, ...]:
    """Copy authority-bearing joint fields into immutable typed scalars."""
    if type(joint) is not MahlerJointFutureAction:
        return (type(joint),)

    def scalar(value: object) -> tuple[object, ...]:
        return type(value), value

    def rational(value: object) -> tuple[object, ...]:
        if type(value) is not ExactRational:
            return (type(value),)
        return (
            type(value),
            scalar(value.numerator),
            scalar(value.denominator),
        )

    guard = joint.guard
    guard_snapshot = (
        (type(guard), rational(guard.lower), rational(guard.upper))
        if type(guard) is HalfOpenInterval
        else (type(guard),)
    )
    safety = joint.safety
    safety_snapshot = (
        (
            type(safety),
            scalar(safety.extent),
            scalar(safety.offset_hat),
            scalar(safety.cap_hat),
        )
        if type(safety) is MahlerSourceBoundSafetyAction
        else (type(safety),)
    )
    return (
        type(joint),
        scalar(joint.extent),
        scalar(joint.residue),
        scalar(joint.innovation),
        scalar(getattr(joint, "_gain", None)),
        guard_snapshot,
        safety_snapshot,
    )


def _macro_radix_harmonics(
    extent: int, places: int, walsh: bool
) -> tuple[dict[int, dict[str, object]], tuple[int, ...] | None]:
    radix_rows: dict[int, dict[str, object]] = {}
    for base in (2, 5, 10):
        ports = ThreePowerRadixOrbit("ordinary", extent, base).ordinary_ports(places)
        radix_rows[base] = {
            "tripling_carries": ports.carry_word,
            "innovation_borrows": ports.forward_borrow_mask,
            "xor": ports.difference_xor_mask,
        }
    radix64 = (
        ThreePowerRadixOrbit("ordinary", extent, 64).ordinary_ports(64)
        if walsh
        else None
    )
    return radix_rows, (
        None if radix64 is None else walsh64_mod5(radix64.difference_xor_mask)
    )


@dataclass(frozen=True, slots=True)
class MahlerOddSeamStep:
    """One exact witnessed odd-source event, no exponential q numerator."""

    index: int
    clock: int
    source: int
    x: int
    exponent: int
    incoming_balance: int
    ending_balance: int
    next_source: int
    next_x: int
    next_clock: int
    q_valuation: int
    required_valuation: int
    barrier_fails: bool

    @property
    def q_divisible(self) -> bool:
        return self.barrier_fails

    def demanded_q_ports(
        self,
        *,
        places: int = 8,
        walsh: bool = False,
        prime_radices: bool = False,
    ) -> dict[str, object]:
        """Source-derived q recurrence carries/borrows in radix 2, 5, 10, 64.

        q_i = 2**n * (3D+1), q_next = 3**a * q_i + 2**(n+a).
        The recurrence is evaluated only at demanded prime-radix moduli.
        No materialization of the unbounded q tape or of intervening bits.
        """
        _validate_q_port_demand(places, walsh, prime_radices)
        canonical = _canonical_odd_seam(self)
        return canonical.demanded_q_ports_after_validation(
            places=places, walsh=walsh, prime_radices=prime_radices
        )

    def demanded_q_ports_after_validation(
        self, *, places: int, walsh: bool, prime_radices: bool = False
    ) -> dict[str, object]:
        """Project q ports through the validated seam collaborator API."""
        _validate_q_port_demand(places, walsh, prime_radices)
        canonical = _canonical_odd_seam(self)
        rows: dict[int, dict[str, object]] = {}
        q_endpoints: dict[int, int] = {}
        bases = (
            (2, 3, 5, 6, 10, 64)
            if prime_radices
            else (2, 5, 10, 64)
            if walsh
            else (2, 5, 10)
        )
        for base in bases:
            cells = 64 if base == 64 and walsh else places
            carries = borrows = 0
            q_initial = q_next = 0
            for j in range(1, cells + 1):
                modulus = base**j
                q_initial = (
                    exact_modular_power(2, canonical.clock, modulus)
                    * (canonical.x + 1)
                    % modulus
                )
                # Ordinary 3^a is the exact Collatz radix source at this seam.
                triple = triple_residue("ordinary", canonical.exponent, base, j)
                summand = exact_modular_power(2, canonical.next_clock, modulus)
                product = triple * q_initial % modulus
                q_next = (product + summand) % modulus
                expected = (
                    exact_modular_power(2, canonical.next_clock, modulus)
                    * (canonical.next_x + 1)
                    % modulus
                )
                if q_next != expected:
                    raise ArithmeticError("q recurrence departed from pointed source")
                carries |= int(product + summand >= modulus) << (j - 1)
                borrows |= int(q_next < q_initial) << (j - 1)
            q_endpoints[base] = q_next
            rows[base] = {
                "q_initial": q_initial,
                "q_next": q_next,
                "carry_mask": carries,
                "difference_borrow_mask": borrows,
                "carry_borrow_xor": carries ^ borrows,
                "walsh64_mod5": (
                    walsh64_mod5(carries ^ borrows) if base == 64 and walsh else None
                ),
            }
        # Base-10 carries depend on both 2- and 5-primary constraints.
        m2, m5 = 1 << places, 5**places
        b2 = q_endpoints[2] % m2
        b5 = q_endpoints[5]
        joined: int = b2 + m2 * ((b5 - b2) * exact_modular_power(m2, -1, m5) % m5)
        if joined != q_endpoints[10]:
            raise ArithmeticError("q primary orbits do not reconstruct decimal suffix")
        return {
            "source_clock": canonical.clock,
            "odd_index": canonical.index,
            "q_valuation": canonical.q_valuation,
            "barrier_exponent": canonical.required_valuation,
            "base_10_crt": joined,
            "radix_ports": rows,
        }


def odd_seam_pointwise_packet(
    seam: MahlerOddSeamStep, *, places: int = 4
) -> dict[str, object]:
    """Publish only a pointed event/barrier and bounded q-radix projection.

    Unlike :func:`odd_seam_packet`, this does not build event-word harmonics,
    source windows, or a repeated-event ring. It is intended for a pointwise
    observer attached to an already admitted arithmetic endpoint.
    """
    _validate_q_port_demand(places, False, True)
    canonical = _canonical_odd_seam(seam)
    q_ports = canonical.demanded_q_ports_after_validation(
        places=places, walsh=False, prime_radices=True
    )
    raw_ports = q_ports["radix_ports"]
    if (
        not is_object_dictionary(raw_ports)
        or type(raw_ports) is not dict
        or set(raw_ports) != {2, 3, 5, 6, 10, 64}
    ):
        raise ArithmeticError("pointwise q observer returned an incomplete radix set")
    return {
        "source": canonical.source,
        "odd_index": canonical.index,
        "source_clock": canonical.clock,
        "incoming_balance": canonical.incoming_balance,
        "x": canonical.x,
        "run_exponent": canonical.exponent,
        "next_odd_source": canonical.next_source,
        "next_x": canonical.next_x,
        "next_clock": canonical.next_clock,
        "next_balance": canonical.ending_balance,
        "q_valuation": canonical.q_valuation,
        "required_q_valuation": canonical.required_valuation,
        "barrier_failure_next_macro": canonical.barrier_fails,
        "q_radix_orbits": {str(base): row for base, row in raw_ports.items()},
        "barrier_kind": "Antihydra ledger, not Mahler fractional safety",
        "scope": "authenticated next odd event; Boolean/Walsh windows separate and lazy",
    }


@dataclass(frozen=True, slots=True, init=False, weakref_slot=True)
class MahlerOddToOddAction:
    """Pointed source-bound action for one or more supplied odd-to-odd runs.

    `joint` owns all *intermediate* bit selectors and fractional guards.
    Additionally, the endpoint has odd parity, so the source modulus is
    2**(joint.extent+1). Keeping this extra bit prevents invalid merges
    of sources following the same finite 1,0,... word but ending even.

    The paired `(delta, minimum)` is the real Antihydra ledger action. It
    is independent of, and not a surrogate for, joint.safety's Mahler margin.
    """

    joint: MahlerJointFutureAction
    odd_events: int
    delta: int
    minimum: int
    _issuer: object = field(init=False, repr=False, compare=False)

    def __init__(self) -> None:
        raise TypeError("odd-to-odd actions require a checked factory")

    @classmethod
    def _issue(
        cls,
        joint: MahlerJointFutureAction,
        odd_events: int,
        delta: int,
        minimum: int,
        *,
        issuer: object,
    ) -> MahlerOddToOddAction:
        if issuer is not _ODD_ACTION_ISSUER:
            raise TypeError("odd-to-odd actions require the canonical issuer")
        result = object.__new__(cls)
        object.__setattr__(result, "joint", joint)
        object.__setattr__(result, "odd_events", odd_events)
        object.__setattr__(result, "delta", delta)
        object.__setattr__(result, "minimum", minimum)
        result.__post_init__()
        object.__setattr__(
            result,
            "_issuer",
            _OddActionProvenance(_ODD_ACTION_ISSUER, ref(result), result._snapshot()),
        )
        result.verify_issued()
        return result

    def _snapshot(self) -> tuple[object, ...]:
        return (
            _exact_joint_snapshot(self.joint),
            (type(self.odd_events), self.odd_events),
            (type(self.delta), self.delta),
            (type(self.minimum), self.minimum),
        )

    def verify_issued(self) -> None:
        provenance = getattr(self, "_issuer", None)
        if (
            type(provenance) is not _OddActionProvenance
            or provenance.issuer is not _ODD_ACTION_ISSUER
            or provenance.record() is not self
            or provenance.snapshot != self._snapshot()
        ):
            raise ValueError("odd-to-odd action is not an unchanged factory result")

    def __post_init__(self) -> None:
        if type(self.joint) is not MahlerJointFutureAction:
            raise TypeError("odd action requires an authenticated Mahler source action")
        if type(self.odd_events) is not int or self.odd_events < 0:
            raise ValueError("odd event count must be a natural integer")
        if type(self.delta) is not int or type(self.minimum) is not int:
            raise TypeError("ledger effects must be exact integers")
        if self.delta != 3 * self.odd_events - self.joint.extent:
            raise ValueError("Antihydra ledger and temporal odd counts disagree")
        if self.minimum > min(0, self.delta):
            raise ValueError("Antihydra minimum-prefix certificate is unsound")
        if self.joint.extent == 0 and (self.odd_events or self.minimum):
            raise ValueError("identity odd-seam action must be an identity")

    @classmethod
    def identity(cls) -> MahlerOddToOddAction:
        return cls._issue(MahlerJointFutureAction(), 0, 0, 0, issuer=_ODD_ACTION_ISSUER)

    @classmethod
    def from_bits(
        cls, bits: tuple[int, ...], *, max_extent: int = 4096
    ) -> MahlerOddToOddAction:
        """Issue one exact odd-to-odd action from a supplied parity word.

        The source cylinder chooses the final high bit that makes the target
        odd. Prefix ledger effects are accumulated from the same word; no
        source-dependent event is guessed or extended by this constructor.
        """
        if (
            type(bits) is not tuple
            or not bits
            or any(type(bit) is not int or bit not in (0, 1) for bit in bits)
        ):
            raise ValueError("odd-to-odd source word must be a nonempty bit tuple")
        if bits[0] != 1:
            raise ValueError("odd-to-odd source word must start at an odd state")
        if type(max_extent) is not int or max_extent < 1 or len(bits) > max_extent:
            raise BlockContextBudgetExceeded("odd word exceeds temporal bit budget")
        joint = MahlerJointFutureAction()
        balance = minimum = odd_events = 0
        for bit in bits:
            joint = joint.then(MahlerJointFutureAction.bit(bit))
            if bit:
                odd_events += 1
                balance += 2
            else:
                balance -= 1
            minimum = min(minimum, balance)
        return cls._issue(
            joint,
            odd_events,
            balance,
            minimum,
            issuer=_ODD_ACTION_ISSUER,
        )

    @classmethod
    def run(cls, exponent: int, *, max_extent: int = 4096) -> MahlerOddToOddAction:
        """Source-guarded 1,0**(a-1) with its final *odd* seam bit."""
        if type(exponent) is not int or exponent < 1:
            raise ValueError("odd-to-odd run length must be positive")
        if type(max_extent) is not int or max_extent < 1 or exponent > max_extent:
            raise BlockContextBudgetExceeded("odd macro exceeds temporal bit budget")
        zero_tail = MahlerJointFutureAction.zero_run(
            exponent - 1, max_extent=max_extent
        )
        joint = MahlerJointFutureAction.bit(1).then(zero_tail)
        if joint.innovation != 3 ** (exponent - 1):
            raise ArithmeticError("odd-return affine numerator is not authenticated")
        return cls._issue(
            joint,
            1,
            3 - exponent,
            min(0, 3 - exponent),
            issuer=_ODD_ACTION_ISSUER,
        )

    @property
    def extent(self) -> int:
        return self.joint.extent

    @property
    def source_modulus(self) -> int:
        self.verify_issued()
        return 1 << (self.extent + 1)

    @property
    def source_residue(self) -> int:
        """Choose the unique next high bit making the terminal source odd."""
        self.verify_issued()
        incoming_high_bit = 1 ^ (self.joint.endpoint_residue & 1)
        return self.joint.residue + (incoming_high_bit << self.extent)

    @property
    def semantic_id(self) -> tuple[object, ...]:
        """Lossless exact guarded action; NOT claimed globally Moore-minimal."""
        self.verify_issued()
        return (
            _ODD_TO_ODD_ACTION_TAG,
            self.joint.semantic_id,
            self.source_residue,
            self.odd_events,
            self.delta,
            self.minimum,
        )

    def integer_admits(self, source: int) -> bool:
        self.verify_issued()
        if type(source) is not int or source < 1:
            return False
        source_cell = source % self.source_modulus
        if (
            source_cell != self.source_residue
            or not self.joint.integer_admits(source)
            or source_cell % 2 != 1
        ):
            return False
        endpoint_high_bit = source_cell >> self.joint.extent
        endpoint_parity = (
            self.joint.endpoint_residue + self.joint.gain * endpoint_high_bit
        ) & 1
        return endpoint_parity == 1

    def advance(self, source: int, balance: int) -> tuple[int, int]:
        """Total arithmetic action even if ledger safety fails."""
        if type(balance) is not int or not self.integer_admits(source):
            raise ValueError("odd macro requires exact pointed source and balance")
        endpoint = self.joint.endpoint(source)
        if not (source & 1 and endpoint & 1):
            raise ArithmeticError("odd-return source/end parity is inconsistent")
        return endpoint, balance + self.delta

    def apply(self, source: int, balance: int) -> tuple[int, int]:
        """Safety-authorized use of an already issued odd-to-odd action."""
        self.verify_issued()
        if type(balance) is not int or balance + self.minimum < 0:
            raise ValueError("odd macro violates Antihydra prefix ledger safety")
        return self.advance(source, balance)

    def then(self, after: MahlerOddToOddAction) -> MahlerOddToOddAction:
        self.verify_issued()
        if type(after) is not MahlerOddToOddAction:
            raise TypeError(
                "chronological odd-return composition requires pointed actions"
            )
        after.verify_issued()
        joined = self.joint.then(after.joint)
        result = MahlerOddToOddAction._issue(
            joined,
            self.odd_events + after.odd_events,
            self.delta + after.delta,
            min(self.minimum, self.delta + after.minimum),
            issuer=_ODD_ACTION_ISSUER,
        )
        # Every nonempty block begins/ends at an odd source; the next bit of
        # `after` fixes the former endpoint. The extra last parity bit fixes
        # the final endpoint, so no unpointed source is admitted.
        if self.extent and after.extent:
            if result.source_residue % self.source_modulus != self.source_residue:
                raise ArithmeticError("odd seam source guard was lost in CONCAT")
            if (
                self.joint.endpoint(result.source_residue) % after.source_modulus
                != after.source_residue
            ):
                raise ArithmeticError("odd seam intermediate source guard was lost")
        return result

    def power(
        self, repetitions: int, *, max_extent: int = 4096
    ) -> MahlerOddToOddAction:
        """Logarithmic exact guard/ledger powering of a supplied run word."""
        self.verify_issued()
        if type(repetitions) is not int or repetitions < 0:
            raise ValueError("odd-run repetition count must be natural")
        if type(max_extent) is not int or max_extent < 1:
            raise ValueError("positive odd-run action budget required")
        if self.extent * repetitions > max_extent:
            raise BlockContextBudgetExceeded("odd-run powered width budget exceeded")
        return binary_power(
            self,
            repetitions,
            identity=self.identity(),
            compose=MahlerOddToOddAction.then,
        ).value

    def _harmonic_action_fields(
        self,
        radix_rows: dict[int, dict[str, object]],
        walsh64: tuple[int, ...] | None,
    ) -> dict[str, object]:
        radial = self.joint.safety.radial_sturmian_clock
        return {
            "source_residue": self.source_residue,
            "source_modulus": self.source_modulus,
            "extent": self.extent,
            "odd_events": self.odd_events,
            "balance_delta": self.delta,
            "balance_minimum": self.minimum,
            "margin_guard_empty": self.joint.guard.empty,
            "radial_scale": (radial.scale.growths, radial.scale.halvings),
            "radix_ports": radix_rows,
            "walsh64_mod5": walsh64,
            "all_time_claim": False,
        }

    def demanded_harmonics(
        self,
        source: int,
        *,
        bits: int = 16,
        decimal_places: int = 4,
        places: int = 6,
        walsh: bool = False,
    ) -> dict[str, object]:
        """One source-certified action with Collatz/NC15 Boolean & multiradix ports.

        No second source/itinerary discovery: all digits are projections of
        `joint`, whose complete temporal guard has already been issued.
        """
        if not self.integer_admits(source):
            raise ValueError("harmonics require the exact pointed source fiber")
        if type(places) is not int or not 1 <= places <= 64:
            raise ValueError("radix-demand places must be in 1..64")
        window = self.joint.source_window(
            source, bits=bits, decimal_places=decimal_places
        )
        radix_rows, walsh64 = _macro_radix_harmonics(self.extent, places, walsh)
        multiplier, offset, modulus = self.joint.five_adic_affine(decimal_places)
        if (multiplier * source + offset) % modulus != window.source_endpoint % modulus:
            raise ArithmeticError("odd macro 5-adic projection detached from source")
        packet = self._harmonic_action_fields(radix_rows, walsh64)
        packet.update(
            {
                "binary_next": window.next_binary,
                "binary_carry_contexts": window.counter.next_carries,
                "binary_counter_h5": tuple(
                    (h.phi2, h.phi3_a, h.phi3_b) for h in window.counter.harmonics
                ),
                "binary_xor_mask": window.xor_mask,
                "binary_difference_borrows": window.binary_difference_borrows,
                "five_adic": (multiplier, offset, modulus),
                "five_next": window.next_five,
                "decimal_next": window.next_decimal,
                "decimal_difference_borrows": window.decimal_difference_borrows,
            }
        )
        return packet

    def endpoint_harmonics(
        self,
        source: int,
        endpoint: int,
        *,
        bits: int,
        decimal_places: int,
        places: int,
        walsh: bool,
    ) -> dict[str, object]:
        """Project this admitted macro's endpoint without observing its future."""
        if not self.integer_admits(source):
            raise ValueError("harmonics require the exact pointed source fiber")
        if type(endpoint) is not int or endpoint != self.joint.endpoint(source):
            raise ValueError("harmonics endpoint differs from the admitted macro")
        if (
            type(bits) is not int
            or type(decimal_places) is not int
            or not 1 <= decimal_places <= bits <= 4096
            or decimal_places > 64
        ):
            raise ValueError("endpoint harmonics need bounded exact positions")
        if type(places) is not int or not 1 <= places <= 64:
            raise ValueError("radix-demand places must be in 1..64")

        radix_rows, walsh64 = _macro_radix_harmonics(self.extent, places, walsh)
        multiplier, offset, modulus = self.joint.five_adic_affine(decimal_places)
        if (multiplier * source + offset) % modulus != endpoint % modulus:
            raise ArithmeticError("5-adic macro projection detached from endpoint")
        packet = self._harmonic_action_fields(radix_rows, walsh64)
        packet.update(
            {
                "endpoint": endpoint,
                "binary_endpoint": endpoint % (1 << bits),
                "five_endpoint": endpoint % (5**decimal_places),
                "decimal_endpoint": endpoint % (10**decimal_places),
                "five_adic": (multiplier, offset, modulus),
                "scope": "admitted odd macro endpoint; no post-endpoint source window",
            }
        )
        return packet


def odd_seam_step(
    source: int, index: int, clock: int, balance: int, *, max_extent: int = 4096
) -> MahlerOddSeamStep:
    """Exact next barrier from one witnessed odd centered source.

    The q numerator is not constructed. We use v2(q)=n+v2(3D+1).
    The equalities C=3*i-n and x=3D are authenticated at this seam.
    """
    if type(max_extent) is not int or not 1 <= max_extent <= 4096:
        raise ValueError("odd-seam extent budget is outside its hard bound")
    if type(source) is not int or source < 1 or source % 2 != 1:
        raise ValueError("odd-seam source must be a positive odd integer")
    if (
        any(type(v) is not int or v < 0 for v in (index, clock))
        or type(balance) is not int
        or balance != 3 * index - clock
    ):
        raise ValueError("odd-seam ledger/clock/index provenance disagrees")
    x = 3 * source
    exponent = v2_positive(x + 1)
    if exponent > max_extent:
        raise BlockContextBudgetExceeded("odd seam exceeds exact source budget")
    # The v2 comparison is the exact user-proposed q divisibility criterion.
    valuation, required = clock + exponent, 3 * index + 4
    failure = valuation >= required
    action = MahlerOddToOddAction.run(exponent, max_extent=max_extent)
    if not action.integer_admits(source):
        raise ArithmeticError("v2 first-hole source disagrees with odd pointed guard")
    next_source, next_balance = action.advance(source, balance)
    next_x = 3**exponent * ((x + 1) >> exponent)
    if 3 * next_source != next_x or failure != (next_balance < 0):
        raise ArithmeticError("odd-to-odd exponent, q-barrier, and ledger disagree")
    return MahlerOddSeamStep(
        index,
        clock,
        source,
        x,
        exponent,
        balance,
        next_balance,
        next_source,
        next_x,
        clock + exponent,
        valuation,
        required,
        failure,
    )


def _canonical_odd_seam(seam: object) -> MahlerOddSeamStep:
    """Authenticate every seam field against its source recurrence exactly once."""
    if type(seam) is not MahlerOddSeamStep:
        raise TypeError("odd-seam projection requires a canonical seam record")
    integer_fields = (
        "index",
        "clock",
        "source",
        "x",
        "exponent",
        "incoming_balance",
        "ending_balance",
        "next_source",
        "next_x",
        "next_clock",
        "q_valuation",
        "required_valuation",
    )
    if (
        any(type(getattr(seam, name)) is not int for name in integer_fields)
        or type(seam.barrier_fails) is not bool
    ):
        raise ValueError("odd-seam projection requires canonical fields")
    try:
        canonical = odd_seam_step(
            seam.source, seam.index, seam.clock, seam.incoming_balance
        )
    except ValueError as error:
        raise ValueError(
            "odd-seam fields do not match their source recurrence"
        ) from error
    if seam != canonical:
        raise ValueError("odd-seam fields do not match their source recurrence")
    return canonical


def odd_seam_packet(
    seam: MahlerOddSeamStep,
    *,
    bits: int = 16,
    decimal_places: int = 4,
    walsh: bool = True,
    include_mixed_ring: bool = True,
) -> dict[str, object]:
    """The one shared producer-owned NC16 macro + harmonics packet.

    No secondary source itinerary discovery. Both consumers authenticate the
    same pointed action and preserve separate ledger/fractional predicates.
    """
    seam = _canonical_odd_seam(seam)
    _validate_q_port_demand(decimal_places, walsh, False)
    if type(include_mixed_ring) is not bool:
        raise TypeError("mixed harmonic ring demand must be Boolean")
    action = MahlerOddToOddAction.run(seam.exponent)
    if action.advance(seam.source, seam.incoming_balance) != (
        seam.next_source,
        seam.ending_balance,
    ):
        raise ArithmeticError("NC16 macro diverged from pointed source certificate")
    harmonics = action.endpoint_harmonics(
        seam.source,
        seam.next_source,
        bits=bits,
        decimal_places=decimal_places,
        places=decimal_places,
        walsh=walsh,
    )
    q_ports = seam.demanded_q_ports_after_validation(places=decimal_places, walsh=walsh)
    # The repeated-word ring is a separate, source-cylinder consumer. It is
    # constructed only for this detailed packet; ordinary Mahler terms and
    # the one-event action do not build a future graph.
    from number_compiler.sequences.antihydra.mahler_harmonic_ring import (
        MahlerFixedOddHarmonicRing,
        OpenMahlerRingInletsRequired,
    )
    from number_compiler.sequences.antihydra.mahler_open_harmonic_moore import (
        MahlerConditionalOpenMoore,
    )

    ring = MahlerFixedOddHarmonicRing.from_source(seam.source)
    if ring.exponent != seam.exponent or not ring.admits(1):
        raise ArithmeticError("source-certified ring differs from the odd seam")
    certified = ring.demand_count(
        max_events=32,
        max_steps=4096,
    )
    if certified < 1:
        raise ArithmeticError("an issued odd seam did not admit its first return")
    powered = ring.action(certified)
    projected_endpoint, projected_balance = powered.advance(
        seam.source, seam.incoming_balance
    )
    if projected_balance != seam.incoming_balance + powered.delta:
        raise ArithmeticError("fixed-word ring detached from the admitted odd seam")
    primary = ring.position_spectrum(5, 0, certified)
    try:
        decimal = ring.position_spectrum(10, 0, certified)
    except OpenMahlerRingInletsRequired:
        decimal_packet: dict[str, object] = {
            "mode": "open_inlet_required",
            "source_certification": "no finite periodic wraparound",
        }
    else:
        decimal_packet = {
            "mode": "closed_binary_cone",
            "period": decimal.period,
            "digit_counts": decimal.digit_counts,
            "phase_f5": decimal.phase_f5,
        }
    conditional_packet: dict[str, object] | None = None
    if ring.exponent <= 4 and certified >= 2:
        open_bank = MahlerConditionalOpenMoore.compile(
            ring,
            binary_bits=max(4, ring.exponent + 1),
            five_places=1,
            max_states=2048,
        )
        target, phase_counts, mode = open_bank.source_certified_path(ring, certified)
        conditional_packet = {
            "source_certification": mode,
            "reachable_states": len(open_bank.states),
            "future_moore_classes": open_bank.class_count,
            "endpoint_class": target,
            "six_phase_f5_digit_counts": tuple(value % 5 for value in phase_counts[:6]),
            "six_phase_xor_counts": tuple(phase_counts[6:12]),
            "six_phase_borrow_counts": tuple(phase_counts[12:18]),
        }
    q_temporal: dict[str, object] = {}
    for odd_radix in (3, 5):
        spectrum = ring.q_phase_spectrum(
            odd_radix,
            min(decimal_places, 4),
            certified,
            clock=seam.clock,
            walsh64=walsh and certified >= 64,
        )
        q_temporal[str(odd_radix)] = {
            "certified_copies": spectrum.copies,
            "observed_prefix_length": spectrum.prefix_length,
            "finite_orbit_period": spectrum.period,
            "carry_six_phase_counts": spectrum.carry_phase_counts,
            "borrow_six_phase_counts": spectrum.borrow_phase_counts,
            "xor_six_phase_counts": spectrum.xor_phase_counts,
            "xor_f5": spectrum.xor_f5,
            "walsh64_xor": spectrum.walsh64_xor,
        }
    ring_packet: dict[str, object] = {
        "fixed_exponent": ring.exponent,
        "defect_valuation": ring.defect_valuation,
        "certified_capacity": ring.capacity,
        "powered_copies": certified,
        "source_guard_residue": powered.source_residue,
        "source_guard_modulus": powered.source_modulus,
        "powered_endpoint": projected_endpoint,
        "powered_ledger_delta": powered.delta,
        "powered_ledger_minimum": powered.minimum,
        "ledger_safe": seam.incoming_balance + powered.minimum >= 0,
        "fractional_guard_empty": powered.joint.guard.empty,
        "radix_endpoint": {
            str(base): ring.radix_residue(base, decimal_places, certified)
            for base in (2, 5, 10, 64)
        },
        "five_digit_phase_f5": primary.phase_f5,
        "five_digit_counts": primary.digit_counts,
        "five_odd_orbit_period": primary.period,
        "q_temporal_carry_borrow_harmonics": q_temporal,
        "decimal_position_zero": decimal_packet,
        "conditional_open_bank": conditional_packet,
        "future_scope": "source-certified fixed exponent only; no future exponent guess",
    }
    mixed_packet: dict[str, object] | None = None
    if include_mixed_ring:
        from number_compiler.sequences.antihydra.mahler_mixed_harmonic_ring import (
            MahlerMixedOddHarmonicRing,
        )

        try:
            mixed = MahlerMixedOddHarmonicRing.best_repeating(
                seam.source, max_events=4, min_copies=2
            )
            if mixed is None:
                # Retain only the small actually witnessed word if it cannot
                # be repeated. Its powered certificate still never predicts
                # beyond the available 2-adic source cylinder.
                mixed = MahlerMixedOddHarmonicRing.discover(seam.source, max_events=4)
                mixed_copies = 1
            else:
                mixed_copies = min(
                    mixed.capacity,
                    32,
                    4096 // mixed.extent,
                )
            mixed_packet = mixed.observation(
                repetitions=mixed_copies,
                clock=seam.clock,
                places=min(decimal_places, 6),
                walsh64=walsh,
            )
        except BlockContextBudgetExceeded:
            mixed_packet = {
                "mode": "budget_refused",
                "scope": "finite source-certified mixed motif only",
                "all_time_claim": False,
            }
    # Only the PUBLIC packet has JSON wire keys. Keep integer radix keys
    # on the internal typed demand for existing arithmetic callers.
    harmonics["radix_ports"] = _string_keyed_radix_ports(harmonics)
    q_ports["radix_ports"] = _string_keyed_radix_ports(q_ports)
    return {
        "source": seam.source,
        "odd_index": seam.index,
        "source_clock": seam.clock,
        "incoming_balance": seam.incoming_balance,
        "x": seam.x,
        "run_exponent": seam.exponent,
        "next_odd_source": seam.next_source,
        "next_x": seam.next_x,
        "next_clock": seam.next_clock,
        "next_balance": seam.ending_balance,
        "q_valuation": seam.q_valuation,
        "required_q_valuation": seam.required_valuation,
        "barrier_failure_next_macro": seam.barrier_fails,
        "pointed_source_residue": action.source_residue,
        "pointed_source_modulus": action.source_modulus,
        "prefix_minimum": action.minimum,
        "harmonics": harmonics,
        "q_radix_orbits": q_ports,
        "source_bound_harmonic_ring": ring_packet,
        **(
            {"source_bound_mixed_odd_ring": mixed_packet}
            if mixed_packet is not None
            else {}
        ),
        "barrier_kind": "Antihydra ledger, not Mahler fractional safety",
        "all_time_claim": False,
    }


def _string_keyed_radix_ports(packet: dict[str, object]) -> dict[str, object]:
    raw_ports = packet.get("radix_ports")
    if not is_object_dictionary(raw_ports) or type(raw_ports) is not dict:
        raise ArithmeticError("radix port payload is not a mapping")
    wire_ports: dict[str, object] = {}
    for base, row in raw_ports.items():
        if type(base) is not int or type(row) is not dict:
            raise ArithmeticError("radix port payload has invalid entries")
        wire_ports[str(base)] = row
    return wire_ports


__all__ = (
    "MahlerOddSeamStep",
    "MahlerOddToOddAction",
    "odd_seam_packet",
    "odd_seam_pointwise_packet",
    "odd_seam_step",
)
