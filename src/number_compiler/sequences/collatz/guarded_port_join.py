"""Source-preserving, demand-punctured Collatz boundary/carry relation.

The *one* source cylinder is the authority for the affine, base-6, decimal
100-state, upper-digit and future-border ports. A row is admitted only after
all requested constraints have been pulled back to that original cylinder.
This avoids unguarded Boolean matrix products and treating a forced base-6
carry as a decimal carry. No port supplies an unknown future parity word.

A puncture at normalized time t takes at most 200 decimal-inlet alternatives.
No full 100x100 matrix, digit forest, or speculative scheduler search is built.
One may use a compressed action for large powers and demand only its boundary
cuts; intermediate weighted arrivals require a certified finite inlet program.
"""

from __future__ import annotations

from dataclasses import dataclass
from math import gcd
from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.resources.metric_keys import collatz as _collatz_keys
from number_compiler.sequences.collatz.border_identity import (
    CollatzSegmentIdentity,
)
from number_compiler.sequences.collatz.border_pair_temporal_matrix import (
    GuardedPairEntry,
    WeightedPairMatrix,
    validate_pointed_pair_action,
)
from number_compiler.sequences.collatz.collatz_two_sided_ring import (
    CollatzTwoSidedCylinder,
)
from number_compiler.sequences.collatz.dyadic_terminal_cocycle import (
    DyadicTerminalFieldAction,
)
from number_compiler.sequences.collatz.guarded_port_source import (
    ceil_div as _ceil_div,
)
from number_compiler.sequences.collatz.guarded_port_source import (
    merge_five_source_bands as _merge_five_source_bands,
)
from number_compiler.sequences.collatz.guarded_port_source import (
    restrict_forced_five_suffix as _restrict_forced_five_suffix,
)
from number_compiler.sequences.collatz.guarded_port_source import (
    restrict_source as _restrict,
)
from number_compiler.sequences.collatz.guarded_port_types import (
    GuardedCarryRow,
    GuardedPortCut,
    PortPuncture,
)
from number_compiler.sequences.collatz.guarded_radix6_bridge import (
    FiveBand,
    GuardedRadix6Bridge,
    certify_guarded_radix6_bridge,
    common_plus_one_valuation,
    merge_bands,
    trace_is_zero_tail,
    transport_bands,
)
from number_compiler.sequences.collatz.source_closed_port_action import (
    MacroTraceGrammar,
    SourceClosedPortAction,
    SourceCongruence,
)

if TYPE_CHECKING:
    from number_compiler.resources.ledger import ResourceLedger
    from number_compiler.sequences.collatz.guarded_radix6_bridge import (
        GuardedTemporalCarryCounts,
    )
    from number_compiler.sequences.collatz.named_border_carry_matrix import (
        UnitsCarryMatrix,
    )
    from number_compiler.sequences.collatz.parity_carry_tape import (
        ParityCarryTape,
    )


@dataclass(frozen=True, slots=True)
class GuardedPortJoin:
    """The single port owner for a certified Collatz macro and cylinder.

    Matrix rows are *generated after* intersecting the input guard, any
    inverse-image upper/digit/border constraints, the base-6 5-suffix
    congruence and the original physical action. Later guards cannot be
    joined after the matrix has lost their original source correlations.
    """

    source: CollatzTwoSidedCylinder
    port: SourceClosedPortAction
    bridge: GuardedRadix6Bridge
    named_macro: object | None = None
    factor_grammar: tuple[tuple[tuple[int, ...], int], ...] | None = None
    factor_repetitions: int = 1
    parity_tape: ParityCarryTape | None = None

    def __post_init__(self) -> None:
        if (
            type(self.source) is not CollatzTwoSidedCylinder
            or type(self.port) is not SourceClosedPortAction
            or type(self.bridge) is not GuardedRadix6Bridge
        ):
            raise TypeError(
                "port join requires a cylinder, issued action and base-6 certificate"
            )
        self.port.verify_issued()
        if (
            self.bridge.action.coefficient_snapshot()
            != self.port.action.coefficient_snapshot()
            or self.bridge.odd_events != self.port.odd_events
            or self.bridge.inlet != self.source
        ):
            raise ValueError("source-bound spatial certificate differs from action")
        if (
            self.source.count > 1 and self.source.modulus % self.port.guard.modulus
        ) or (
            not self.port.guard.admits(self.source.first)
            or not self.port.guard.admits(self.source.last)
        ):
            raise ValueError(
                "port join source is not contained in original action guard"
            )
        if self.source.transport(self.port.action) != self.bridge.target:
            raise ArithmeticError("port join disagrees on the authenticated endpoint")
        if self.factor_grammar is not None:
            if self.named_macro is not None:
                raise ValueError(
                    "named and composed prefix grammars cannot both own the port"
                )
            if type(self.factor_repetitions) is not int or self.factor_repetitions < 1:
                raise ValueError("composed macro repetitions must be positive")
            block = DyadicTerminalFieldAction.identity()
            odd_count = 0
            for motif, repetitions in self.factor_grammar:
                if (
                    type(motif) is not tuple
                    or not 1 <= len(motif) <= 64
                    or any(type(bit) is not int or bit not in (0, 1) for bit in motif)
                    or type(repetitions) is not int
                    or repetitions < 1
                ):
                    raise ValueError("invalid authenticated factor grammar")
                word = DyadicTerminalFieldAction.identity()
                for bit in motif:
                    word = word.then(
                        DyadicTerminalFieldAction.one_run(1)
                        if bit
                        else DyadicTerminalFieldAction.zero_run(1)
                    )
                block = block.then(word.power(repetitions))
                odd_count += sum(motif) * repetitions
            if (
                block.steps == 0
                or block.power(self.factor_repetitions).coefficient_snapshot()
                != self.port.action.coefficient_snapshot()
                or odd_count * self.factor_repetitions != self.port.odd_events
            ):
                raise ValueError(
                    "composed carry factors differ from the issued temporal action"
                )
        elif self.factor_repetitions != 1:
            raise ValueError("orphaned composed carry repetition count")
        if self.named_macro is not None:
            from number_compiler.sequences.collatz.border_return_grammar import (
                BorderReturnMacro,
                validate_border_return_macro,
            )
            from number_compiler.sequences.collatz.boundary_macros import (
                CollatzBoundaryMacro,
                validate_boundary_macro,
            )

            if type(self.named_macro) is CollatzBoundaryMacro:
                validate_boundary_macro(self.named_macro)
            elif type(self.named_macro) is BorderReturnMacro:
                validate_border_return_macro(self.named_macro)
            else:
                raise TypeError(
                    "only a producer-issued macro may drive the matrix prefix"
                )
            if (
                self.named_macro.fields.coefficient_snapshot()
                != self.port.action.coefficient_snapshot()
                or self.named_macro.odd_symbols != self.port.odd_events
                or not self.source.contains(self.named_macro.source)
                or self.named_macro.endpoint
                != self.port.endpoint(self.named_macro.source)
            ):
                raise ValueError("named matrix prefix belongs to another issued action")
        if self.parity_tape is not None:
            from number_compiler.sequences.collatz.parity_carry_tape import (
                ParityCarryTape,
            )

            if (
                type(self.parity_tape) is not ParityCarryTape
                or self.parity_tape.steps != self.port.action.steps
                or self.parity_tape.odds != self.port.odd_events
                or self.parity_tape.action().coefficient_snapshot()
                != self.port.action.coefficient_snapshot()
            ):
                raise ValueError("retained parity tape differs from the issued action")

    def parity_tape_for_action(self) -> ParityCarryTape | None:
        """Return only an already-retained, source-validated parity grammar."""
        if self.parity_tape is not None:
            return self.parity_tape
        from number_compiler.sequences.collatz.parity_carry_tape import (
            ParityCarryTape,
        )

        if self.factor_grammar is not None:
            return ParityCarryTape.factors(
                self.factor_grammar, repetitions=self.factor_repetitions
            )
        macro = self.named_macro
        if macro is None:
            return None
        return ParityCarryTape.from_named_macro(macro)

    def _prefix(self, time: int) -> tuple[DyadicTerminalFieldAction, int]:
        """Recover a *proved* prefix from the issued parity residue, not a guess.

        The producer's full source guard is what authorizes the parity path;
        its integer representative is only used to decode the local letters.
        """
        if type(time) is not int or not 0 <= time <= self.port.action.steps:
            raise ValueError("time puncture outside issued normalized action")
        if time == self.port.action.steps:
            return self.port.action, self.port.odd_events
        tape = self.parity_tape_for_action()
        if tape is not None:
            action = tape.prefix_action(time)
            odds = tape.prefix_odds(time)
            if (
                not action.certifies(self.source.first)
                or not action.certifies(self.source.last)
                or (
                    self.source.count > 1
                    and self.source.modulus % action.source_modulus
                )
            ):
                raise ArithmeticError(
                    "retained parity grammar violates its source guard"
                )
            return action, odds
        x = self.source.first
        action = DyadicTerminalFieldAction.identity()
        odds = 0
        for _ in range(time):
            odd = x & 1
            action = action.then(
                DyadicTerminalFieldAction.one_run(1)
                if odd
                else DyadicTerminalFieldAction.zero_run(1)
            )
            x = ((3 * x + 1) // 2) if odd else (x // 2)
            odds += odd
        if not action.certifies(self.source.first) or not action.certifies(
            self.source.last
        ):
            raise ArithmeticError("prefix parity was not forced on the complete source")
        # The full issuing guard implies this prefix, not merely a sample.
        if self.source.count > 1 and self.source.modulus % action.source_modulus:
            raise ArithmeticError(
                "source cylinder does not force the decoded parity prefix"
            )
        return action, odds

    def _base_fives(
        self,
        time: int,
        prefix: DyadicTerminalFieldAction,
        odds: int,
        *,
        demand: bool,
        narrowed: CollatzTwoSidedCylinder | None = None,
    ) -> tuple[FiveBand, ...]:
        if not demand:
            return ()
        cylinder = self.source if narrowed is None else narrowed
        if time == self.port.action.steps:
            return self.bridge.restrict_to(cylinder).target_fives
        if time == 0:
            return self.bridge.restrict_to(cylinder).source_fives
        # Carry reset is a source-wide 6-adic fact: previously certified
        # bands can be transported through the exact prefix without another
        # radix conversion.  If a narrower port forces additional trailing
        # fives, the 2/3-adic valuations supply them algebraically.
        starts = self.bridge.restrict_to(cylinder).source_fives
        inherited = transport_bands(starts, odds, time)
        born: tuple[FiveBand, ...] = ()
        if prefix.offset + (1 << time) == prefix.gain:
            v2 = common_plus_one_valuation(cylinder, 2)
            v3 = common_plus_one_valuation(cylinder, 3)
            if v2 < time:
                raise ArithmeticError("source narrowed beyond certified parity guard")
            k = min(v2 - time, v3 + odds)
            if k:
                born = (FiveBand(0, k),)
        return merge_bands(inherited + born)

    def puncture(
        self,
        time: int,
        request: PortPuncture | None = None,
        *,
        pointed_source: int | None = None,
        max_rows: int = 200,
        max_prefix_steps: int = 512,
    ) -> GuardedPortCut:
        """Exact guarded matrix intersection for one demanded temporal port.

        Both time ``0`` and the final time are valid. At the final time the
        only local row is an identity (zero new carries); future border/F5
        constraints still pull back through the powered action.
        """
        if request is None:
            request = PortPuncture()
        if type(request) is not PortPuncture:
            raise TypeError(
                "Collatz puncture requires explicit bounded port requirements"
            )
        if type(max_rows) is not int or not 1 <= max_rows <= 200:
            raise ValueError("punctured matrix row budget must be 1..200")
        if type(max_prefix_steps) is not int or not 0 <= max_prefix_steps <= 4096:
            raise ValueError("punctured matrix prefix budget must be 0..4096")
        if type(time) is not int or not 0 <= time <= self.port.action.steps:
            raise ValueError("time puncture outside issued normalized action")
        if time not in (0, self.port.action.steps) and time > max_prefix_steps:
            raise BlockContextBudgetExceeded(
                "intermediate source prefix exceeds the puncture budget"
            )
        prefix, odds = self._prefix(time)
        prefix_scalar_steps = time if time not in (0, self.port.action.steps) else 0
        current = self.source.transport(prefix)
        base: CollatzTwoSidedCylinder | None = self.source
        # Future-low borders and F5 upper-numerator rings are *source* guards,
        # not additional untracked observations after a matrix multiply.
        if request.future_border is not None:
            g = SourceCongruence(request.future_border, 10).pullback(prefix)
            base = None if g is None else _restrict(self.source, g)
        if base is not None and request.numerator_f5 is not None:
            # At a 3-border, (3*x+1)/10 ≡s (mod 5) fixes x modulo 50.
            s = request.numerator_f5
            residue = ((10 * s - 1) * pow(3, -1, 50)) % 50
            if residue % 10 != 3:
                raise ArithmeticError("numerator residue inversion broke the 3-border")
            g = SourceCongruence(residue, 50).pullback(prefix)
            base = None if g is None else _restrict(base, g)
        # CRT 99/198/25 clocks constrain the SAME original source, rather
        # than being checked on the scalar endpoint after selecting a macro.
        for modulus, residue in request.clock_residues:
            if base is None:
                break
            g = SourceCongruence(residue, modulus).pullback(prefix)
            base = None if g is None else _restrict(base, g)
        if base is not None and request.upper_word is not None:
            width, digits, word = request.upper_word
            scale = 6 ** (width - digits)
            low, high = word * scale, (word + 1) * scale - 1
            low = max(low, 6 ** (width - 1))
            high = min(high, 6**width - 1)
            if low > high:
                base = None
            else:
                den = 1 << prefix.steps
                low_x = _ceil_div(den * low - prefix.offset, prefix.gain)
                high_x = (den * high - prefix.offset) // prefix.gain
                base = base.intersect_interval(low_x, high_x)
        demand_fives = request != PortPuncture()
        fives = (
            self._base_fives(
                time,
                prefix,
                odds,
                demand=demand_fives,
                narrowed=base,
            )
            if base is not None
            else ()
        )
        # 5-runs might become provable ONLY AFTER a decimal-pair or
        # upper-inlet cut. Do not refuse a requested reset using the wider
        # pre-puncture cylinder: evaluate source-wide 5s per surviving row.
        step_exists = time < self.port.action.steps
        next_odd = current.forced_residue(2) if step_exists else None
        if step_exists and next_odd is None:
            raise ArithmeticError("issued source did not force the next parity inlet")
        if request.five_carry is not None and (
            not step_exists or next_odd != 1 or request.five_carry != 2
        ):
            return GuardedPortCut(
                time, self.source, (), fives, prefix, prefix_scalar_steps
            )
        if request.five_remainder is not None and (
            not step_exists or request.five_remainder != 1
        ):
            return GuardedPortCut(
                time, self.source, (), fives, prefix, prefix_scalar_steps
            )
        if base is None:
            return GuardedPortCut(
                time, self.source, (), fives, prefix, prefix_scalar_steps
            )
        # A certified 5-suffix is x_t ≡ -1 (mod 6**k). Pull it back
        # BEFORE materializing decimal matrix entries. For non-suffix bands,
        # keep the exact certified cylinder and the reset wire; equating it
        # to a decimal carry would be mathematically invalid.
        for band in fives:
            if band.lower == 0:
                base = _restrict_forced_five_suffix(base, prefix, band)
                if base is None:
                    raise ArithmeticError(
                        "certified base-6 five suffix contradicts source"
                    )
        stage = base.transport(prefix)
        n = min(stage.count, 200 // gcd(stage.modulus, 200))
        residues: tuple[int, ...]
        if pointed_source is not None:
            if type(pointed_source) is not int or not base.contains(pointed_source):
                raise ValueError("pointed Collatz source is outside joined guard")
            residues = (prefix.endpoint(pointed_source) % 200,)
        else:
            residues = tuple((stage.first + stage.modulus * j) % 200 for j in range(n))
        if len(residues) > max_rows:
            raise BlockContextBudgetExceeded(
                "source-punctured 100x100 row budget exceeded"
            )
        identity = time == self.port.action.steps
        result: list[GuardedCarryRow] = []
        for residue in residues:
            pair, upper = residue % 100, residue // 100
            if request.input_pair is not None and pair != request.input_pair:
                continue
            if request.upper_parity is not None and upper != request.upper_parity:
                continue
            incoming = SourceCongruence(residue, 200).pullback(prefix)
            if incoming is None:
                continue
            guard = self.port.guard.meet(incoming)
            if guard is None:
                continue
            root = _restrict(base, guard)
            if root is None:
                continue
            if identity:
                odd, successor, c1, c2 = 0, pair, 0, 0
                image = root.transport(prefix)
            else:
                odd = pair & 1
                matrix = (
                    WeightedPairMatrix.odd_half(upper)
                    if odd
                    else WeightedPairMatrix.even(upper)
                )
                values = matrix.successors(pair)
                if len(values) != 1:
                    raise ArithmeticError(
                        "source-forced parity has no decimal matrix successor"
                    )
                successor, c1, c2 = values[0]
                step = (
                    DyadicTerminalFieldAction.one_run(1)
                    if odd
                    else DyadicTerminalFieldAction.zero_run(1)
                )
                image = root.transport(prefix.then(step))
                if image.forced_residue(100) != successor:
                    raise ArithmeticError(
                        "source-punctured pair matrix disagrees with transport"
                    )
            if (
                request.output_pair is not None
                and successor != request.output_pair
                or request.tens is not None
                and c1 != request.tens
                or request.hundreds is not None
                and c2 != request.hundreds
            ):
                continue
            local_fives = fives
            if demand_fives and root != base:
                local_fives = _merge_five_source_bands(
                    fives,
                    self._base_fives(
                        time,
                        prefix,
                        odds,
                        demand=True,
                        narrowed=root,
                    ),
                )
            if (request.five_carry is not None and not local_fives) or (
                request.five_remainder is not None
                and not any(band.upper - band.lower > odd for band in local_fives)
            ):
                # Explicit 5-run requests may require upper, non-suffix
                # digits newly certified by the narrowed endpoint interval.
                # Pay for complete positional coverage only on this missing
                # port, never for every ordinary matrix/admission seam.
                expanded = certify_guarded_radix6_bridge(
                    root,
                    prefix,
                    odds,
                    max_upper_digits=12,
                    max_lower_digits=32,
                )
                local_fives = _merge_five_source_bands(
                    local_fives,
                    expanded.target_fives,
                )
            if request.five_carry is not None and not local_fives:
                continue
            if request.five_remainder is not None and not any(
                band.upper - band.lower > odd for band in local_fives
            ):
                continue
            # At every surviving row, the proved 5-suffix must itself have
            # a nonempty original-source CRT preimage. Verify conservation
            # rather than equating base-6 reset wires with decimal carries.
            for band in local_fives:
                if band.lower == 0:
                    matched = _restrict_forced_five_suffix(root, prefix, band)
                    if matched is None or matched.count != root.count:
                        raise ArithmeticError(
                            "joint matrix row contradicts forced six-adic suffix"
                        )
            result.append(
                GuardedCarryRow(
                    guard,
                    root,
                    time,
                    pair,
                    upper,
                    odd,
                    successor,
                    c1,
                    c2,
                    image,
                    local_fives,
                )
            )
        result.sort(key=lambda row: (row.input_pair, row.upper_parity))
        if (
            pointed_source is None
            and request == PortPuncture()
            and sum(row.count for row in result) != self.source.count
        ):
            raise ArithmeticError(
                "source-aligned decimal matrix lost a source alternative"
            )
        return GuardedPortCut(
            time, self.source, tuple(result), fives, prefix, prefix_scalar_steps
        )

    def then(self, after: GuardedPortJoin) -> GuardedPortJoin | None:
        """Source-pulled guard join, retaining intermediate 5 births.

        If the next source fiber is only a subcylinder of this action's
        target, rebuild both certificates on that smaller fiber BEFORE
        composing.  Mere coincident Moore labels are never a valid join.
        """
        if type(after) is not GuardedPortJoin:
            raise TypeError("guarded port composition requires another joint port")
        combined = self.port.then(after.port)
        if combined is None:
            return None
        root = _restrict(self.source, combined.guard)
        if root is None:
            return None
        seam = root.transport(self.port.action)
        if (
            seam.first < after.source.first
            or seam.last > after.source.last
            or (seam.count > 1 and seam.modulus % after.source.modulus != 0)
            or not after.source.contains(seam.first)
            or not after.source.contains(seam.last)
        ):
            raise ValueError("guarded port join has no complete authenticated seam")
        # A proof on a wider cylinder remains valid on its source subset;
        # algebraically enrich only newly forced 6-adic suffixes. Re-running
        # radix-6 upper coverage at every seam used to dominate the CLI.
        first = self.bridge.restrict_to(root)
        second = after.bridge.restrict_to(seam)
        first_tape = self.parity_tape_for_action()
        second_tape = after.parity_tape_for_action()
        tape = None
        if first_tape is not None and second_tape is not None:
            from number_compiler.sequences.collatz.parity_carry_tape import (
                ParityCarryTape,
            )

            tape = ParityCarryTape.sequence((first_tape, second_tape))
        return GuardedPortJoin(
            root,
            combined,
            first.then(second),
            parity_tape=tape,
        )

    def prefix_units(self, time: int) -> UnitsCarryMatrix:
        """Demand the authenticated five-state weighted prefix of this tape."""
        tape = self.parity_tape_for_action()
        if tape is None:
            raise ValueError("source join has no certified parity prefix tape")
        if type(time) is not int or not 0 <= time <= self.port.action.steps:
            raise ValueError("weighted prefix outside issued action")
        return tape.prefix_units(time)

    def future_family_partition(
        self,
    ) -> tuple[tuple[CollatzSegmentIdentity | None, CollatzTwoSidedCylinder], ...]:
        """Partition the source by the shared future-family classifier."""
        from number_compiler.sequences.collatz.guarded_port_partitions import (
            future_family_partition,
        )

        return future_family_partition(self)

    def future_border_partition(self) -> tuple[tuple[int, GuardedPortJoin], ...]:
        """Partition all source alternatives by their next decimal border."""
        from number_compiler.sequences.collatz.guarded_port_partitions import (
            future_border_partition,
        )

        return future_border_partition(self)

    def future_tails(
        self,
        *,
        max_tail: int = 12,
    ) -> tuple[tuple[int | None, GuardedPortJoin], ...]:
        """Demand exact source-guarded tails from the family partitioner."""
        from number_compiler.sequences.collatz.guarded_port_partitions import (
            future_tails,
        )

        return future_tails(self, max_tail=max_tail)

    def future_border(self, digit: int) -> GuardedPortJoin | None:
        """Puncture an authenticated border *before* the next macro is chosen."""
        if type(digit) is not int or not 0 <= digit <= 9:
            raise ValueError("future border digit must be 0..9")
        pulled = SourceCongruence(digit, 10).pullback(self.port.action)
        if pulled is None:
            return None
        guard = self.port.guard.meet(pulled)
        if guard is None:
            return None
        root = _restrict(self.source, guard)
        if root is None:
            return None
        # Retain the same issued parity word and affine coefficients; only
        # narrow its source guard using an exact inverse-image constraint.
        port = SourceClosedPortAction(
            self.port.action,
            guard,
            self.port.odd_events,
            self.port.clock,
            self.port.trace,
        )
        bridge = self.bridge.restrict_to(root)
        return GuardedPortJoin(
            root, port, bridge, parity_tape=self.parity_tape_for_action()
        )

    def require_pointed(
        self, source: int, *, check_last: bool = True
    ) -> tuple[GuardedCarryRow, GuardedCarryRow | None]:
        """Authenticate local carry inlet and powered pair outlet before admission."""
        first = self.puncture(
            0, PortPuncture(input_pair=source % 100), pointed_source=source
        ).pointed(source)
        if first is None:
            raise ArithmeticError("joined source guard refused the first carry row")
        last = None
        if check_last:
            target = self.port.endpoint(source)
            last = self.puncture(
                self.port.action.steps,
                PortPuncture(input_pair=target % 100, future_border=target % 10),
                pointed_source=source,
            ).pointed(source)
            if last is None or last.output_pair != target % 100:
                raise ArithmeticError(
                    "joined upper/lower border constraints reject endpoint"
                )
        return first, last

    def powered_zero_tail_carries(
        self,
        source: int,
    ) -> tuple[int, int, int, int, int, int] | None:
        """Power a *proved* five-phase 100x100 carry inlet program.

        For N successive zero-tail 6305 returns x'+1=9(x+1)/4.
        A source-wide valuation v2(x+1)>=2*N+2 forces x_k=-1 mod16
        at the start of EVERY return, including the last. Meanwhile
        (x_k+1) mod25 multiplies by 21, an element of order 5. CRT(16,25)
        determines x_k mod400 and therefore both upper-parity inlets of
        the two normalized odd steps in each return. The ten inlet matrices
        repeat after five returns, and only *then* is temporal squaring
        authorized. For any shorter valuation or mixed trace, return None.

        This is a genuine guarded weighted 100x100 matrix power; no scalar
        trajectory is enumerated, and no guessed carry-arrival period is used.
        """
        if not self.source.contains(source):
            raise ValueError("powered carry source is outside its original guard")
        from number_compiler.sequences.collatz.guarded_radix6_bridge import (
            common_plus_one_valuation,
        )

        trace = self.port.trace
        if type(trace) is not MacroTraceGrammar or trace.length == 0:
            return None
        n = trace.length
        if n > 8192 or self.port.action.steps != 2 * n or self.port.odd_events != 2 * n:
            return None
        if not self.bridge.centered_at_minus_one:
            return None
        if not trace_is_zero_tail(trace):
            return None
        if common_plus_one_valuation(self.source, 2) < 2 * n + 2:
            return None
        # The full source class must force x mod25, or be a singleton.
        phase = self.source.forced_residue(25)
        if phase is None:
            return None
        # A five-return cycle is determined entirely by the forced 2-adic
        # suffix and this mod25 phase. 21^5=1 (mod 25).
        if pow(21, 5, 25) != 1:
            raise ArithmeticError("low cyclotomic carry clock is not period five")
        inv16 = pow(16, -1, 25)
        cycle = WeightedPairMatrix.identity()
        letters: list[WeightedPairMatrix] = []
        compositions = 0
        for k in range(5):
            residue25 = (pow(21, k, 25) * (phase + 1) - 1) % 25
            source400 = 15 + 16 * (((residue25 - 15) * inv16) % 25)
            after_first200 = ((3 * source400 + 1) // 2) % 200
            one = WeightedPairMatrix.odd_half((source400 // 100) & 1)
            two = WeightedPairMatrix.odd_half((after_first200 // 100) & 1)
            cycle = cycle.then(one).then(two)
            compositions += 2
            letters.extend((one, two))
        q, r = divmod(n, 5)
        powered, power_compositions, squarings = cycle.power_with_work(q)
        compositions += power_compositions
        for matrix in letters[: 2 * r]:
            powered = powered.then(matrix)
            compositions += 1
        row = powered.successors(source % 100)
        if len(row) != 1:
            raise ArithmeticError(
                "five-phase 100-state source row is not deterministic"
            )
        last, c1, c2 = row[0]
        if last != self.port.endpoint(source) % 100:
            raise ArithmeticError("guarded five-phase carry matrix lost the endpoint")
        return c1, c2, 2 * n, last, compositions, squarings

    def authenticate_weighted_ports(
        self,
        source: int,
        *,
        max_steps: int = 512,
    ) -> GuardedTemporalCarryCounts:
        """Intersect EVERY demanded temporal matrix row with its source guard.

        At stage t, the original source must imply the entire 200-state
        inlet letter under the affine prefix, as well as every available
        source-wide base-6 5-suffix reset. The matrix then yields the exact
        two decimal carry arrivals. On an authenticated five-phase period the
        same proof uses the logarithmic powered matrix, not a linear walk.
        """
        from number_compiler.sequences.collatz.guarded_radix6_bridge import (
            GuardedTemporalCarryCounts,
            common_plus_one_valuation,
            merge_bands,
        )

        steps = self.port.action.steps
        if type(max_steps) is not int or not 0 <= max_steps <= 4096:
            raise ValueError("invalid joined matrix temporal budget")
        if type(source) is not int or not self.source.contains(source):
            raise ValueError("temporal inlet source is outside joint source guard")
        program_modulus = 200 << steps
        program_guard = SourceCongruence(source % program_modulus, program_modulus)
        fiber = _restrict(self.source, program_guard)
        if fiber is None or not fiber.contains(source):
            raise ArithmeticError(
                "temporal inlet preimage has no original-source fiber"
            )
        # The special five-return cycle is proved for the COMPLETE original
        # joined cylinder. It must never be inferred from just a pointed root.
        powered = self.powered_zero_tail_carries(source)
        if powered is not None:
            tens, hundreds, odds, last, compositions, squarings = powered
            return GuardedTemporalCarryCounts.create_checked(
                program_guard,
                steps,
                odds,
                tens,
                hundreds,
                last,
                matrix_power_period=5,
                forced_six_reset_events=0,
                port_punctures=0,
                matrix_compositions=compositions,
                matrix_squarings=squarings,
                scalar_steps=0,
            )
        if steps > max_steps:
            raise BlockContextBudgetExceeded(
                "unproved nonperiodic carry-inlet program exceeds its budget"
            )
        value = source
        prefix = DyadicTerminalFieldAction.identity()
        odds = tens = hundreds = resets = remainders = 0
        # All source alternatives inside the *inlet guard* have these
        # guaranteed base-6 fives; the original wider source cannot be used
        # as a substitute for a stricter source-derived observation.
        original_cover = certify_guarded_radix6_bridge(
            fiber,
            prefix,
            0,
            max_upper_digits=0,
            max_lower_digits=32,
        )
        bands = original_cover.source_fives
        v2 = common_plus_one_valuation(fiber, 2)
        v3 = common_plus_one_valuation(fiber, 3)
        for t in range(steps):
            # Detect newly born fives from the exact centered affine action,
            # then put their 6-adic congruence into the ORIGINAL source guard.
            if prefix.offset + (1 << t) == prefix.gain and v2 >= t:
                born = min(v2 - t, v3 + odds)
                if born:
                    bands = merge_bands(bands + (FiveBand(0, born),))
            odd_now = value & 1
            for band in bands:
                if odd_now:
                    resets += band.upper - band.lower
                remainders += max(0, band.upper - band.lower - odd_now)
                if band.lower == 0:
                    checked = _restrict_forced_five_suffix(fiber, prefix, band)
                    if checked is None or checked.count != fiber.count:
                        raise ArithmeticError(
                            "forced radix-6 carry reset contradicts a matrix source row"
                        )
            letter = SourceCongruence(value % 200, 200).pullback(prefix)
            constrained = None if letter is None else _restrict(fiber, letter)
            if constrained is None or constrained.count != fiber.count:
                raise ArithmeticError(
                    "weighted matrix inlet is not forced by its complete source guard"
                )
            pair, high, odd = value % 100, (value // 100) & 1, value & 1
            matrix = (
                WeightedPairMatrix.odd_half(high)
                if odd
                else WeightedPairMatrix.even(high)
            )
            rows = matrix.successors(pair)
            if len(rows) != 1:
                raise ArithmeticError(
                    "guarded decimal inlet has no normalized successor"
                )
            output, c1, c2 = rows[0]
            step = (
                DyadicTerminalFieldAction.one_run(1)
                if odd
                else DyadicTerminalFieldAction.zero_run(1)
            )
            next_value = ((3 * value + 1) // 2) if odd else value // 2
            if next_value % 100 != output:
                raise ArithmeticError(
                    "forced carry/matrix output contradicts exact affine step"
                )
            prefix = prefix.then(step)
            odds += odd
            tens += c1
            hundreds += c2
            value = next_value
            bands = merge_bands(
                tuple(
                    carried
                    for band in bands
                    if (carried := band.through(odd, 1)) is not None
                )
            )
        if (
            prefix.coefficient_snapshot() != self.port.action.coefficient_snapshot()
            or odds != self.port.odd_events
            or value != self.port.endpoint(source)
        ):
            raise ArithmeticError("joined matrix tape disagrees with the issued macro")
        return GuardedTemporalCarryCounts.create_checked(
            program_guard,
            steps,
            odds,
            tens,
            hundreds,
            value % 100,
            matrix_power_period=None,
            forced_six_reset_events=resets,
            forced_six_div_remainders=remainders,
            port_punctures=steps,
            scalar_steps=steps,
        )

    def weighted_pointed_program(
        self, source: int, *, max_steps: int = 512
    ) -> tuple[int, int, int, int]:
        """Compatibility projection of the single authenticated weighted port."""
        result = self.authenticate_weighted_ports(source, max_steps=max_steps)
        return (
            result.carry_tens,
            result.carry_hundreds,
            result.odds,
            result.last_pair,
        )


def certify_pointed_port_join(
    source: int,
    action: DyadicTerminalFieldAction,
    odd_events: int,
    *,
    bridge: GuardedRadix6Bridge | None = None,
    trace: MacroTraceGrammar | tuple[int, ...] = (),
    ledger: ResourceLedger | None = None,
    macro: object | None = None,
    source_cylinder: CollatzTwoSidedCylinder | None = None,
    factor_grammar: tuple[tuple[tuple[int, ...], int], ...] | None = None,
    factor_repetitions: int = 1,
    pointed_pair: GuardedPairEntry | None = None,
) -> GuardedPortJoin:
    """Rejoin a named 6305/8/9 macro to its actual source carry rows."""
    if (
        type(source) is not int
        or source <= 0
        or type(action) is not DyadicTerminalFieldAction
        or not action.producer_issued
        or type(odd_events) is not int
        or not 0 <= odd_events <= action.steps
        or type(trace) not in (tuple, MacroTraceGrammar)
    ):
        raise ValueError("named border join requires an issued action and pointed root")
    guard = SourceCongruence(action.source_residue, action.source_modulus).meet(
        SourceCongruence(source % 10, 10)
    )
    if guard is None or not guard.admits(source):
        raise ArithmeticError("named border guard contradicts the parity action")
    grammar = MacroTraceGrammar.leaf(trace) if type(trace) is tuple else trace
    port = SourceClosedPortAction(action, guard, odd_events, None, grammar)
    if source_cylinder is None:
        source_cylinder = CollatzTwoSidedCylinder(source, source, 0, 1)
    elif type(
        source_cylinder
    ) is not CollatzTwoSidedCylinder or not source_cylinder.contains(source):
        raise ValueError("named matrix source class does not contain pointed root")
    if bridge is None:
        bridge = certify_guarded_radix6_bridge(
            source_cylinder, action, odd_events, ledger=ledger
        )
    elif bridge.inlet != source_cylinder:
        raise ValueError("named macro bridge and requested source class disagree")
    joined = GuardedPortJoin(
        bridge.inlet,
        port,
        bridge,
        named_macro=macro,
        factor_grammar=factor_grammar,
        factor_repetitions=factor_repetitions,
    )
    if pointed_pair is None:
        joined.require_pointed(source)
    else:
        endpoint = validate_pointed_pair_action(pointed_pair, source, action)
        if not joined.bridge.target.contains(endpoint):
            raise ArithmeticError("pointed pair misses joined bridge endpoint")
        if ledger is not None:
            ledger.bump(_collatz_keys.COLLATZ_POINTED_PAIR_CERTIFICATE_REUSES)
    return joined


__all__ = [
    "GuardedCarryRow",
    "GuardedPortCut",
    "GuardedPortJoin",
    "PortPuncture",
    "certify_pointed_port_join",
]
