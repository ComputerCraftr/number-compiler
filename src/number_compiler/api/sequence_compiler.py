"""Canonical cross-family sequence compiler.

The compiler is intentionally small and production-only: it imports no tests,
benchmarks, release probes, or encoding-analysis modules.  Every cache key is a
semantic frozen specification.  Family-specific analysis is retained only when
it is an exact by-product of the compiled representation.
"""

from __future__ import annotations

from typing import TYPE_CHECKING, overload

from number_compiler.api.sequence_types import (
    CollatzCompilation,
    CollatzSequenceSpec,
    FermatCompilation,
    FermatCompiledTerm,
    FermatSequenceSpec,
    MersenneCompilation,
    MersenneCompiledTerm,
    MersenneSequenceSpec,
    PrimeBlockCompilation,
    PrimeBlockSequenceSpec,
    PrimeFactoredAutomatonCompilation,
    ReverseAddCompilation,
    ReverseAddSequenceSpec,
    SequenceCompilation,
    SequenceSpec,
)
from number_compiler.arithmetic.automata.program_word import from_runs
from number_compiler.arithmetic.contracts.input_validation import require_integer
from number_compiler.arithmetic.fields.digit_formula import DigitSpec
from number_compiler.arithmetic.formula.summary import get_summary
from number_compiler.arithmetic.formula.types import RadixSpec
from number_compiler.sequences.power_numbers.numbers import (
    FermatNumberSpec,
    MersenneNumberSpec,
    fermat_radix_reinterpretation,
    mersenne_radix_reinterpretation,
    special_modulus_matches,
)

if TYPE_CHECKING:
    from number_compiler.arithmetic.formula.symmetry_frame import (
        ReverseAddSymmetryLinearAction,
    )
    from number_compiler.arithmetic.polynomials.cyclotomic_transport import (
        PowerTwoCyclotomicRadialQuotient,
    )
    from number_compiler.projection.output_quotient import (
        BinaryOutputCoordinate,
        SpecialBranchMask,
    )
    from number_compiler.sequences.power_numbers.germ import SpecialGermConstraintState
    from number_compiler.sequences.power_numbers.theorem_query import (
        SpecialTheoremResolution,
    )


class CanonicalSequenceCompiler:
    """One semantic cache for every supported concrete sequence family."""

    __slots__ = ("_cache", "_special_constraint_cache", "_theorem_cache")

    def __init__(self) -> None:
        self._cache: dict[tuple[object, ...], SequenceCompilation] = {}
        self._theorem_cache: dict[tuple[object, ...], SpecialTheoremResolution] = {}
        # family/parameter -> accumulated theorem-sheet survivor mask.  This is
        # the lazy tropical kernel: one two-bit coordinate, never a factor-slot list.
        self._special_constraint_cache: dict[tuple[str, int], object] = {}

    @overload
    def compile(
        self, spec: ReverseAddSequenceSpec, *, diagnostics: bool = False
    ) -> ReverseAddCompilation: ...

    @overload
    def compile(
        self, spec: CollatzSequenceSpec, *, diagnostics: bool = False
    ) -> CollatzCompilation: ...

    @overload
    def compile(
        self, spec: PrimeBlockSequenceSpec, *, diagnostics: bool = False
    ) -> PrimeBlockCompilation: ...

    @overload
    def compile(
        self, spec: FermatSequenceSpec, *, diagnostics: bool = False
    ) -> FermatCompilation: ...

    @overload
    def compile(
        self, spec: MersenneSequenceSpec, *, diagnostics: bool = False
    ) -> MersenneCompilation: ...

    def compile(
        self, spec: SequenceSpec, *, diagnostics: bool = False
    ) -> SequenceCompilation:
        """Compile the requested semantic object.

        ``diagnostics=False`` is the production path: it does not materialize
        complete formula values or execute research-only auxiliary traversals.
        ``diagnostics=True`` adds the release/accounting views while preserving
        the same semantic result.  The mode is part of the cache identity so a
        diagnostic object can never alias the cheaper semantic compilation.
        """
        from number_compiler.sequences.prime.lane_quotient import (
            canonical_prime_base_period,
            compile_prime_block_lane_quotient,
        )

        if type(diagnostics) is not bool:
            raise TypeError("diagnostics must be a Boolean")
        spec_types = (
            ReverseAddSequenceSpec,
            CollatzSequenceSpec,
            PrimeBlockSequenceSpec,
            FermatSequenceSpec,
            MersenneSequenceSpec,
        )
        if type(spec) not in spec_types:
            raise TypeError("compiler requires an exact sequence specification")
        # Frozen construction is not authority after adversarial deserialization
        # or object.__setattr__. Revalidate before a warm semantic-key lookup.
        spec.__post_init__()
        key = (*spec.canonical_key, "diagnostics", diagnostics)
        old = self._cache.get(key)
        if old is not None:
            return old
        if type(spec) is ReverseAddSequenceSpec:
            out: SequenceCompilation = self._compile_reverse_add(
                spec, diagnostics=diagnostics
            )
        elif type(spec) is CollatzSequenceSpec:
            from number_compiler.api.collatz_compilation import _compile_collatz

            out = _compile_collatz(spec, diagnostics=diagnostics)
        elif type(spec) is PrimeBlockSequenceSpec:
            # The residual-divisor set morphism is the sole semantic block
            # projection.  The packed congruence automaton, primary jets and
            # translation sensitivity are orthogonal diagnostic/random-access
            # views and are built only when explicitly requested.
            decision = compile_prime_block_lane_quotient(
                spec.start,
                spec.length,
                base_period=canonical_prime_base_period(spec.length),
                include_primary_jet=False,
                include_wheel_cyclotomic=(diagnostics or spec.random_access),
            )
            automaton_view = None
            translation_sensitivity = None
            if diagnostics:
                from math import isqrt

                from number_compiler.arithmetic.fields.adic_morphism import (
                    prime_translation_sensitivity,
                )
                from number_compiler.sequences.prime.congruence import (
                    FactoredPrimeAutomaton,
                )

                high = spec.start + 2 * max(0, spec.length - 1)
                automaton = FactoredPrimeAutomaton.build(
                    isqrt(high), word_bits=spec.word_bits
                )
                start_state, start_morphism = automaton.state_from_value(
                    spec.start, radix=2
                )
                first = decision.summary.first
                first_compositions = first_calls = cyclotomic_first_calls = 0
                if first is not None:
                    first_state, jump = automaton.advance(start_state, first)
                    is_prime, first_calls = automaton.classify_state(first_state)
                    if not is_prime:
                        raise AssertionError(
                            "factored automaton disagrees with residual-set quotient"
                        )
                    first_compositions = jump.compositions
                cyclotomic = decision.wheel_cyclotomic
                if cyclotomic is None:
                    raise AssertionError(
                        "diagnostic prime compile omitted cyclotomic wheel"
                    )
                if first is not None:
                    cyclo_prime, cyclotomic_first_calls = cyclotomic.classify_index(
                        first
                    )
                    if not cyclo_prime:
                        raise AssertionError(
                            "cyclotomic wheel disagrees with residual-set quotient"
                        )
                packed_charged_bits = 2 * automaton.wheel.total_group_bits
                cyclotomic_charged_bits = (
                    cyclotomic.state_bits + cyclotomic.descriptor_bits
                )
                selected = (
                    "cyclotomic"
                    if cyclotomic_charged_bits <= packed_charged_bits
                    else "packed"
                )
                automaton_view = PrimeFactoredAutomatonCompilation(
                    group_count=automaton.wheel.group_count,
                    total_group_bits=automaton.wheel.total_group_bits,
                    start_morphism_compositions=start_morphism.compositions,
                    first_index=first,
                    first_jump_compositions=first_compositions,
                    first_gcd_calls=first_calls,
                    cyclotomic_group_count=len(cyclotomic.groups),
                    cyclotomic_state_bits=cyclotomic.state_bits,
                    cyclotomic_descriptor_bits=cyclotomic.descriptor_bits,
                    cyclotomic_prime_candidates=cyclotomic.construction_prime_candidates,
                    cyclotomic_root_trials=cyclotomic.construction_root_trials,
                    cyclotomic_first_calls=cyclotomic_first_calls,
                    selected_random_access=selected,
                )
                translation_sensitivity = prime_translation_sensitivity(2, 8).power(
                    spec.length
                )
            out = PrimeBlockCompilation(
                spec,
                decision,
                automaton_view,
                translation_sensitivity,
                (decision.wheel_cyclotomic if spec.random_access else None),
            )
        elif type(spec) is FermatSequenceSpec:
            out = self._compile_fermat(spec, diagnostics=diagnostics)
        elif isinstance(spec, MersenneSequenceSpec):
            out = self._compile_mersenne(spec, diagnostics=diagnostics)
        else:  # pragma: no cover - closed union guard
            raise TypeError(type(spec))
        self._cache[key] = out
        return out

    @overload
    def compile_diagnostic(
        self, spec: ReverseAddSequenceSpec
    ) -> ReverseAddCompilation: ...

    @overload
    def compile_diagnostic(self, spec: CollatzSequenceSpec) -> CollatzCompilation: ...

    @overload
    def compile_diagnostic(
        self, spec: PrimeBlockSequenceSpec
    ) -> PrimeBlockCompilation: ...

    @overload
    def compile_diagnostic(self, spec: FermatSequenceSpec) -> FermatCompilation: ...

    @overload
    def compile_diagnostic(self, spec: MersenneSequenceSpec) -> MersenneCompilation: ...

    def compile_diagnostic(self, spec: SequenceSpec) -> SequenceCompilation:
        """Compile with all release/accounting views enabled.

        This is intentionally separate from :meth:`compile` so benchmarks and
        release audits cannot accidentally make diagnostic materialization part
        of the production semantic cost model.
        """
        return self.compile(spec, diagnostics=True)

    @property
    def cache_size(self) -> int:
        return len(self._cache)

    @property
    def theorem_cache_size(self) -> int:
        return len(self._theorem_cache)

    @property
    def special_constraint_cache_size(self) -> int:
        return len(self._special_constraint_cache)

    def _special_constraint_state(
        self, family: str, parameter: int
    ) -> SpecialGermConstraintState:
        from number_compiler.sequences.power_numbers.germ import (
            SpecialGermConstraintState,
        )

        if type(family) is not str:
            raise TypeError("special family must be a string")
        parameter = require_integer(parameter, "special parameter", 0)
        out = self._special_constraint_cache.get((family, parameter))
        if out is None:
            return SpecialGermConstraintState.identity()
        if not isinstance(out, SpecialGermConstraintState):
            raise TypeError(type(out))
        return out

    @staticmethod
    def _special_constraint_failure_bit(
        state: SpecialGermConstraintState,
    ) -> bool | None:
        return state.constraint_failure_bit

    def _refine_special_constraint_state(
        self, family: str, parameter: int, constraint: SpecialGermConstraintState
    ) -> SpecialGermConstraintState:
        from number_compiler.sequences.power_numbers.germ import (
            SpecialGermConstraintState,
        )

        if type(constraint) is not SpecialGermConstraintState:
            raise TypeError(type(constraint))
        if type(family) is not str:
            raise TypeError("special family must be a string")
        key = (family, require_integer(parameter, "special parameter", 0))
        refined = self._special_constraint_state(*key).then(constraint)
        self._special_constraint_failure_bit(
            refined
        )  # reject contradictory evidence now
        self._special_constraint_cache[key] = refined
        return refined

    def _refine_special_constraint_mask(
        self, family: str, parameter: int, mask: SpecialBranchMask
    ) -> SpecialBranchMask:
        from number_compiler.projection.output_quotient import SpecialBranchMask
        from number_compiler.sequences.power_numbers.germ import (
            SpecialGermConstraintState,
        )

        if type(mask) is not SpecialBranchMask:
            raise TypeError(type(mask))
        state = self._refine_special_constraint_state(
            family,
            parameter,
            SpecialGermConstraintState.from_mask(mask, method="source-output-mask"),
        )
        return state.mask

    def _special_constraint_mask(
        self, family: str, parameter: int
    ) -> SpecialBranchMask:
        return self._special_constraint_state(family, parameter).mask

    def pullback_special_defect(
        self,
        family: str,
        parameter: int,
        modulus: int,
        defect: int,
        *,
        method: str,
    ) -> SpecialGermConstraintState:
        """Persist a candidate-derived theorem defect without enumerating support slots.

        ``gcd(modulus, defect)`` is accumulated as one support ideal.  Adjacent
        powered blocks may call this repeatedly; composition retains one gcd and
        one two-bit sheet mask regardless of the number of checkpoints.
        """
        from number_compiler.sequences.power_numbers.germ import (
            SpecialGermConstraintState,
        )

        if type(family) is not str or type(method) is not str:
            raise TypeError("special family and defect method must be strings")
        parameter = require_integer(parameter, "special parameter", 0)
        modulus = require_integer(modulus, "defect modulus", 1)
        defect = require_integer(defect, "defect", 0)
        if not special_modulus_matches(family, parameter, modulus):
            raise ValueError(
                "defect modulus does not match the requested special source"
            )
        return self._refine_special_constraint_state(
            family,
            parameter,
            SpecialGermConstraintState.from_defect(
                modulus,
                defect,
                method=method,
                candidate_derived=True,
            ),
        )

    @staticmethod
    def _compile_reverse_add(
        spec: ReverseAddSequenceSpec, *, diagnostics: bool
    ) -> ReverseAddCompilation:
        from number_compiler.api.sequence_terms import formula_term
        from number_compiler.arithmetic.functions.state_reduction import (
            ReverseAddGrowthState,
        )
        from number_compiler.sequences.reverse_add.digits import (
            reverse_add_orbit_formulas,
        )

        arena, digit_roots, pair_roots = reverse_add_orbit_formulas(
            spec.seed, spec.steps, base=spec.base
        )
        dspec = DigitSpec(spec.base)
        terms = tuple(
            formula_term(
                i,
                spec.base,
                root,
                arena=arena,
                digit_spec=dspec,
                diagnostics=diagnostics,
            )
            for i, root in enumerate(digit_roots)
        )
        growths = tuple(
            pair_roots[i + 1].width - pair_roots[i].width for i in range(spec.steps)
        )
        if diagnostics and spec.base >= 3:
            from number_compiler.arithmetic.carry.event_memory import pair_plane_bits

            bits = pair_plane_bits(spec.base)
        else:
            bits = 0
        live_avg: float | None = None
        live_max: int | None = None
        live_ratio: float | None = None
        # Full symmetric pair roots already carry a constant-size BlockSummary.
        # Project its first reset/relationship directly: no growth bit-vector or
        # positional carry scan is retained for the branch decision.
        growth_states = tuple(
            ReverseAddGrowthState.from_summary(
                get_summary(arena, root, RadixSpec(spec.base), required=True),
                base=spec.base,
            )
            for root in pair_roots
        )
        growth_state_classes = len({state.canonical_key for state in growth_states})
        growth_state_max_bits = max(
            (state.description_bits for state in growth_states), default=0
        )
        carry_reset_max_bits = 0
        if tuple(state.growth for state in growth_states[:-1]) != growths:
            raise AssertionError("boundary growth observer disagrees with pair widths")
        # Lossless carry-history diagnostics are an explicit proof operation.
        # Even diagnostic compilation must not silently bootstrap raw H rows.
        cyclotomic: list[tuple[int, int]] = []
        if growths and bits:
            from number_compiler.arithmetic.carry.carry_itinerary import (
                adaptive_negacyclic_memory_horizon,
                adaptive_zplus1_memory_horizon,
            )

            endpoints = range(min(len(growths), 4 * bits), len(growths) + 1)
            if endpoints:
                h1 = [
                    adaptive_zplus1_memory_horizon(growths, e, degree=1, bits=bits)
                    for e in endpoints
                ]
                if all(h is not None for h in h1):
                    cyclotomic.append((1, max(int(h) for h in h1 if h is not None)))
                for classes in (2, 4, 8):
                    hs = [
                        adaptive_negacyclic_memory_horizon(
                            growths, e, classes=classes, bits=bits
                        )
                        for e in endpoints
                    ]
                    if all(h is not None for h in hs):
                        cyclotomic.append(
                            (classes, max(int(h) for h in hs if h is not None))
                        )
        radial_modes: tuple[PowerTwoCyclotomicRadialQuotient, ...] = ()
        symmetry_modes: tuple[ReverseAddSymmetryLinearAction, ...] = ()
        if bits and growths:
            from number_compiler.arithmetic.formula.symmetry_frame import (
                ReverseAddSymmetryLinearAction,
            )
            from number_compiler.arithmetic.polynomials.cyclotomic_transport import (
                power_two_cyclotomic_radial_quotient,
            )

            q = sum(1 - int(g) for g in growths)
            r = sum(map(int, growths))
            radial_modes = tuple(
                power_two_cyclotomic_radial_quotient(m, q, r, bits=bits)
                for m in (1, 2, 4, 8)
            )
            symmetry_modes = tuple(
                ReverseAddSymmetryLinearAction(order, bits, q, r)
                for order in (2, 4, 8, 16)
            )
        return ReverseAddCompilation(
            spec,
            terms,
            live_avg,
            live_max,
            live_ratio,
            tuple(cyclotomic),
            radial_modes,
            growth_state_classes,
            growth_state_max_bits,
            carry_reset_max_bits,
            symmetry_modes,
        )

    def resolve_special_theorem(
        self,
        family: str,
        parameter: int,
        *,
        factor_limit: int = 1000,
        use_factor_projection: bool = False,
        use_terminal_certificate: bool = True,
        allow_classical_ceiling: bool = False,
        collect_etale_factor: bool = False,
        max_factor_products: int = 4096,
        max_candidate_bits: int = 1_000_000,
    ) -> SpecialTheoremResolution:
        """Explicitly demand Fermat/Mersenne theorem classification.

        Compilation never requests primality. Consume existing source constraints
        before new theorem work; classical recurrence completion is forbidden.
        ``collect_etale_factor`` requests a separately charged coefficient-gcd
        witness, which can establish compositeness for an unresolved candidate.
        """
        if type(family) is not str:
            raise TypeError("special family must be a string")
        parameter = require_integer(parameter, "special parameter", 0)
        factor_limit = require_integer(factor_limit, "factor limit", 0)
        max_factor_products = require_integer(max_factor_products, "factor products", 0)
        if (
            type(use_factor_projection) is not bool
            or type(use_terminal_certificate) is not bool
            or type(allow_classical_ceiling) is not bool
            or type(collect_etale_factor) is not bool
        ):
            raise TypeError("special theorem policies must be Booleans")
        if allow_classical_ceiling:
            raise ValueError("classical primality recurrences are not production paths")
        from number_compiler.sequences.power_numbers.admission import (
            require_special_candidate_budget,
        )

        require_special_candidate_budget(family, parameter, max_candidate_bits)
        factor_witness_key = ("etale-factor-witness", family, parameter)
        if collect_etale_factor:
            # Factor output enriches the existing theorem result without replaying it.
            known_witness = self._theorem_cache.get(factor_witness_key)
            if known_witness is not None and known_witness.factor_witness is not None:
                return known_witness
            factor_cache_key = (
                "etale-factor-output",
                max_factor_products,
                family,
                parameter,
                use_factor_projection,
                factor_limit if use_factor_projection else 0,
                use_terminal_certificate,
            )
            cached_factor = self._theorem_cache.get(factor_cache_key)
        state = self._special_constraint_state(family, parameter)
        pulled_bit = self._special_constraint_failure_bit(state)
        if collect_etale_factor and cached_factor is not None:
            support = state.support_gcd
            modulus = state.support_modulus
            if support is None or modulus is None or not 1 < support < modulus:
                return cached_factor
            if cached_factor.factor_witness == support:
                return cached_factor
        if pulled_bit is not None:
            from number_compiler.projection.output_quotient import SpecialSourceGuard
            from number_compiler.sequences.power_numbers.theorem_query import (
                SpecialTheoremResolution,
            )

            support = state.support_gcd
            modulus = state.support_modulus
            proper_support = (
                support
                if support is not None and modulus is not None and 1 < support < modulus
                else None
            )
            method = (
                "pulled-back-support-defect"
                if support is not None
                else "pulled-back-output-constraint"
            )
            guard = SpecialSourceGuard(family, parameter, pulled_bit, method)
            result = SpecialTheoremResolution(
                family,
                parameter,
                guard,
                projection_method=method,
                factor_witness=proper_support,
            )
            if collect_etale_factor:
                from number_compiler.sequences.power_numbers.theorem_query import (
                    with_etale_factor,
                )

                result = with_etale_factor(result, max_products=max_factor_products)
                self._theorem_cache[factor_cache_key] = result
                if result.factor_witness is not None:
                    self._theorem_cache[factor_witness_key] = result
            return result
        # A factor limit is semantically irrelevant when the optional factor
        # projection is disabled.  Normalize it out of theorem-cache identity.
        factor_key = factor_limit if use_factor_projection else 0
        base_key = (
            family,
            parameter,
            factor_key,
            use_factor_projection,
            use_terminal_certificate,
        )
        key = (
            *base_key,
            collect_etale_factor,
            max_factor_products if collect_etale_factor else 0,
        )
        old = self._theorem_cache.get(key)
        if old is not None:
            return old
        from number_compiler.sequences.power_numbers.theorem_query import (
            resolve_special_theorem as resolve_special_theorem_query,
        )
        from number_compiler.sequences.power_numbers.theorem_query import (
            with_etale_factor,
        )

        # Enrich the admitted base result, charging only new witness work.
        base = (
            self._theorem_cache.get((*base_key, False, 0))
            if collect_etale_factor
            else None
        )
        if collect_etale_factor and base is not None:
            out = with_etale_factor(base, max_products=max_factor_products)
        else:
            out = resolve_special_theorem_query(
                family,
                parameter,
                factor_limit=factor_limit,
                use_factor_projection=use_factor_projection,
                use_terminal_certificate=use_terminal_certificate,
                allow_classical_ceiling=allow_classical_ceiling,
                collect_etale_factor=collect_etale_factor,
                max_factor_products=max_factor_products,
                max_candidate_bits=max_candidate_bits,
            )
        if out.source_guard.failure_bit is not None:
            from number_compiler.projection.output_quotient import SpecialBranchMask

            theorem_mask = SpecialBranchMask(
                0b10 if out.source_guard.failure_bit else 0b01
            )
            self._refine_special_constraint_mask(family, parameter, theorem_mask)
        if collect_etale_factor:
            self._theorem_cache[factor_cache_key] = out
            if out.factor_witness is not None:
                self._theorem_cache[factor_witness_key] = out
        self._theorem_cache[key] = out
        return out

    def project_special_branch_values(
        self,
        family: str,
        parameter: int,
        pass_value: int,
        fail_value: int,
        *,
        mask: SpecialBranchMask | None = None,
        require_concrete: bool = False,
    ) -> BinaryOutputCoordinate:
        """Apply cheap branch constraints before optionally asking the theorem.

        ``mask`` is normally produced by :class:`SpecialSourceShape` from known
        source length/digit/oddness/boundary facts.  It is intersected into the
        source's persistent two-bit survivor mask, so a sheet killed by one
        coordinate stays dead for later coordinates.  Only an unresolved
        separating output with ``require_concrete=True`` reaches arithmetic
        theorem work.
        """
        from number_compiler.projection.output_quotient import (
            SpecialBranchMask,
            SpecialSourceGuard,
        )

        if type(family) is not str:
            raise TypeError("special family must be a string")
        parameter = require_integer(parameter, "special parameter", 0)
        pass_value = require_integer(pass_value, "pass value")
        fail_value = require_integer(fail_value, "fail value")
        if type(require_concrete) is not bool:
            raise TypeError("require_concrete must be a Boolean")
        guard = SpecialSourceGuard(family, parameter, None, "lazy-output-frontier")
        coordinate = guard.project_branch_values(pass_value, fail_value)
        if mask is not None:
            if type(mask) is not SpecialBranchMask:
                raise TypeError(type(mask))
            self._refine_special_constraint_mask(family, parameter, mask)
        state = self._special_constraint_state(family, parameter)
        pulled_bit = self._special_constraint_failure_bit(state)
        coordinate = (
            coordinate.resolve(pulled_bit)
            if pulled_bit is not None
            else coordinate.restrict(state.mask)
        )
        if coordinate.mode.value != "Guarded" or not require_concrete:
            return coordinate
        resolution = self.resolve_special_theorem(family, parameter)
        if resolution.source_guard.failure_bit is None:
            return coordinate
        return coordinate.resolve(resolution.source_guard.failure_bit)

    def project_special_digit(
        self,
        family: str,
        parameter: int,
        index: int,
        pass_digit: int,
        fail_digit: int,
    ) -> BinaryOutputCoordinate:
        """Resolve a source digit by its exact sparse support, with zero theorem work."""
        from number_compiler.projection.output_quotient import SpecialSourceShape

        if type(family) is not str:
            raise TypeError("special family must be a string")
        parameter = require_integer(parameter, "special parameter", 0)
        index = require_integer(index, "digit coordinate", 0)
        pass_digit = require_integer(pass_digit, "pass digit")
        fail_digit = require_integer(fail_digit, "fail digit")
        shape = SpecialSourceShape(family, parameter)
        mask = shape.digit_mask(index, pass_digit, fail_digit).require_possible()
        return self.project_special_branch_values(
            family,
            parameter,
            pass_digit,
            fail_digit,
            mask=mask,
        )

    def project_special_parity(
        self,
        family: str,
        parameter: int,
        pass_value: int,
        fail_value: int,
    ) -> BinaryOutputCoordinate:
        """Resolve the forced odd low bit before any theorem work."""
        from number_compiler.projection.output_quotient import SpecialSourceShape

        if type(family) is not str:
            raise TypeError("special family must be a string")
        parameter = require_integer(parameter, "special parameter", 0)
        pass_value = require_integer(pass_value, "pass value")
        fail_value = require_integer(fail_value, "fail value")
        shape = SpecialSourceShape(family, parameter)
        mask = shape.odd_mask(pass_value, fail_value).require_possible()
        return self.project_special_branch_values(
            family,
            parameter,
            pass_value & 1,
            fail_value & 1,
            mask=mask,
        )

    def project_special_length(
        self,
        family: str,
        parameter: int,
        pass_length: int,
        fail_length: int,
    ) -> BinaryOutputCoordinate:
        """Resolve canonical source length before any theorem query."""
        from number_compiler.projection.output_quotient import SpecialSourceShape

        if type(family) is not str:
            raise TypeError("special family must be a string")
        parameter = require_integer(parameter, "special parameter", 0)
        pass_length = require_integer(pass_length, "pass length", 0)
        fail_length = require_integer(fail_length, "fail length", 0)
        shape = SpecialSourceShape(family, parameter)
        mask = shape.length_mask(pass_length, fail_length).require_possible()
        return self.project_special_branch_values(
            family,
            parameter,
            pass_length,
            fail_length,
            mask=mask,
        )

    def project_special_carry(
        self,
        family: str,
        parameter: int,
        expected_carry: int,
        pass_carry: int,
        fail_carry: int,
    ) -> BinaryOutputCoordinate:
        """Resolve a carry checkpoint supplied by an independent powered block."""
        from number_compiler.projection.output_quotient import SpecialSourceShape

        if type(family) is not str:
            raise TypeError("special family must be a string")
        parameter = require_integer(parameter, "special parameter", 0)
        expected_carry = require_integer(expected_carry, "expected carry")
        pass_carry = require_integer(pass_carry, "pass carry")
        fail_carry = require_integer(fail_carry, "fail carry")
        shape = SpecialSourceShape(family, parameter)
        mask = shape.carry_mask(
            expected_carry, pass_carry, fail_carry
        ).require_possible()
        return self.project_special_branch_values(
            family,
            parameter,
            pass_carry,
            fail_carry,
            mask=mask,
        )

    def project_special_boundary_sign(
        self,
        family: str,
        parameter: int,
        pass_sign: int,
        fail_sign: int,
    ) -> BinaryOutputCoordinate:
        """Resolve cyclic/negacyclic boundary geometry before theorem work."""
        from number_compiler.projection.output_quotient import SpecialSourceShape

        if type(family) is not str:
            raise TypeError("special family must be a string")
        parameter = require_integer(parameter, "special parameter", 0)
        pass_sign = require_integer(pass_sign, "pass sign")
        fail_sign = require_integer(fail_sign, "fail sign")
        shape = SpecialSourceShape(family, parameter)
        mask = shape.boundary_mask(pass_sign, fail_sign).require_possible()
        return self.project_special_branch_values(
            family,
            parameter,
            pass_sign,
            fail_sign,
            mask=mask,
        )

    @staticmethod
    def _compile_fermat(
        spec: FermatSequenceSpec, *, diagnostics: bool
    ) -> FermatCompilation:
        from number_compiler.api.sequence_terms import symbolic_sparse_term

        if diagnostics:
            from number_compiler.arithmetic.fields.adic_morphism import (
                fermat_shifted_square_sensitivity,
            )
            from number_compiler.arithmetic.polynomials.primary_jet import (
                primary_jet_from_runs,
            )
        # ``test_through`` is a legacy theorem policy, not source identity.
        # Normalize it away in the cached source compilation.
        source_spec = FermatSequenceSpec(
            spec.indices,
            test_through=0,
            reinterpret_radices=spec.reinterpret_radices,
        )
        terms: list[FermatCompiledTerm] = []
        reinterpret_radices = (
            (2, 3, 5, 6, 10)
            if diagnostics and spec.reinterpret_radices == (2,)
            else spec.reinterpret_radices
        )
        for index in spec.indices:
            number = FermatNumberSpec(index)
            width = number.bit_length_extent
            order = number.cyclotomic_order_extent
            # The semantic source is sparse: 11 for F_0 and 1 0^(2^n-1) 1
            # otherwise.  Do not lower 2^n into a Python integer merely to put
            # that extent into a CanonicalWord run.
            run_count = 1 if index == 0 else 3
            jet = None
            if diagnostics and index <= 4096:
                # Diagnostics are explicitly optional.  Keep legacy primary-jet
                # observability for practical indices while the semantic source
                # itself remains algebraic.
                exponent = number.exponent_extent.materialize(max_power=4096)
                jet_runs = (
                    ((1, 2),) if index == 0 else ((1, 1), (0, exponent - 1), (1, 1))
                )
                jet = primary_jet_from_runs(jet_runs, degree=4, modulus=32)
            radix_word = symbolic_sparse_term(
                index,
                2,
                width,
                runs=run_count,
                extent_parameters=(number.exponent_extent,),
                diagnostics_jet=jet,
            )
            reinterpretations = tuple(
                symbolic_sparse_term(
                    index,
                    radix,
                    width,
                    runs=run_count,
                    extent_parameters=(number.exponent_extent,),
                    diagnostics_jet=jet,
                )
                for radix in reinterpret_radices
                if radix != 2
            )
            for term in reinterpretations:
                rspec = fermat_radix_reinterpretation(index, term.radix)
                if (rspec.cyclotomic_order_extent, rspec.digit_length_extent) != (
                    order,
                    width,
                ):
                    raise AssertionError("Fermat radix reinterpretation mismatch")
            terms.append(
                FermatCompiledTerm(
                    index,
                    width,
                    order,
                    radix_word,
                    None,
                    "deferred",
                    None,
                    reinterpretations,
                    (
                        fermat_shifted_square_sensitivity(16).power(index)
                        if diagnostics
                        else None
                    ),
                    None,
                    None,
                )
            )
        return FermatCompilation(source_spec, tuple(terms))

    @staticmethod
    def _compile_mersenne(
        spec: MersenneSequenceSpec, *, diagnostics: bool
    ) -> MersenneCompilation:
        from number_compiler.api.sequence_terms import symbolic_word_term

        if diagnostics:
            from number_compiler.arithmetic.fields.adic_morphism import (
                mersenne_successor_2adic_sensitivity,
            )
        source_spec = MersenneSequenceSpec(
            spec.exponents,
            test_through=0,
            reinterpret_radices=spec.reinterpret_radices,
        )
        terms: list[MersenneCompiledTerm] = []
        reinterpret_radices = (
            (2, 3, 5, 6, 10)
            if diagnostics and spec.reinterpret_radices == (2,)
            else spec.reinterpret_radices
        )
        for exponent in spec.exponents:
            number = MersenneNumberSpec(exponent)
            word = from_runs(((1, exponent),))
            radix_word = symbolic_word_term(exponent, 2, word, diagnostics=diagnostics)
            reinterpretations = tuple(
                symbolic_word_term(exponent, radix, word, diagnostics=diagnostics)
                for radix in reinterpret_radices
                if radix != 2
            )
            for term in reinterpretations:
                rspec = mersenne_radix_reinterpretation(exponent, term.radix)
                if rspec.digit_length != number.bit_length:
                    raise AssertionError("Mersenne radix reinterpretation mismatch")
            terms.append(
                MersenneCompiledTerm(
                    exponent,
                    number.bit_length,
                    radix_word,
                    None,
                    None,
                    "deferred",
                    None,
                    reinterpretations,
                    (
                        mersenne_successor_2adic_sensitivity(16).power(
                            max(0, exponent - 1)
                        )
                        if diagnostics
                        else None
                    ),
                    None,
                    None,
                )
            )
        return MersenneCompilation(source_spec, tuple(terms))


__all__ = [
    "CanonicalSequenceCompiler",
    "CollatzCompilation",
    "CollatzSequenceSpec",
    "FermatCompilation",
    "FermatSequenceSpec",
    "MersenneCompilation",
    "MersenneSequenceSpec",
    "PrimeBlockCompilation",
    "PrimeBlockSequenceSpec",
    "ReverseAddCompilation",
    "ReverseAddSequenceSpec",
]
