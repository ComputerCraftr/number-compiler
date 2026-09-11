"""Data-only audit records for special successor research.

Separated from the executable probes so the research surface stays below the
repository size cap and no audit record is defined more than once.
"""

from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True, slots=True)
class ImageFiltrationAudit:
    family: str
    parameter: int
    carrier_classes: int
    moore_classes: int
    image_ranks: tuple[int, ...]
    stable_states: int
    finite_depths: int
    moore_equals_image_depth: bool
    source_depth: int
    target_depths: tuple[int, ...]
    prime_case: bool


@dataclass(frozen=True, slots=True)
class ResidueConstraintAudit:
    family: str
    parameter: int
    predicate: str
    target_set: str
    target_size: int
    feature_classes: int
    conflicts: int
    exact_on_domain: bool
    ring_safe_one_way: bool


@dataclass(frozen=True, slots=True)
class StaticInjectionAudit:
    family: str
    parameter: int
    feature_family: str
    source_states: int
    target_classes: int
    selected_features: tuple[str, ...]
    selected_key_classes: int
    target_separating: bool
    noninjective: bool


@dataclass(frozen=True, slots=True)
class StructuredAutomatonAudit:
    family: str
    parameter: int
    raw_states: int
    target_classes: int
    best_base: int
    best_direction: str
    best_nodes: int
    best_max_level_states: int
    node_ratio: float


@dataclass(frozen=True, slots=True)
class BooleanSetAudit:
    family: str
    parameter: int
    image_level: int
    input_bits: int
    set_size: int
    anf_degree: int
    anf_terms: int


@dataclass(frozen=True, slots=True)
class PureTwoGroupAudit:
    family: str
    parameter: int
    group_or_quotient_exponent: int
    predicted_group_states: int
    observed_relevant_states: int
    matches: bool
    interpretation: str


@dataclass(frozen=True, slots=True)
class PrimeGroupDepthAudit:
    family: str
    parameter: int
    active_two_group_exponent: int
    stable_image_states: int
    predicted_quotient_classes: int
    bounded_moore_classes: int
    predicted_target_depth: int
    bounded_target_depth: int
    predicted_image_ranks: tuple[int, ...]
    bounded_image_ranks: tuple[int, ...]
    image_rank_formula_exact: bool
    moore_equals_image_depth: bool
    target_distance_formula_exact: bool
    source_orbit_covers_all_classes: bool
    source_machine_isomorphic: bool
    carrier_states_avoided_by_theorem: int


@dataclass(frozen=True, slots=True)
class LocalTwoPrimaryComponent:
    prime: int
    multiplicity: int
    local_model: str
    discriminant_character: int | None
    ambient_order: int
    ambient_v2: int
    ambient_odd_part: int
    quotient_order: int | None
    quotient_v2: int | None
    quotient_odd_part: int | None
    source_order: int
    source_v2: int
    source_odd_part: int


@dataclass(frozen=True, slots=True)
class CRTPurityAudit:
    family: str
    parameter: int
    modulus: int
    factors: tuple[tuple[int, int], ...]
    components: tuple[LocalTwoPrimaryComponent, ...]
    pure_prime_domain_shape: bool
    obstructions: tuple[str, ...]


@dataclass(frozen=True, slots=True)
class TwoPrimaryPurityProbe:
    family: str
    parameter: int
    outer_signature: tuple[int, ...]
    proper_gcd_witness: int | None
    status: str
    reciprocity_steps: int


@dataclass(frozen=True, slots=True)
class TwoPrimaryResidualShape:
    """Factor-identity-free local shape used only by the research factor-backed differential."""

    local_model: str
    discriminant_character: int | None
    ambient_v2: int
    ambient_has_odd_part: bool
    source_v2: int
    source_has_odd_part: bool


@dataclass(frozen=True, slots=True)
class TwoPrimaryResidualInterfaceAudit:
    family: str
    parameter: int
    raw_components: int
    canonical_shapes: tuple[tuple[TwoPrimaryResidualShape, int], ...]
    retained_description_bits: int
    factor_identities_retained: bool
    classifies_purity_exactly: bool
    purity_status: str


@dataclass(frozen=True, slots=True)
class TwoPrimaryShiftAudit:
    family: str
    parameter: int
    block_size: int
    canonical_shapes: int
    powered_compositions: int
    exact_for_all_components: bool
    retained_description_bits: int


@dataclass(frozen=True, slots=True)
class BehavioralPurityBlockAudit:
    family: str
    parameter: int
    block_size: int
    carrier_states: int
    one_step_classes: int
    sampled_block_classes: int
    exact_block_classes: int
    sampled_compression_is_unsound: bool
    powering_compositions: int
    exact_quotient_description_bits: int


@dataclass(frozen=True, slots=True)
class AlgebraicBlockObserverAudit:
    family: str
    parameter: int
    block_size: int
    source_states: int
    available_features: int
    selected_features: tuple[str, ...]
    selected_classes: int
    closed: bool
    noninjective: bool
    unresolved_counterexamples: int


@dataclass(frozen=True, slots=True)
class CarryTransferAutomatonAudit:
    family: str
    parameter: int
    radix: int
    block_size: int
    carrier_states: int
    reachable_carry_values: int
    action_alphabet: int
    action_word_classes: int
    successor_conflicts: int
    closed: bool
    average_action_bits: float


@dataclass(frozen=True, slots=True)
class CarryCyclotomicTransducerAudit:
    family: str
    parameter: int
    radix: int
    block_size: int
    order: int
    modulus: int
    reachable_carry_values: int
    transducer_alphabet: int
    transducer_word_classes: int
    successor_conflicts: int
    closed: bool
    average_transducer_bits: float


@dataclass(frozen=True, slots=True)
class BoundaryConsumerQuotientAudit:
    """Bounded future-consumer quotient audit for one square recurrence."""

    family: str
    parameter: int
    source_states: int
    distinct_raw_products: int
    exact_output_action_classes: int
    exact_output_action_injective: bool
    carry_action_classes: int
    carry_successor_conflicts: int
    harmonic_order: int
    harmonic_action_classes: int
    harmonic_successor_conflicts: int
    harmonic_noninjective: bool
    scheduler_promotion_safe: bool


@dataclass(frozen=True, slots=True)
class CarryHenselCyclotomicAudit:
    family: str
    parameter: int
    source_channels: str
    available_features: int
    selected_features: tuple[str, ...]
    selected_classes: int
    closed: bool
    noninjective: bool
    unresolved_counterexamples: int


@dataclass(frozen=True, slots=True)
class CarryTemporalAutomatonAudit:
    family: str
    parameter: int
    marker: str
    marker_classes: int
    closure_horizon: int | None
    horizon_classes: int
    moore_classes: int
    prime_target_depth: int | None
    subdepth_closure: bool


@dataclass(frozen=True, slots=True)
class CarryPhaseRefinementAudit:
    """Bounded check that a carry itinerary is only a refinement of depth.

    ``history_refines_depth`` means the complete carry-marker history at the
    first successor-closed horizon determines image depth.  The history can
    still retain irrelevant phase/provenance; ``minimized_history_equals_depth``
    checks that exact Moore minimization deletes precisely that excess.

    Image depth is defined independently by ``unary_image_filtration``.  No
    target carry event is constructed or used here.  This audit is therefore
    only a regression witness for redundant carry/radix phase after the group
    theorem has independently established the semantic depth quotient.
    """

    family: str
    parameter: int
    radix: int
    marker_classes: int
    history_horizon: int
    history_classes: int
    depth_classes: int
    history_refines_depth: bool
    minimized_history_classes: int
    minimized_history_equals_depth: bool
    excess_phase_classes: int
    max_finite_phase_fiber: int
    stable_phase_classes: int
    target_depth: int


@dataclass(frozen=True, slots=True)
class CompositeDepthSemanticsAudit:
    """Composite M11 guard built without carry observers or event timestamps."""

    family: str
    parameter: int
    image_ranks: tuple[int, ...]
    finite_depth_strata: tuple[int, ...]
    stable_image_states: int
    image_depth_classes: int
    moore_classes: int
    moore_equals_image_depth: bool
    target_image_depths: tuple[int, ...]
    output_states: int
    finite_target_hitting_counts: tuple[tuple[int, int], ...]
    never_target_states: int
    source_image_depth: int
    source_target_hitting_time: int | None


@dataclass(frozen=True, slots=True)
class SpecialFactorShortCircuitAudit:
    family: str
    parameter: int
    image_height: int
    candidate_budget: int
    candidates_tested: int
    small_ring_compositions: int
    witness_k: int | None
    witness_factor: int | None
    status: str
    complete_primality_decision: bool
    max_candidate_bits: int
    batched_powered_compositions: int
    product_multiplications: int
    product_depth: int
    product_gcd_calls: int
    candidate_product_bits: int
    batch_witness_matches_serial: bool


@dataclass(frozen=True, slots=True)
class PurityWorkCost:
    big_ring_squarings: int = 0
    big_ring_multiplies: int = 0
    small_ring_powered_compositions: int = 0
    candidate_product_multiplications: int = 0
    candidate_product_bits: int = 0
    gcd_calls: int = 0
    reciprocity_steps: int = 0
    max_extension_degree: int = 1
    uses_factorization: bool = False
    uses_discrete_log: bool = False
    reconstructs_crt: bool = False
    sequential_image_height_work: bool = False


@dataclass(frozen=True, slots=True)
class PurityCandidateAudit:
    family: str
    candidate: str
    prime_parameter: int
    composite_parameter: int
    prime_observation: str
    composite_observation: str
    distinguishes_fixture: bool
    establishes_purity: bool
    available: bool
    cost: PurityWorkCost
    gate_accepted: bool
    rejection_reasons: tuple[str, ...]


@dataclass(frozen=True, slots=True)
class SpecialSuccessorGeneratorMetrics:
    filtrations: tuple[ImageFiltrationAudit, ...]
    residue_constraints: tuple[ResidueConstraintAudit, ...]
    static_injections: tuple[StaticInjectionAudit, ...]
    structured_automata: tuple[StructuredAutomatonAudit, ...]
    boolean_sets: tuple[BooleanSetAudit, ...]
    two_groups: tuple[PureTwoGroupAudit, ...]
    prime_group_depths: tuple[PrimeGroupDepthAudit, ...]
    crt_purity: tuple[CRTPurityAudit, ...]
    cheap_purity_probes: tuple[TwoPrimaryPurityProbe, ...]
    purity_candidates: tuple[PurityCandidateAudit, ...]
    residual_interfaces: tuple[TwoPrimaryResidualInterfaceAudit, ...]
    shift_blocks: tuple[TwoPrimaryShiftAudit, ...]
    behavioral_blocks: tuple[BehavioralPurityBlockAudit, ...]
    algebraic_block_observers: tuple[AlgebraicBlockObserverAudit, ...]
    carry_transfer_automata: tuple[CarryTransferAutomatonAudit, ...]
    carry_cyclotomic_transducers: tuple[CarryCyclotomicTransducerAudit, ...]
    carry_hensel_cyclotomic: tuple[CarryHenselCyclotomicAudit, ...]
    carry_temporal_automata: tuple[CarryTemporalAutomatonAudit, ...]
    carry_phase_refinements: tuple[CarryPhaseRefinementAudit, ...]
    composite_depth_semantics: CompositeDepthSemanticsAudit
    factor_short_circuits: tuple[SpecialFactorShortCircuitAudit, ...]
