theory Power_Clock_Jumps
  imports Main
begin

text \<open>Concrete temporal clocks for the two power-number recurrences.
The statements are ring identities, hence apply inside any separately
constructed modular quotient ring.  They do not construct a finite carry/germ
quotient and do not assert that the full digit-field consumer is temporally
closed.\<close>

definition square_step :: "'a::monoid_mult \<Rightarrow> 'a" where
  "square_step value = value * value"

definition dyadic_clock :: "nat \<Rightarrow> 'a::monoid_mult \<Rightarrow> 'a" where
  "dyadic_clock depth value = value ^ (2 ^ depth)"

lemma square_step_power:
  "square_step value = value ^ 2"
  by (simp add: square_step_def power2_eq_square)

theorem dyadic_clock_doubles:
  "dyadic_clock (Suc depth) value = square_step (dyadic_clock depth value)"
proof -
  have exponent: "(2::nat) ^ Suc depth = ((2::nat) ^ depth) * 2"
    by (simp add: mult.commute)
  show ?thesis
    by (simp only: dyadic_clock_def square_step_power exponent power_mult)
qed

theorem dyadic_clock_skip_ahead:
  "dyadic_clock (first + second) value =
    dyadic_clock second (dyadic_clock first value)"
  by (simp add: dyadic_clock_def power_mult power_add)

theorem square_iteration_is_dyadic_clock:
  "(square_step ^^ depth) value = dyadic_clock depth value"
proof (induction depth)
  case 0
  then show ?case by (simp add: dyadic_clock_def)
next
  case (Suc depth)
  then show ?case
    by (simp add: funpow_Suc_right dyadic_clock_doubles)
qed

theorem square_iteration_skip_ahead:
  "(square_step ^^ (first + second)) value =
    (square_step ^^ second) ((square_step ^^ first) value)"
  by (simp add: square_iteration_is_dyadic_clock dyadic_clock_skip_ahead)

section \<open>Fermat square deck\<close>

lemma square_step_deck [simp]:
  "square_step (- value :: 'a::ring_1) = square_step value"
  by (simp add: square_step_def)

theorem fermat_deck_dies_after_one_square:
  "(square_step ^^ Suc depth) (- value :: 'a::ring_1) =
    (square_step ^^ Suc depth) value"
  by (simp only: funpow_Suc_right comp_apply square_step_deck)

corollary fermat_pulled_terminal_observer_is_deck_invariant:
  "((square_step ^^ Suc depth) (- value :: 'a::ring_1) = -1) =
    ((square_step ^^ Suc depth) value = -1)"
proof -
  have deck:
      "(square_step ^^ Suc depth) (- value) =
        (square_step ^^ Suc depth) value"
    by (rule fermat_deck_dies_after_one_square)
  show ?thesis
    by (simp only: deck)
qed

lemma fermat_current_terminal_observer_splits_deck:
  "(-1::int) = -1 \<and> (1::int) \<noteq> -1"
  by simp

section \<open>Lucas trace of a norm-one doubling clock\<close>

definition lucas_trace_step :: "'a::ring_1 \<Rightarrow> 'a" where
  "lucas_trace_step trace = trace * trace - 2"

definition norm_one_pair :: "'a::monoid_mult \<Rightarrow> 'a \<Rightarrow> bool" where
  "norm_one_pair forward backward \<longleftrightarrow> forward * backward = 1"

definition trace_readout :: "'a::plus \<Rightarrow> 'a \<Rightarrow> 'a" where
  "trace_readout forward backward = forward + backward"

lemma norm_one_pair_square:
  fixes forward backward :: "'a::comm_monoid_mult"
  assumes "norm_one_pair forward backward"
  shows "norm_one_pair (square_step forward) (square_step backward)"
  using assms
  by (simp add: norm_one_pair_def square_step_def mult_ac)

lemma norm_one_trace_square:
  fixes forward backward :: "'a::comm_ring_1"
  assumes "norm_one_pair forward backward"
  shows "lucas_trace_step (trace_readout forward backward) =
    trace_readout (square_step forward) (square_step backward)"
proof -
  have product: "forward * backward = 1"
    using assms by (simp only: norm_one_pair_def)
  have reverse_product: "backward * forward = 1"
    using product by (simp add: mult.commute)
  show ?thesis
    unfolding lucas_trace_step_def trace_readout_def square_step_def
    using product reverse_product
    by (simp add: algebra_simps)
qed

lemma dyadic_clock_norm_one:
  fixes forward backward :: "'a::comm_ring_1"
  assumes "norm_one_pair forward backward"
  shows "norm_one_pair (dyadic_clock depth forward)
    (dyadic_clock depth backward)"
  using assms
proof (induction depth)
  case 0
  then show ?case by (simp add: dyadic_clock_def)
next
  case (Suc depth)
  then show ?case
    using norm_one_pair_square dyadic_clock_doubles by metis
qed

theorem lucas_trace_iteration_is_clock_readout:
  fixes forward backward :: "'a::comm_ring_1"
  assumes "norm_one_pair forward backward"
  shows "(lucas_trace_step ^^ depth) (trace_readout forward backward) =
    trace_readout (dyadic_clock depth forward)
      (dyadic_clock depth backward)"
  using assms
proof (induction depth arbitrary: forward backward)
  case 0
  then show ?case by (simp add: dyadic_clock_def)
next
  case (Suc depth)
  have clock_norm:
      "norm_one_pair (dyadic_clock depth forward)
        (dyadic_clock depth backward)"
    using Suc.prems by (rule dyadic_clock_norm_one)
  have next_step:
      "lucas_trace_step
          (trace_readout (dyadic_clock depth forward)
            (dyadic_clock depth backward)) =
        trace_readout (square_step (dyadic_clock depth forward))
          (square_step (dyadic_clock depth backward))"
    using clock_norm by (rule norm_one_trace_square)
  show ?case
    using Suc.IH[OF Suc.prems] next_step
    by (simp only: funpow.simps(2) comp_apply dyadic_clock_doubles)
qed

theorem lucas_trace_skip_ahead:
  fixes forward backward :: "'a::comm_ring_1"
  assumes "norm_one_pair forward backward"
  shows "(lucas_trace_step ^^ (first + second))
      (trace_readout forward backward) =
    trace_readout (dyadic_clock second (dyadic_clock first forward))
      (dyadic_clock second (dyadic_clock first backward))"
  using assms
  by (simp add: lucas_trace_iteration_is_clock_readout dyadic_clock_skip_ahead)

section \<open>Known-order clock reduction\<close>

lemma power_reduce_at_known_period:
  fixes element :: "'a::monoid_mult"
  assumes positive: "period > 0"
      and period_identity: "element ^ period = 1"
  shows "element ^ exponent = element ^ (exponent mod period)"
proof -
  have split:
      "exponent = period * (exponent div period) + exponent mod period"
    using div_mult_mod_eq[of exponent period]
    by (simp add: mult.commute)
  have "element ^ exponent =
      element ^ (period * (exponent div period) + exponent mod period)"
    using split by simp
  also have "... = (element ^ period) ^ (exponent div period) *
      element ^ (exponent mod period)"
    by (simp only: power_add power_mult)
  finally show ?thesis
    by (simp add: period_identity)
qed

theorem dyadic_clock_known_order_reduce:
  fixes element :: "'a::monoid_mult"
  assumes "period > 0" "element ^ period = 1"
  shows "dyadic_clock depth element = element ^ ((2 ^ depth) mod period)"
  unfolding dyadic_clock_def
  by (rule power_reduce_at_known_period[OF assms])

theorem norm_one_clock_readout_known_order_reduce:
  fixes forward backward :: "'a::comm_ring_1"
  assumes positive: "period > 0"
      and forward_order: "forward ^ period = 1"
      and backward_order: "backward ^ period = 1"
  shows "trace_readout (dyadic_clock depth forward)
      (dyadic_clock depth backward) =
    trace_readout (forward ^ ((2 ^ depth) mod period))
      (backward ^ ((2 ^ depth) mod period))"
  by (simp add: dyadic_clock_known_order_reduce[OF positive forward_order]
      dyadic_clock_known_order_reduce[OF positive backward_order])

section \<open>Normalized two-primary phase occurrence\<close>

lemma two_primary_phase_rebase:
  "(2::nat) ^ depth * odd_phase * 2 ^ steps =
    2 ^ (depth + steps) * odd_phase"
  by (simp add: power_add ac_simps)

lemma two_primary_odd_phase_truncation:
  assumes "live_depth \<le> width"
  shows "(2 ^ live_depth * odd_phase) mod (2::nat) ^ width =
    2 ^ live_depth * (odd_phase mod 2 ^ (width - live_depth))"
proof -
  have split: "width = live_depth + (width - live_depth)"
    using assms by simp
  have exponent:
      "(2::nat) ^ width = 2 ^ (live_depth + (width - live_depth))"
    using split by (rule arg_cong)
  have modulus:
      "(2::nat) ^ width = 2 ^ live_depth * 2 ^ (width - live_depth)"
    using exponent by (simp only: power_add)
  have "2 ^ live_depth * (odd_phase mod 2 ^ (width - live_depth)) =
      (2 ^ live_depth * odd_phase) mod
        (2 ^ live_depth * 2 ^ (width - live_depth))"
    by (rule mult_mod_right)
  then show ?thesis
    by (simp only: modulus)
qed

theorem two_primary_jump_truncates_dead_phase:
  assumes "depth + steps \<le> width"
  shows "((2::nat) ^ depth * odd_phase * 2 ^ steps) mod 2 ^ width =
    2 ^ (depth + steps) *
      (odd_phase mod 2 ^ (width - (depth + steps)))"
  by (simp only: two_primary_phase_rebase
      two_primary_odd_phase_truncation[OF assms])

theorem two_primary_jump_annihilates_phase:
  assumes "width \<le> depth + steps"
  shows "((2::nat) ^ depth * odd_phase * 2 ^ steps) mod 2 ^ width = 0"
proof -
  have split: "depth + steps = width + (depth + steps - width)"
    using assms by simp
  have exponent:
      "(2::nat) ^ (depth + steps) =
        2 ^ (width + (depth + steps - width))"
    using split by (rule arg_cong)
  have powered:
      "(2::nat) ^ (depth + steps) =
        2 ^ width * 2 ^ (depth + steps - width)"
    using exponent by (simp only: power_add)
  show ?thesis
    by (simp only: two_primary_phase_rebase powered)
      simp
qed

section \<open>Minimum local depth as a derived survival view\<close>

definition depth_remaining :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "depth_remaining minimum level =
    (if level \<le> minimum then minimum + 1 - level else 0)"

definition depth_survives :: "nat \<Rightarrow> bool" where
  "depth_survives remaining \<longleftrightarrow> remaining > 0"

definition depth_tangent :: "nat \<Rightarrow> int" where
  "depth_tangent remaining =
    int (remaining - 1) - int remaining"

definition depth_curvature :: "nat \<Rightarrow> int" where
  "depth_curvature remaining =
    depth_tangent (remaining - 1) - depth_tangent remaining"

definition depth_readout_delta :: "nat \<Rightarrow> int" where
  "depth_readout_delta remaining =
    (if depth_survives (remaining - 1) then 1 else 0) -
    (if depth_survives remaining then 1 else 0)"

definition depth_readout_curvature :: "nat \<Rightarrow> int" where
  "depth_readout_curvature remaining =
    depth_readout_delta (remaining - 1) - depth_readout_delta remaining"

definition raw_depth_remaining :: "nat \<Rightarrow> nat \<Rightarrow> int" where
  "raw_depth_remaining minimum level = int minimum + 1 - int level"

lemma depth_remaining_exact:
  assumes "level \<le> minimum"
  shows "depth_remaining minimum level = minimum + 1 - level"
  using assms by (simp add: depth_remaining_def)

lemma depth_remaining_dead_iff:
  "depth_remaining minimum level = 0 \<longleftrightarrow> minimum < level"
  by (auto simp: depth_remaining_def)

lemma depth_remaining_successor:
  "depth_remaining minimum (Suc level) =
    depth_remaining minimum level - 1"
  by (auto simp: depth_remaining_def)

lemma depth_remaining_dead_sink:
  assumes "minimum < level"
  shows "depth_remaining minimum (level + extra) = 0"
  using assms by (simp add: depth_remaining_def)

lemma depth_survives_is_remaining:
  "depth_survives (depth_remaining minimum level) \<longleftrightarrow>
    level \<le> minimum"
  by (auto simp: depth_survives_def depth_remaining_def)

lemma depth_tangent_closed_form:
  "depth_tangent remaining = (if remaining = 0 then 0 else -1)"
  by (cases remaining) (simp_all add: depth_tangent_def)

lemma depth_curvature_closed_form:
  "depth_curvature remaining = (if remaining = 1 then 1 else 0)"
proof (cases remaining)
  case 0
  then show ?thesis by (simp add: depth_curvature_def depth_tangent_closed_form)
next
  case (Suc natural)
  then show ?thesis
    by (cases natural) (simp_all add: depth_curvature_def depth_tangent_closed_form)
qed

lemma depth_readout_delta_closed_form:
  "depth_readout_delta remaining = (if remaining = 1 then -1 else 0)"
  by (cases remaining; simp add: depth_readout_delta_def depth_survives_def)

lemma depth_readout_curvature_closed_form:
  "depth_readout_curvature remaining =
    (if remaining = 1 then 1 else if remaining = 2 then -1 else 0)"
proof (cases remaining)
  case 0
  then show ?thesis
    by (simp add: depth_readout_curvature_def depth_readout_delta_closed_form)
next
  case (Suc natural)
  then show ?thesis
    by (cases natural; simp add: depth_readout_curvature_def
      depth_readout_delta_closed_form)
qed

lemma raw_depth_remaining_delta:
  "raw_depth_remaining minimum (Suc level) - raw_depth_remaining minimum level = -1"
  by (simp add: raw_depth_remaining_def)

lemma raw_depth_remaining_second_delta:
  "(raw_depth_remaining minimum (level + 2) -
      raw_depth_remaining minimum (level + 1)) -
    (raw_depth_remaining minimum (level + 1) -
      raw_depth_remaining minimum level) = 0"
  by (simp add: raw_depth_remaining_def)

lemma depth_views_are_derived:
  assumes "first = second"
  shows "(depth_survives first, depth_readout_delta first,
      depth_readout_curvature first) =
    (depth_survives second, depth_readout_delta second,
      depth_readout_curvature second)"
  using assms by simp

theorem local_minimum_owns_survival:
  fixes depths :: "nat list"
  assumes "depths \<noteq> []"
  shows "level \<le> Min (set depths) \<longleftrightarrow>
    (\<forall>s\<in>set depths. level \<le> s)"
  using assms by simp

lemma local_minimum_is_noninjective:
  "([1,1]::nat list) \<noteq> [6,1] \<and>
    Min (set ([1,1]::nat list)) = Min (set [6,1])"
  by simp

theorem remaining_depth_direct_jump:
  "((\<lambda>r::nat. r-1) ^^ steps) remaining = remaining - steps"
  by (induction steps) (simp_all add: diff_diff_add)

text \<open>The survival output is the threshold predicate level <= minimum.
Its first difference is -1 at remaining=1, and its second difference has the
two boundary values +1 at remaining=1 and -1 at remaining=2.  These readout
differences are distinct from differentiating the clipped remaining coordinate.
The current point target is the negative readout delta at remaining=1, and coincides
with a Fermat -1 or Lucas trace-zero observation only after the corresponding
clock alignment theorem.  Neither observation discovers the local minimum.\<close>

text \<open>The clock exponent and trace recurrence may therefore skip by an
arbitrary duration algebraically.  Evaluating or quotienting a newly demanded
carry, fold, Hensel lift, or full harmonic germ remains a separate obligation.\<close>

ML \<open>
  val checked = @{thms dyadic_clock_doubles dyadic_clock_skip_ahead
    square_iteration_is_dyadic_clock square_iteration_skip_ahead
    fermat_deck_dies_after_one_square
    fermat_pulled_terminal_observer_is_deck_invariant
    fermat_current_terminal_observer_splits_deck norm_one_pair_square
    norm_one_trace_square dyadic_clock_norm_one
    lucas_trace_iteration_is_clock_readout lucas_trace_skip_ahead
    power_reduce_at_known_period dyadic_clock_known_order_reduce
    norm_one_clock_readout_known_order_reduce two_primary_phase_rebase
    two_primary_odd_phase_truncation two_primary_jump_truncates_dead_phase
    two_primary_jump_annihilates_phase depth_remaining_exact
    depth_remaining_dead_iff depth_remaining_successor
    depth_remaining_dead_sink depth_survives_is_remaining
    depth_tangent_closed_form depth_curvature_closed_form
    depth_readout_delta_closed_form depth_readout_curvature_closed_form
    raw_depth_remaining_delta raw_depth_remaining_second_delta
    depth_views_are_derived local_minimum_owns_survival
    local_minimum_is_noninjective remaining_depth_direct_jump};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Power clock jump proof depends on an oracle";
\<close>

end
