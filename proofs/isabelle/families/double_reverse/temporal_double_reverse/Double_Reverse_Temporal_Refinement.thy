theory Double_Reverse_Temporal_Refinement
  imports Shared_Carry_Dynamics.Temporal_Moment_Algebra
    Shared_Carry_Dynamics.Temporal_Decimal_Carry_Monoid
begin

text \<open>The border phase, source-aligned endpoint moments, and decimal
threshold carry laws are separated here.  A repeated phase action is not by
itself a powered sequence occurrence: applying an action still requires the
exact source/target root seam.  This theory therefore proves the finite
controller and endpoint algebra, not the HashLife cone worklist or a general
source-independent affine intercept.\<close>

definition double_reverse_phase_after :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "double_reverse_phase_after steps phase = (phase + 2*steps) mod 4"

definition double_reverse_left_birth :: "nat \<Rightarrow> nat" where
  "double_reverse_left_birth phase =
    (if phase mod 4 = 2 \<or> phase mod 4 = 3 then 1 else 0)"

definition double_reverse_right_birth :: "nat \<Rightarrow> nat" where
  "double_reverse_right_birth phase =
    (if phase mod 4 = 0 \<or> phase mod 4 = 3 then 1 else 0)"

lemma double_reverse_phase_after_one_mod:
  "double_reverse_phase_after 1 (phase mod 4) =
    double_reverse_phase_after 1 phase"
proof -
  have phase_add:
    "(phase mod 4 + 2) mod 4 = (phase + 2) mod 4"
    by (rule mod_add_left_eq)
  show ?thesis
    unfolding double_reverse_phase_after_def
    using phase_add by simp
qed

lemma double_reverse_left_birth_mod:
  "double_reverse_left_birth (phase mod 4) =
    double_reverse_left_birth phase"
  by (simp add: double_reverse_left_birth_def)

lemma double_reverse_right_birth_mod:
  "double_reverse_right_birth (phase mod 4) =
    double_reverse_right_birth phase"
  by (simp add: double_reverse_right_birth_def)

definition double_reverse_growth_then :: "nat \<times> nat \<Rightarrow> nat \<times> nat
    \<Rightarrow> nat \<times> nat" where
  "double_reverse_growth_then first second =
    (fst first + fst second, snd first + snd second)"

fun double_reverse_growth_trace :: "nat \<Rightarrow> nat \<Rightarrow> nat \<times> nat" where
  "double_reverse_growth_trace 0 phase = (0,0)"
| "double_reverse_growth_trace (Suc steps) phase =
    double_reverse_growth_then
      (double_reverse_left_birth phase, double_reverse_right_birth phase)
      (double_reverse_growth_trace steps
        (double_reverse_phase_after 1 phase))"

lemma double_reverse_growth_trace_phase_mod:
  "double_reverse_growth_trace steps (phase mod 4) =
    double_reverse_growth_trace steps phase"
proof (induction steps arbitrary: phase)
  case 0
  then show ?case by simp
next
  case (Suc steps)
  have phase_step:
    "double_reverse_phase_after 1 (phase mod 4) =
      double_reverse_phase_after 1 phase"
    by (rule double_reverse_phase_after_one_mod)
  show ?case
    using Suc.IH[of "double_reverse_phase_after 1 phase"] phase_step
    by (simp add: double_reverse_growth_then_def
        double_reverse_left_birth_mod double_reverse_right_birth_mod)
qed

lemma double_reverse_phase_add:
  "double_reverse_phase_after (first+second) phase =
    double_reverse_phase_after second
      (double_reverse_phase_after first phase)"
  unfolding double_reverse_phase_after_def
  by presburger

lemma double_reverse_phase_after_suc:
  "double_reverse_phase_after first
      (double_reverse_phase_after 1 phase) =
    double_reverse_phase_after (Suc first) phase"
  using double_reverse_phase_add[of 1 first phase]
  by simp

lemma double_reverse_growth_trace_add:
  "double_reverse_growth_trace (first+second) phase =
    double_reverse_growth_then
      (double_reverse_growth_trace first phase)
      (double_reverse_growth_trace second
        (double_reverse_phase_after first phase))"
proof (induction first arbitrary: phase)
  case 0
  have phase_zero:
    "double_reverse_phase_after 0 phase = phase mod 4"
    by (simp add: double_reverse_phase_after_def)
  show ?case
    using phase_zero
    by (simp add: double_reverse_growth_then_def
      double_reverse_growth_trace_phase_mod)
next
  case (Suc first)
  have ih: "double_reverse_growth_trace (first + second)
      (double_reverse_phase_after 1 phase) =
      double_reverse_growth_then
        (double_reverse_growth_trace first
          (double_reverse_phase_after 1 phase))
        (double_reverse_growth_trace second
          (double_reverse_phase_after first
            (double_reverse_phase_after 1 phase)))"
    by (rule Suc.IH)
  have phase_comp:
    "double_reverse_phase_after first
        (double_reverse_phase_after 1 phase) =
      double_reverse_phase_after (Suc first) phase"
    by (rule double_reverse_phase_after_suc)
  let ?birth = "(double_reverse_left_birth phase,
      double_reverse_right_birth phase)"
  have first_expansion:
    "double_reverse_growth_trace (Suc first) phase =
      double_reverse_growth_then ?birth
        (double_reverse_growth_trace first
          (double_reverse_phase_after 1 phase))"
    by simp
  have chain:
    "double_reverse_growth_trace (Suc first + second) phase =
      double_reverse_growth_then ?birth
        (double_reverse_growth_trace (first + second)
          (double_reverse_phase_after 1 phase))"
    by simp
  also have "... = double_reverse_growth_then ?birth
      (double_reverse_growth_then
        (double_reverse_growth_trace first
          (double_reverse_phase_after 1 phase))
        (double_reverse_growth_trace second
          (double_reverse_phase_after first
            (double_reverse_phase_after 1 phase))))"
    by (simp only: ih)
  also have "... = double_reverse_growth_then ?birth
      (double_reverse_growth_then
        (double_reverse_growth_trace first
          (double_reverse_phase_after 1 phase))
        (double_reverse_growth_trace second
          (double_reverse_phase_after (Suc first) phase)))"
    by (simp only: phase_comp)
  also have "... = double_reverse_growth_then
      (double_reverse_growth_then ?birth
        (double_reverse_growth_trace first
          (double_reverse_phase_after 1 phase)))
      (double_reverse_growth_trace second
        (double_reverse_phase_after (Suc first) phase))"
    by (simp add: double_reverse_growth_then_def add.assoc)
  also have "... = double_reverse_growth_then
      (double_reverse_growth_trace (Suc first) phase)
      (double_reverse_growth_trace second
        (double_reverse_phase_after (Suc first) phase))"
    by (simp only: first_expansion)
  finally show ?case .
qed

lemma double_reverse_growth_trace_two:
  assumes phase: "phase < 4"
  shows "double_reverse_growth_trace 2 phase = (1,1)"
proof -
  have phase_cases: "phase=0 \<or> phase=1 \<or> phase=2 \<or> phase=3"
    using phase by presburger
  have zero: "double_reverse_growth_trace 2 0 = (1,1)"
    unfolding numeral_2_eq_2
    by (simp add: double_reverse_phase_after_def
        double_reverse_left_birth_def double_reverse_right_birth_def
        double_reverse_growth_then_def)
  have one: "double_reverse_growth_trace 2 1 = (1,1)"
    unfolding numeral_2_eq_2
    by (simp add: double_reverse_phase_after_def
        double_reverse_left_birth_def double_reverse_right_birth_def
        double_reverse_growth_then_def)
  have two: "double_reverse_growth_trace 2 2 = (1,1)"
    unfolding numeral_2_eq_2
    by (simp add: double_reverse_phase_after_def
        double_reverse_left_birth_def double_reverse_right_birth_def
        double_reverse_growth_then_def)
  have three: "double_reverse_growth_trace 2 3 = (1,1)"
    unfolding numeral_2_eq_2
    by (simp add: double_reverse_phase_after_def
        double_reverse_left_birth_def double_reverse_right_birth_def
        double_reverse_growth_then_def)
  show ?thesis using phase_cases zero one two three by auto
qed

theorem double_reverse_growth_trace_even:
  assumes phase: "phase < 4"
  shows "double_reverse_growth_trace (2*returns) phase = (returns,returns)"
  using phase
proof (induction returns)
  case 0
  then show ?case by simp
next
  case (Suc returns)
  have phase_return:
    "double_reverse_phase_after (2*returns) phase = phase"
    using Suc.prems
    unfolding double_reverse_phase_after_def
    by presburger
  have two: "double_reverse_growth_trace 2 phase = (1,1)"
    by (rule double_reverse_growth_trace_two[OF Suc.prems])
  have ih: "double_reverse_growth_trace (2*returns) phase =
      (returns,returns)"
    by (rule Suc.IH[OF Suc.prems])
  have span: "2 * Suc returns = 2*returns + 2" by simp
  have trace_sum:
    "double_reverse_growth_trace (2*returns + 2) phase =
      double_reverse_growth_then
        (double_reverse_growth_trace (2*returns) phase)
        (double_reverse_growth_trace 2
          (double_reverse_phase_after (2*returns) phase))"
    by (rule double_reverse_growth_trace_add)
  have shifted_two:
    "double_reverse_growth_trace 2
      (double_reverse_phase_after (2*returns) phase) = (1,1)"
    using phase_return two by simp
  have start:
    "double_reverse_growth_trace (2 * Suc returns) phase =
      double_reverse_growth_trace (2*returns + 2) phase"
    using span by simp
  also have "... = double_reverse_growth_then
      (double_reverse_growth_trace (2*returns) phase)
      (double_reverse_growth_trace 2
        (double_reverse_phase_after (2*returns) phase))"
    by (rule trace_sum)
  also have "... = double_reverse_growth_then (returns,returns) (1,1)"
    by (simp only: ih shifted_two)
  finally show ?case
    by (simp add: double_reverse_growth_then_def)
qed

text \<open>For the physical rule (X_{i+1}=2R_i), the last reversed value
must be retained separately from the sum of increments.  The interval
descriptor records both quantities and composes only adjacent occurrences.\<close>

definition double_reverse_interval_moments ::
    "(nat \<Rightarrow> int) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
      last_increment_moments" where
  "double_reverse_interval_moments reverse_at start duration =
    (let first = reverse_at start;
         last = (if duration = 0 then first
           else reverse_at (start+duration-1));
         final = reverse_at (start+duration)
     in \<lparr>lim_span = duration, lim_sum = final-first,
          lim_shortened = (if duration = 0 then 0 else last-first)\<rparr>)"

theorem double_reverse_interval_moments_source_aligned:
  assumes second_nonempty: "0 < second"
  shows "double_reverse_interval_moments reverse_at start (first+second) =
    last_increment_moments_then
      (double_reverse_interval_moments reverse_at start first)
      (double_reverse_interval_moments reverse_at (start+first) second)"
  using second_nonempty
  by (cases first)
    (simp_all add: double_reverse_interval_moments_def
      last_increment_moments_then_def Let_def algebra_simps)

theorem double_reverse_endpoint_matrix_refines_source:
  assumes duration: "0 < lim_span action"
    and source_relation:
      "term_at (start + lim_span action) =
        2 * reverse_at (start + lim_span action - 1)"
    and action_exact:
      "action = double_reverse_interval_moments reverse_at start
        (lim_span action)"
  shows "last_increment_moments_apply action
      (term_at start, reverse_at start) =
    (term_at (start + lim_span action),
      reverse_at (start + lim_span action))"
proof -
  have h:
    "lim_shortened action =
      reverse_at (start + lim_span action - 1) - reverse_at start"
  proof -
    have projected:
      "lim_shortened action = lim_shortened
        (double_reverse_interval_moments reverse_at start (lim_span action))"
      using action_exact by (rule arg_cong)
    show ?thesis
      using projected duration
      by (subst projected; simp add: double_reverse_interval_moments_def Let_def)
  qed
  have u:
    "lim_sum action =
      reverse_at (start + lim_span action) - reverse_at start"
  proof -
    have projected:
      "lim_sum action = lim_sum
        (double_reverse_interval_moments reverse_at start (lim_span action))"
      using action_exact by (rule arg_cong)
    show ?thesis
      using projected
      by (subst projected; simp add: double_reverse_interval_moments_def Let_def)
  qed
  show ?thesis
    using h u source_relation
    by (simp add: last_increment_moments_apply_def algebra_simps)
qed

text \<open>The local T-squared digit transfer is stated with its four-port
guard as a function.  Its producer refinement remains a separate obligation;
the phase-growth theorem above does not establish that an arbitrary endpoint
root was generated by this local digit rule.\<close>

definition double_reverse_t2_digit :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "double_reverse_t2_digit left center right =
    (4*center + 2*(if 5 \<le> left then 1 else 0) +
      (if (2*right + (if 5 \<le> center then 1 else 0)) mod 10 \<ge> 5
       then 1 else 0)) mod 10"

definition threshold5_digit :: "nat \<Rightarrow> nat" where
  "threshold5_digit digit = (if 5 \<le> digit then 1 else 0)"

definition double_reverse_first_pass_cell ::
    "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "double_reverse_first_pass_cell left center =
    (2*center + threshold5_digit left) mod 10"

definition double_reverse_two_pass_cell ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "double_reverse_two_pass_cell left center right =
    (2*double_reverse_first_pass_cell left center +
      (if (2*right + threshold5_digit center) mod 10 \<ge> 5
       then 1 else 0)) mod 10"

lemma double_reverse_two_pass_cell_refines_kernel:
  assumes digits: "left < 10" "center < 10" "right < 10"
  shows "double_reverse_two_pass_cell left center right =
    double_reverse_t2_digit left center right"
proof -
  let ?left = "threshold5_digit left"
  let ?right = "(if (2*right + threshold5_digit center) mod 10 \<ge> 5
    then 1 else 0)"
  have product:
    "(2 * ((2*center + ?left) mod 10)) mod 10 =
      (2 * (2*center + ?left)) mod 10"
    by (rule mod_mult_right_eq)
  have carry_output:
    "(2 * ((2*center + ?left) mod 10) + ?right) mod 10 =
      (2 * (2*center + ?left) + ?right) mod 10"
    by (rule mod_add_cong[OF product refl])
  show ?thesis
    using carry_output
    unfolding double_reverse_two_pass_cell_def
      double_reverse_first_pass_cell_def double_reverse_t2_digit_def
      threshold5_digit_def
    by (simp add: algebra_simps)
qed

text \<open>The carry reset law is the invariant that permits this local kernel
composition: each nonempty emitted digit selects its outgoing threshold
carry without consulting a stale incoming port.  This theorem is local to
the cell expression and says nothing about a scheduler's published roots.\<close>

definition double_reverse_two_digit_action :: "nat \<Rightarrow> nat" where
  "double_reverse_two_digit_action value =
    2*(10*(value mod 10) + value div 10)"

lemma double_reverse_ordered_pair_regression:
  "(19::nat) div 10 + 19 mod 10 = 28 div 10 + 28 mod 10 \<and>
    double_reverse_two_digit_action 19 = 182 \<and>
    double_reverse_two_digit_action 28 = 164 \<and>
    double_reverse_two_digit_action 19 \<noteq>
      double_reverse_two_digit_action 28"
  by (simp add: double_reverse_two_digit_action_def)

ML \<open>
  val checked = @{thms double_reverse_phase_add double_reverse_growth_trace_add
    double_reverse_growth_trace_two double_reverse_growth_trace_even
    double_reverse_interval_moments_source_aligned
    double_reverse_endpoint_matrix_refines_source
    double_reverse_two_pass_cell_refines_kernel
    double_reverse_ordered_pair_regression
    threshold5_carry_reset threshold5_weight_append threshold5_weight_repeat};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Double-reverse temporal refinement depends on an oracle";
\<close>

end
