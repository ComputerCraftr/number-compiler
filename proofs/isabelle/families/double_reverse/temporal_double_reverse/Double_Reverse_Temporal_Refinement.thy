theory Double_Reverse_Temporal_Refinement
  imports Double_Reverse_Decimal_Arithmetic
    Shared_Carry_Dynamics.Temporal_Moment_Algebra
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

text \<open>The mod-99 clock composes only after the width growth and skew
moment of the first source interval are supplied.  It is a scalar quotient
action; this theorem does not authorize any digit word or source interior.\<close>

definition double_reverse_mod99_clock_exponent ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "double_reverse_mod99_clock_exponent width steps skew =
    steps * (width - 1) + skew"

definition double_reverse_mod99_clock_action ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "double_reverse_mod99_clock_action width steps skew residue =
    (residue * 2 ^ steps *
      10 ^ double_reverse_mod99_clock_exponent width steps skew) mod 99"

definition double_reverse_width_moments ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> increment_moments" where
  "double_reverse_width_moments steps growth skew =
    \<lparr>im_span = steps, im_sum = int growth, im_skew = int skew\<rparr>"

lemma double_reverse_width_moments_then:
  "double_reverse_width_moments (first + second)
      (first_growth + second_growth)
      (first_skew + second_skew + second * first_growth) =
    increment_moments_then
      (double_reverse_width_moments first first_growth first_skew)
      (double_reverse_width_moments second second_growth second_skew)"
  by (simp add: double_reverse_width_moments_def
      increment_moments_then_def algebra_simps)

lemma double_reverse_mod99_clock_exponent_shared:
  assumes width: "0 < width"
  shows "int (double_reverse_mod99_clock_exponent width steps skew) =
    increment_moments_weighted_exponent (int width)
      (double_reverse_width_moments steps growth skew)"
  using width
  by (cases width)
    (simp_all add: double_reverse_mod99_clock_exponent_def
      increment_moments_weighted_exponent_def
      double_reverse_width_moments_def)

lemma double_reverse_mod99_clock_exponent_compose:
  assumes width: "0 < width"
  shows "double_reverse_mod99_clock_exponent width (first + second)
      (first_skew + second_skew + second * first_growth) =
    double_reverse_mod99_clock_exponent width first first_skew +
    double_reverse_mod99_clock_exponent (width + first_growth)
      second second_skew"
proof -
  let ?first = "double_reverse_width_moments first first_growth first_skew"
  let ?second = "double_reverse_width_moments second second_growth second_skew"
  have combined:
    "double_reverse_width_moments (first + second)
        (first_growth + second_growth)
        (first_skew + second_skew + second * first_growth) =
      increment_moments_then ?first ?second"
    by (rule double_reverse_width_moments_then)
  have shared:
    "increment_moments_weighted_exponent (int width)
        (increment_moments_then ?first ?second) =
      increment_moments_weighted_exponent (int width) ?first +
      increment_moments_weighted_exponent (int width + im_sum ?first) ?second"
    by (rule increment_moments_weighted_exponent_then)
  have left:
    "int (double_reverse_mod99_clock_exponent width (first + second)
        (first_skew + second_skew + second * first_growth)) =
      increment_moments_weighted_exponent (int width)
        (increment_moments_then ?first ?second)"
    using double_reverse_mod99_clock_exponent_shared[OF width,
        where steps="first + second"
          and growth="first_growth + second_growth"
          and skew="first_skew + second_skew + second * first_growth"]
      combined by simp
  have width_after: "0 < width + first_growth"
    using width by simp
  have first_exponent:
    "int (double_reverse_mod99_clock_exponent width first first_skew) =
      increment_moments_weighted_exponent (int width) ?first"
    using double_reverse_mod99_clock_exponent_shared[OF width,
        where steps=first and growth=first_growth and skew=first_skew]
    by simp
  have second_exponent:
    "int (double_reverse_mod99_clock_exponent
        (width + first_growth) second second_skew) =
      increment_moments_weighted_exponent
        (int width + im_sum ?first) ?second"
    using double_reverse_mod99_clock_exponent_shared[OF width_after,
        where steps=second and growth=second_growth and skew=second_skew]
    by (simp add: double_reverse_width_moments_def)
  have integer_equality:
    "int (double_reverse_mod99_clock_exponent width (first + second)
        (first_skew + second_skew + second * first_growth)) =
      int (double_reverse_mod99_clock_exponent width first first_skew) +
      int (double_reverse_mod99_clock_exponent
        (width + first_growth) second second_skew)"
    using left shared first_exponent second_exponent by simp
  then show ?thesis
    by (simp only: of_nat_add[symmetric] of_nat_eq_iff)
qed

theorem double_reverse_mod99_clock_action_compose:
  assumes width: "0 < width"
  shows "double_reverse_mod99_clock_action width (first + second)
      (first_skew + second_skew + second * first_growth) residue =
    double_reverse_mod99_clock_action (width + first_growth)
      second second_skew
      (double_reverse_mod99_clock_action width first first_skew residue)"
proof -
  have exponent:
    "double_reverse_mod99_clock_exponent width (first + second)
        (first_skew + second_skew + second * first_growth) =
      double_reverse_mod99_clock_exponent width first first_skew +
      double_reverse_mod99_clock_exponent (width + first_growth)
        second second_skew"
    by (rule double_reverse_mod99_clock_exponent_compose[OF width])
  have factor:
    "residue * 2 ^ (first + second) *
        10 ^ double_reverse_mod99_clock_exponent width (first + second)
          (first_skew + second_skew + second * first_growth) =
      (residue * 2 ^ first *
        10 ^ double_reverse_mod99_clock_exponent width first first_skew) *
        2 ^ second *
        10 ^ double_reverse_mod99_clock_exponent (width + first_growth)
          second second_skew"
    using exponent
    by (simp add: power_add algebra_simps)
  show ?thesis
    unfolding double_reverse_mod99_clock_action_def factor
    by (simp only: mult.assoc mod_mult_left_eq)
qed

text \<open>A pointed output coordinate is expressed from the final word and
translated back to the entry source by subtracting the left-side births.
The mirror coordinate has a separate right-side birth offset; this is why
the two growth ports cannot be collapsed into a single width increment.\<close>

definition double_reverse_entry_pair_start :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "double_reverse_entry_pair_start final_pair_start left_births =
    final_pair_start - left_births"

lemma double_reverse_entry_pair_start_inverse:
  assumes translated: "entry_pair + left_births = final_pair_start"
  shows "double_reverse_entry_pair_start final_pair_start left_births =
    entry_pair"
  using translated
  unfolding double_reverse_entry_pair_start_def
  by presburger

lemma double_reverse_final_mirror_coordinate:
  fixes entry_pair source_width left_births right_births final_pair_start :: nat
  assumes entry: "entry_pair < source_width"
    and translated: "entry_pair + left_births = final_pair_start"
  shows "source_width + left_births + right_births - 1 - final_pair_start =
    source_width - 1 - entry_pair + right_births"
proof -
  have final_start: "final_pair_start = entry_pair + left_births"
    using translated by simp
  show ?thesis
    using entry final_start
    by (subst final_start; arith)
qed

lemma double_reverse_final_pair_interval_to_entry:
  assumes start: "entry_pair + left_births = final_pair_start"
    and offset: "entry_offset < pair_count"
  shows "double_reverse_entry_pair_start
      (final_pair_start + entry_offset) left_births =
    entry_pair + entry_offset"
  using start offset
  unfolding double_reverse_entry_pair_start_def
  by presburger

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

lemma double_reverse_radius_one_carry_primitive:
  assumes digits: "left < 10" "center < 10" "right < 10"
  shows "double_reverse_two_pass_cell left center right =
    (2 * ((2*center + threshold5_digit left) mod 10) +
      (if (2*right + threshold5_digit center) mod 10 \<ge> 5
       then 1 else 0)) mod 10"
  using digits
  unfolding double_reverse_two_pass_cell_def
    double_reverse_first_pass_cell_def
  by simp

text \<open>The guarded periodic bank emits an exact five-way partition of a
source-aligned decimal pair.  Its two borrow outputs are conditional local
responses for incoming borrow 0 or 1; they are not a reconstructed
full-width innovation tape or a closure theorem for arbitrary roots.\<close>

definition double_reverse_pair_lt_low :: "nat \<Rightarrow> nat" where
  "double_reverse_pair_lt_low pair = (if pair < 5 then 1 else 0)"

definition double_reverse_pair_lt_high :: "nat \<Rightarrow> nat" where
  "double_reverse_pair_lt_high pair =
    (if 5 \<le> pair \<and> pair \<le> 8 then 1 else 0)"

definition double_reverse_pair_eq :: "nat \<Rightarrow> nat" where
  "double_reverse_pair_eq pair = (if pair = 9 then 1 else 0)"

definition double_reverse_pair_gt_low :: "nat \<Rightarrow> nat" where
  "double_reverse_pair_gt_low pair =
    (if 10 \<le> pair \<and> pair \<le> 14 then 1 else 0)"

definition double_reverse_pair_gt_high :: "nat \<Rightarrow> nat" where
  "double_reverse_pair_gt_high pair =
    (if 15 \<le> pair \<and> pair \<le> 18 then 1 else 0)"

theorem double_reverse_pair_band_partition:
  assumes "pair \<le> 18"
  shows "double_reverse_pair_lt_low pair +
      double_reverse_pair_lt_high pair + double_reverse_pair_eq pair +
      double_reverse_pair_gt_low pair + double_reverse_pair_gt_high pair = 1"
  using assms
  by (simp add: double_reverse_pair_lt_low_def
      double_reverse_pair_lt_high_def double_reverse_pair_eq_def
      double_reverse_pair_gt_low_def double_reverse_pair_gt_high_def;
      presburger)

lemma double_reverse_decimal_pair_band_partition:
  assumes "left < 10" "right < 10"
  shows "double_reverse_pair_lt_low (left + right) +
      double_reverse_pair_lt_high (left + right) +
      double_reverse_pair_eq (left + right) +
      double_reverse_pair_gt_low (left + right) +
      double_reverse_pair_gt_high (left + right) = 1"
proof -
  have "left + right \<le> 18" using assms by presburger
  then show ?thesis by (rule double_reverse_pair_band_partition)
qed

definition double_reverse_conditional_borrow :: "nat \<Rightarrow> nat \<Rightarrow> nat
    \<Rightarrow> nat" where
  "double_reverse_conditional_borrow before after incoming =
    (if after < before + incoming then 1 else 0)"

lemma double_reverse_conditional_borrow_ports:
  "(double_reverse_conditional_borrow before after 0,
    double_reverse_conditional_borrow before after 1) =
   ((if after < before then 1 else 0),
    (if after < Suc before then 1 else 0))"
  by (simp add: double_reverse_conditional_borrow_def)

text \<open>The pointed temporal evaluator is admitted only after its exact
two-cell edge enters this nine-state cylinder.  This finite relation records
both possible inward carries at the shrinking-side edge and the forced
carry-independent branch at the other edge.  It proves border closure and
phase advance, not generation of an arbitrary interior word by Hashlife.\<close>

text \<open>A three-cell lift retains the exact high/low feedback which the
two-cell relation omits.  Its fourth-from-low carry is the only free port;
the current and next inward carries are derived from the source's low triple
and the computed successor low triple.  This refinement is local and does
not claim arbitrary-source temporal closure.\<close>

type_synonym double_reverse_digit_triple = "nat \<times> nat \<times> nat"

definition double_reverse_three_cell_low ::
    "double_reverse_digit_triple \<Rightarrow> double_reverse_digit_triple" where
  "double_reverse_three_cell_low high = (case high of (a,b,c) \<Rightarrow>
    ((2*c + threshold5_digit b) mod 10,
     (2*b + threshold5_digit a) mod 10, (2*a) mod 10))"

definition double_reverse_three_cell_high ::
    "double_reverse_digit_triple \<Rightarrow> double_reverse_digit_triple
      \<Rightarrow> nat \<Rightarrow> double_reverse_digit_triple option" where
  "double_reverse_three_cell_high high low fourth =
    (case (high,low) of ((a,b,c),(x,y,z)) \<Rightarrow>
      if 5 \<le> z then Some (1, (2*z + threshold5_digit y) mod 10,
        (2*y + threshold5_digit x) mod 10)
      else if 2*z + threshold5_digit y = 0 then None
      else Some (2*z + threshold5_digit y,
        (2*y + threshold5_digit x) mod 10, (2*x + fourth) mod 10))"

definition double_reverse_three_cell_forced_carries ::
    "double_reverse_digit_triple \<Rightarrow> double_reverse_digit_triple
      \<Rightarrow> nat \<times> nat" where
  "double_reverse_three_cell_forced_carries high low =
    (case (high,low) of ((a,b,c),(x,y,z)) \<Rightarrow>
      (threshold5_digit x,
       threshold5_digit ((2*c + threshold5_digit b) mod 10)))"

lemma double_reverse_three_cell_carry_feedback:
  "double_reverse_three_cell_forced_carries high low =
    (threshold5_digit (fst low),
     threshold5_digit (fst (double_reverse_three_cell_low high)))"
  by (cases high; cases low; simp add: double_reverse_three_cell_forced_carries_def
      double_reverse_three_cell_low_def)

lemma double_reverse_three_cell_fourth_carry_locality:
  "(case double_reverse_three_cell_high high low first of
      None \<Rightarrow> None
    | Some (a,b,c) \<Rightarrow> Some (a,b)) =
   (case double_reverse_three_cell_high high low second of
      None \<Rightarrow> None
    | Some (a,b,c) \<Rightarrow> Some (a,b))"
  by (cases high; cases low; simp add: double_reverse_three_cell_high_def)
lemma double_reverse_three_cell_source_step:
  fixes n source_low a b c :: nat
  assumes source_low_def: "source_low = double_reverse_reverse10 n mod 1000"
    and a_def: "a = source_low mod 10"
    and b_def: "b = (source_low div 10) mod 10"
    and c_def: "c = source_low div 100"
  shows "double_reverse_T n mod 1000 =
    100*((2*c + threshold5_digit b) mod 10) +
    10*((2*b + threshold5_digit a) mod 10) + (2*a mod 10)"
proof -
  have ab: "a < 10" using mod_less_divisor[of source_low 10] a_def by arith
  have bb: "b < 10" using mod_less_divisor[of "source_low div 10" 10] b_def by arith
  have source_digits: "source_low = 100*c + 10*b + a"
    using div_mult_mod_eq[of source_low 10] div_mult_mod_eq[of "source_low div 10" 10]
    by (simp only: a_def b_def c_def div_mult2_eq[symmetric] arith_simps; linarith)
  have actual: "double_reverse_T n mod 1000 = (2*source_low) mod 1000"
    unfolding double_reverse_T_def source_low_def
    by (rule mod_mult_right_eq[symmetric])
  show ?thesis
    unfolding actual source_digits threshold5_digit_def
    by (rule decimal_double_three_digits[OF ab bb])
qed
type_synonym double_reverse_boundary_edge = "nat \<times> nat \<times> nat \<times> nat"

definition double_reverse_closed_border :: "double_reverse_boundary_edge set" where
  "double_reverse_closed_border =
    {(1,7,4,2), (1,7,6,8), (1,7,8,8),
     (4,8,4,2), (4,8,6,8), (4,8,8,8),
     (4,9,4,2), (4,9,6,8), (4,9,8,8)}"

definition double_reverse_border_phase ::
    "double_reverse_boundary_edge \<Rightarrow> nat" where
  "double_reverse_border_phase edge =
    (case edge of (a,b,y,z) \<Rightarrow>
      (if a = 1 then (if z = 8 then 0 else 1)
       else (if z = 8 then 3 else 2)))"

definition double_reverse_border_target ::
    "double_reverse_boundary_edge \<Rightarrow> nat \<Rightarrow>
      double_reverse_boundary_edge" where
  "double_reverse_border_target edge inward =
    (case edge of (a,b,y,z) \<Rightarrow>
      (if 5 \<le> z then
        (1, (2*z + threshold5_digit y) mod 10,
          (2*b + threshold5_digit a) mod 10, (2*a) mod 10)
       else
        (2*z + threshold5_digit y, (2*y + inward) mod 10,
          (2*b + threshold5_digit a) mod 10, (2*a) mod 10)))"

definition double_reverse_border_width_growth ::
    "double_reverse_boundary_edge \<Rightarrow> nat" where
  "double_reverse_border_width_growth edge =
    (case edge of (a,b,y,z) \<Rightarrow> if 5 \<le> z then 1 else 0)"

lemma double_reverse_closed_border_ingress_closed:
  assumes edge: "edge \<in> double_reverse_closed_border"
    and inward: "inward < 2"
  shows "double_reverse_border_target edge inward \<in>
    double_reverse_closed_border"
proof -
  have inward_cases: "inward = 0 \<or> inward = 1"
    using inward by presburger
  have edge_cases:
    "edge = (1,7,4,2) \<or> edge = (1,7,6,8) \<or>
      edge = (1,7,8,8) \<or> edge = (4,8,4,2) \<or>
      edge = (4,8,6,8) \<or> edge = (4,8,8,8) \<or>
      edge = (4,9,4,2) \<or> edge = (4,9,6,8) \<or>
      edge = (4,9,8,8)"
    using edge by (simp add: double_reverse_closed_border_def)
  show ?thesis
    using edge_cases inward_cases
    by (elim disjE; simp add: double_reverse_closed_border_def
        double_reverse_border_target_def threshold5_digit_def)
qed

lemma double_reverse_closed_border_phase_step:
  assumes edge: "edge \<in> double_reverse_closed_border"
    and inward: "inward < 2"
  shows "double_reverse_border_phase
      (double_reverse_border_target edge inward) =
    (double_reverse_border_phase edge + 1) mod 4"
proof -
  have inward_cases: "inward = 0 \<or> inward = 1"
    using inward by presburger
  have edge_cases:
    "edge = (1,7,4,2) \<or> edge = (1,7,6,8) \<or>
      edge = (1,7,8,8) \<or> edge = (4,8,4,2) \<or>
      edge = (4,8,6,8) \<or> edge = (4,8,8,8) \<or>
      edge = (4,9,4,2) \<or> edge = (4,9,6,8) \<or>
      edge = (4,9,8,8)"
    using edge by (simp add: double_reverse_closed_border_def)
  show ?thesis
    using edge_cases inward_cases
    by (elim disjE; simp add: double_reverse_closed_border_def
        double_reverse_border_phase_def double_reverse_border_target_def
        threshold5_digit_def)
qed

lemma double_reverse_closed_border_two_phase_steps:
  assumes edge: "edge \<in> double_reverse_closed_border"
    and first_inward: "first_inward < 2"
    and second_inward: "second_inward < 2"
  shows "double_reverse_border_phase
      (double_reverse_border_target
        (double_reverse_border_target edge first_inward) second_inward) =
    double_reverse_phase_after 1 (double_reverse_border_phase edge)"
proof -
  have first_closed:
    "double_reverse_border_target edge first_inward \<in>
      double_reverse_closed_border"
    by (rule double_reverse_closed_border_ingress_closed[OF edge first_inward])
  have first_phase:
    "double_reverse_border_phase
      (double_reverse_border_target edge first_inward) =
      (double_reverse_border_phase edge + 1) mod 4"
    by (rule double_reverse_closed_border_phase_step[OF edge first_inward])
  have second_phase:
    "double_reverse_border_phase
      (double_reverse_border_target
        (double_reverse_border_target edge first_inward) second_inward) =
      (double_reverse_border_phase
        (double_reverse_border_target edge first_inward) + 1) mod 4"
    by (rule double_reverse_closed_border_phase_step[OF first_closed second_inward])
  let ?phase = "double_reverse_border_phase edge"
  have one_plus: "(1::nat) + 1 = 2" by simp
  have mod_nested: "(( (?phase + 1) mod 4 + 1) mod 4) =
      (?phase + 2) mod 4"
    by (simp only: mod_add_left_eq add.assoc one_plus)
  show ?thesis
    using first_phase second_phase mod_nested
    by (simp add: double_reverse_phase_after_def)
qed

definition double_reverse_border_physical_births :: "nat \<Rightarrow> nat \<times> nat" where
  "double_reverse_border_physical_births phase =
    (if phase mod 4 = 3 then 1 else 0,
     if phase mod 4 = 0 then 1 else 0)"

definition double_reverse_border_pair_births :: "nat \<Rightarrow> nat \<times> nat" where
  "double_reverse_border_pair_births phase =
    double_reverse_growth_then
      (double_reverse_border_physical_births phase)
      (double_reverse_border_physical_births ((phase + 1) mod 4))"

lemma double_reverse_closed_border_growth_matches_width:
  assumes edge: "edge \<in> double_reverse_closed_border"
  shows "double_reverse_border_width_growth edge =
    fst (double_reverse_border_physical_births
      (double_reverse_border_phase edge)) +
    snd (double_reverse_border_physical_births
      (double_reverse_border_phase edge))"
  using edge
  by (auto simp: double_reverse_closed_border_def
      double_reverse_border_width_growth_def double_reverse_border_phase_def
      double_reverse_border_physical_births_def split: prod.splits)

lemma double_reverse_border_pair_births_match_controller:
  assumes phase: "phase < 4"
  shows "double_reverse_border_pair_births phase =
    (double_reverse_left_birth phase, double_reverse_right_birth phase)"
  using phase
  by (cases phase; simp add: double_reverse_border_pair_births_def
      double_reverse_border_physical_births_def double_reverse_growth_then_def
      double_reverse_left_birth_def double_reverse_right_birth_def)

fun double_reverse_closed_border_growth_trace ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<times> nat" where
  "double_reverse_closed_border_growth_trace 0 phase = (0,0)"
| "double_reverse_closed_border_growth_trace (Suc steps) phase =
    double_reverse_growth_then
      (double_reverse_border_pair_births phase)
      (double_reverse_closed_border_growth_trace steps
        (double_reverse_phase_after 1 phase))"

lemma double_reverse_closed_border_growth_trace_refines_controller:
  assumes phase: "phase < 4"
  shows "double_reverse_closed_border_growth_trace steps phase =
    double_reverse_growth_trace steps phase"
  using phase
proof (induction steps arbitrary: phase)
  case 0
  then show ?case by simp
next
  case (Suc steps)
  have next_phase: "double_reverse_phase_after 1 phase < 4"
    using Suc.prems
    unfolding double_reverse_phase_after_def
    by presburger
  have pair:
    "double_reverse_border_pair_births phase =
      (double_reverse_left_birth phase, double_reverse_right_birth phase)"
    by (rule double_reverse_border_pair_births_match_controller[OF Suc.prems])
  have ih:
    "double_reverse_closed_border_growth_trace steps
        (double_reverse_phase_after 1 phase) =
      double_reverse_growth_trace steps (double_reverse_phase_after 1 phase)"
    by (rule Suc.IH[OF next_phase])
  show ?case
    using pair ih
    by (simp add: double_reverse_growth_then_def)
qed

theorem double_reverse_closed_border_growth_trace_even:
  assumes phase: "phase < 4"
  shows "double_reverse_closed_border_growth_trace (2*returns) phase =
    (returns, returns)"
proof -
  have refinement:
    "double_reverse_closed_border_growth_trace (2*returns) phase =
      double_reverse_growth_trace (2*returns) phase"
    by (rule double_reverse_closed_border_growth_trace_refines_controller[OF phase])
  have controller:
    "double_reverse_growth_trace (2*returns) phase = (returns, returns)"
    by (rule double_reverse_growth_trace_even[OF phase])
  show ?thesis using refinement controller by simp
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
    double_reverse_mod99_clock_exponent_compose
    double_reverse_mod99_clock_action_compose
    double_reverse_entry_pair_start_inverse
    double_reverse_final_mirror_coordinate
    double_reverse_final_pair_interval_to_entry
    double_reverse_interval_moments_source_aligned
    double_reverse_endpoint_matrix_refines_source
    double_reverse_decimal_arithmetic_oracle_audit_bundle
    double_reverse_two_pass_cell_refines_kernel
    double_reverse_radius_one_carry_primitive
    double_reverse_pair_band_partition
    double_reverse_decimal_pair_band_partition
    double_reverse_conditional_borrow_ports
    double_reverse_three_cell_carry_feedback
    double_reverse_three_cell_fourth_carry_locality
    double_reverse_three_cell_source_step
    double_reverse_closed_border_ingress_closed
    double_reverse_closed_border_phase_step
    double_reverse_closed_border_two_phase_steps
    double_reverse_closed_border_growth_matches_width
    double_reverse_border_pair_births_match_controller
    double_reverse_closed_border_growth_trace_refines_controller
    double_reverse_closed_border_growth_trace_even
    double_reverse_ordered_pair_regression
    threshold5_carry_reset threshold5_weight_append threshold5_weight_repeat};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Double-reverse temporal refinement depends on an oracle";
\<close>

end
