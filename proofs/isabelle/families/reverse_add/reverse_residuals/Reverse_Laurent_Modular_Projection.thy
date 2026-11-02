theory Reverse_Laurent_Modular_Projection
  imports Reverse_Laurent_Producer_Refinement
    Shared_Carry_Dynamics.Decimal_Repunit_Modular
begin

text \<open>The source-issued carry switches describe alternating true-carry
intervals.  This theory proves that the interval projection used by the
production port is exactly the internal carry mask, for every modulus.  The
final carry at the source width is deliberately excluded from the mask and is
carried separately as the growth bit.\<close>

fun reverse_laurent_true_carry_intervals ::
    "nat \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> nat list \<Rightarrow> (nat \<times> nat) list" where
  "reverse_laurent_true_carry_intervals width start active [] =
    (if active \<and> start < width then [(start, width - 1)] else [])"
| "reverse_laurent_true_carry_intervals width start active (switch # switches) =
    (if active \<and> start < switch then [(start, switch - 1)] else []) @
      reverse_laurent_true_carry_intervals width switch (\<not> active) switches"

definition reverse_laurent_interval_value ::
    "nat \<Rightarrow> nat \<times> nat \<Rightarrow> nat" where
  "reverse_laurent_interval_value width interval =
    (case interval of (lo, hi) \<Rightarrow>
      if lo \<le> hi \<and> hi < width
      then decimal_interval_sum width lo hi else 0)"

fun reverse_laurent_interval_sum ::
    "nat \<Rightarrow> (nat \<times> nat) list \<Rightarrow> nat" where
  "reverse_laurent_interval_sum width [] = 0"
| "reverse_laurent_interval_sum width (interval # intervals) =
    reverse_laurent_interval_value width interval +
      reverse_laurent_interval_sum width intervals"

definition reverse_laurent_switch_interval_sum ::
    "nat \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> nat list \<Rightarrow> nat" where
  "reverse_laurent_switch_interval_sum width start active switches =
    reverse_laurent_interval_sum width
      (reverse_laurent_true_carry_intervals width start active switches)"

definition reverse_laurent_interval_projection_piece ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<times> nat \<Rightarrow> nat" where
  "reverse_laurent_interval_projection_piece width modulus interval =
    (case interval of (lo, hi) \<Rightarrow>
      if lo \<le> hi \<and> hi < width then
        ((10 ^ (width - Suc hi) mod modulus) *
          (((10 ^ (hi - lo + 1) mod (9 * modulus) - 1) div 9)
            mod modulus)) mod modulus
      else 0)"

fun reverse_laurent_interval_projection_fold ::
    "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) list \<Rightarrow> nat" where
  "reverse_laurent_interval_projection_fold width modulus [] = 0"
| "reverse_laurent_interval_projection_fold width modulus
      (interval # intervals) =
    (reverse_laurent_interval_projection_piece width modulus interval +
      reverse_laurent_interval_projection_fold width modulus intervals) mod modulus"

definition reverse_laurent_switch_interval_projection ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> nat list \<Rightarrow> nat" where
  "reverse_laurent_switch_interval_projection width modulus start active switches =
    reverse_laurent_interval_projection_fold width modulus
      (reverse_laurent_true_carry_intervals width start active switches)"

lemma reverse_laurent_interval_sum_shift:
  "reverse_laurent_interval_sum (Suc width)
      (map (\<lambda>(lo, hi). (Suc lo, Suc hi)) intervals) =
    reverse_laurent_interval_sum width intervals"
proof (induction intervals)
  case Nil
  then show ?case by simp
next
  case (Cons interval intervals)
  obtain lo hi where interval: "interval = (lo, hi)"
    by (cases interval) auto
  have value_shift:
    "reverse_laurent_interval_value (Suc width)
        (Suc lo, Suc hi) =
      reverse_laurent_interval_value width (lo, hi)"
  proof (cases "lo \<le> hi \<and> hi < width")
    case True
    have shifted_order: "Suc lo \<le> Suc hi"
      using True by simp
    have shifted_inside: "Suc hi < Suc width"
      using True by simp
    have base_order: "lo \<le> hi" using True by auto
    have base_inside: "hi < width" using True by auto
    have shifted_formula:
      "decimal_interval_sum (Suc width) (Suc lo) (Suc hi) =
        10 ^ ((Suc width) - 1 - (Suc hi)) *
          decimal_repunit ((Suc hi) - (Suc lo) + 1)"
      by (rule decimal_interval_sum_geometric[OF shifted_order shifted_inside])
    have base_formula:
      "decimal_interval_sum width lo hi =
        10 ^ (width - 1 - hi) * decimal_repunit (hi - lo + 1)"
      by (rule decimal_interval_sum_geometric[OF base_order base_inside])
    have exponent:
      "(Suc width) - 1 - (Suc hi) = width - 1 - hi"
      by arith
    have length:
      "(Suc hi) - (Suc lo) + 1 = hi - lo + 1"
      by arith
    show ?thesis using True shifted_formula base_formula exponent length
      by (simp add: reverse_laurent_interval_value_def)
  next
    case False
    show ?thesis using False
      by (auto simp: reverse_laurent_interval_value_def)
  qed
  show ?case using Cons.IH value_shift interval by simp
qed

lemma reverse_laurent_true_carry_intervals_shift:
  "reverse_laurent_true_carry_intervals (Suc width) (Suc start) active
      (map Suc switches) =
    map (\<lambda>(lo, hi). (Suc lo, Suc hi))
      (reverse_laurent_true_carry_intervals width start active switches)"
proof (induction switches arbitrary: start active)
  case Nil
  then show ?case by (cases active) simp_all
next
  case (Cons switch switches)
  show ?case
    using Cons.IH[of switch "\<not> active"]
    by (cases active; auto split: if_splits; arith)
qed

lemma reverse_laurent_switch_interval_sum_shift:
  "reverse_laurent_switch_interval_sum (Suc width) (Suc start) active
      (map Suc switches) =
    reverse_laurent_switch_interval_sum width start active switches"
  unfolding reverse_laurent_switch_interval_sum_def
  by (simp only: reverse_laurent_true_carry_intervals_shift
      reverse_laurent_interval_sum_shift)

lemma reverse_laurent_interval_value_split_first:
  fixes width hi :: nat
  assumes width: "1 < width"
    and positive_hi: "0 < hi"
    and inside: "hi < width"
  shows "reverse_laurent_interval_value width (1, hi) =
      10 ^ (width - 2) +
        reverse_laurent_interval_value width (2, hi)"
proof -
  have first_order: "1 \<le> hi" using positive_hi by arith
  have first_formula:
    "decimal_interval_sum width 1 hi =
      10 ^ (width - 1 - hi) * decimal_repunit (hi - 1 + 1)"
    by (rule decimal_interval_sum_geometric[OF first_order inside])
  have first_exponent:
    "width - 1 - hi = width - Suc hi"
    by arith
  have first_count: "hi - 1 + 1 = hi"
    using first_order by arith
  have first_geometric:
    "decimal_interval_sum width 1 hi =
      10 ^ (width - Suc hi) * decimal_repunit hi"
    using first_formula first_exponent first_count by simp
  obtain offset where upper_form: "hi = Suc offset"
    using positive_hi by (cases hi) auto
  show ?thesis
  proof (cases offset)
    case 0
    have upper_one: "hi = 1" using upper_form 0 by simp
    show ?thesis using width upper_one first_geometric
      by (simp add: reverse_laurent_interval_value_def)
  next
    case (Suc remainder)
    have upper_two: "hi = Suc (Suc remainder)"
      using upper_form Suc by simp
    have tail_order: "2 \<le> Suc (Suc remainder)" by simp
    have tail_inside: "Suc (Suc remainder) < width"
      using upper_two inside by simp
    have tail_formula:
      "decimal_interval_sum width 2 (Suc (Suc remainder)) =
        10 ^ (width - 1 - Suc (Suc remainder)) *
          decimal_repunit (Suc (Suc remainder) - 2 + 1)"
      by (rule decimal_interval_sum_geometric[OF tail_order tail_inside])
    have tail_exponent:
      "width - 1 - Suc (Suc remainder) =
        width - Suc (Suc (Suc remainder))"
      by arith
    have tail_count:
      "Suc (Suc remainder) - 2 + 1 = Suc remainder"
      by arith
    have tail_geometric:
      "decimal_interval_sum width 2 (Suc (Suc remainder)) =
          10 ^ (width - Suc (Suc (Suc remainder))) *
          decimal_repunit (Suc remainder)"
      using tail_formula tail_exponent tail_count by simp
    have repunit_step:
      "decimal_repunit (Suc (Suc remainder)) =
        decimal_repunit (Suc remainder) + 10 ^ (Suc remainder)"
    proof -
      have recurrence:
        "decimal_repunit (Suc (Suc remainder)) =
          10 * decimal_repunit (Suc remainder) + 1"
        by (rule decimal_repunit_recurrence)
      have power_identity:
        "10 ^ (Suc remainder) =
          9 * decimal_repunit (Suc remainder) + 1"
        by (rule decimal_repunit_power_identity[symmetric])
      show ?thesis using recurrence power_identity by arith
    qed
    have exponent:
      "width - Suc (Suc (Suc remainder)) + Suc remainder = width - 2"
      using upper_two inside by arith
    have power_product:
      "(10::nat) ^ (width - Suc (Suc (Suc remainder))) *
          (10::nat) ^ (Suc remainder) =
        (10::nat) ^ (width - 2)"
    proof -
      have "(10::nat) ^ (width - Suc (Suc (Suc remainder))) *
          (10::nat) ^ (Suc remainder) =
          (10::nat) ^ (width - Suc (Suc (Suc remainder)) + Suc remainder)"
        by (rule power_add[symmetric])
      also have "... = 10 ^ (width - 2)"
        by (simp only: exponent)
      finally show ?thesis .
    qed
    have full_interval:
      "reverse_laurent_interval_value width (1, hi) =
        10 ^ (width - Suc (Suc (Suc remainder))) *
          decimal_repunit (Suc (Suc remainder))"
      using upper_two first_geometric inside
      by (simp add: reverse_laurent_interval_value_def)
    have tail_interval:
      "reverse_laurent_interval_value width (2, hi) =
        10 ^ (width - Suc (Suc (Suc remainder))) *
          decimal_repunit (Suc remainder)"
      using upper_two tail_geometric inside
      by (simp add: reverse_laurent_interval_value_def)
    have split_value:
      "10 ^ (width - Suc (Suc (Suc remainder))) *
          decimal_repunit (Suc (Suc remainder)) =
        10 ^ (width - 2) +
          10 ^ (width - Suc (Suc (Suc remainder))) *
            decimal_repunit (Suc remainder)"
      by (subst repunit_step)
        (simp only: distrib_left power_product add.commute)
    show ?thesis using full_interval tail_interval split_value
      by simp
  qed
qed

lemma reverse_laurent_switch_interval_sum_peel:
  assumes width: "1 < width"
    and switches: "\<forall>switch\<in>set switches. 0 < switch \<and> switch < width"
  shows "reverse_laurent_switch_interval_sum width 1 active
      (map Suc switches) =
    (if active then 10 ^ (width - 2) else 0) +
      reverse_laurent_switch_interval_sum width 2 active
        (map Suc switches)"
proof (cases active)
  case False
  then show ?thesis by (cases switches) (simp_all
      add: reverse_laurent_switch_interval_sum_def)
next
  case True
  show ?thesis
  proof (cases switches)
    case Nil
    have upper_positive: "0 < width - 1" using width by arith
    have upper_inside: "width - 1 < width" using width by arith
    have split_value:
      "reverse_laurent_interval_value width (1, width - 1) =
        10 ^ (width - 2) +
          reverse_laurent_interval_value width (2, width - 1)"
      by (rule reverse_laurent_interval_value_split_first[OF width
          upper_positive upper_inside])
    have active_case: "active" using True .
    show ?thesis
    proof (cases "width = 2")
      case True
      show ?thesis using Nil active_case split_value True
        by (simp add: reverse_laurent_switch_interval_sum_def
            reverse_laurent_interval_value_def)
    next
      case False
      have width_gt_two: "2 < width" using width False by arith
      show ?thesis using Nil active_case split_value width_gt_two False
        by (simp add: reverse_laurent_switch_interval_sum_def
            reverse_laurent_interval_value_def)
    qed
  next
    case (Cons switch tail)
    have switch_positive: "0 < switch" using switches Cons by auto
    have switch_inside: "switch < width" using switches Cons by auto
    have active_case: "active" using True .
    show ?thesis
    proof (cases "switch = 1")
      case True
      show ?thesis using Cons active_case switch_positive switch_inside True
          reverse_laurent_interval_value_split_first[OF width switch_positive
            switch_inside]
        by (simp add: reverse_laurent_switch_interval_sum_def
            reverse_laurent_interval_value_def)
    next
      case False
      have switch_gt_one: "1 < switch" using switch_positive False by arith
      show ?thesis using Cons active_case switch_positive switch_inside
          switch_gt_one False
          reverse_laurent_interval_value_split_first[OF width switch_positive
            switch_inside]
        by (simp add: reverse_laurent_switch_interval_sum_def
            reverse_laurent_interval_value_def)
    qed
  qed
qed

lemma reverse_laurent_switch_trace_within_width:
  "switch \<le> position + length trace"
  if "switch \<in> set (reverse_laurent_switch_trace position active trace)"
  using that
proof (induction trace arbitrary: position active switch)
  case Nil
  then show ?case by simp
next
  case (Cons following trace)
  show ?case
  proof (cases "following = active")
    case True
    have member:
      "switch \<in> set (reverse_laurent_switch_trace (Suc position)
        following trace)"
      using Cons.prems True by simp
    have "switch \<le> Suc position + length trace"
      using Cons.IH[where position="Suc position" and active=following
          and switch=switch] member .
    then show ?thesis by simp
  next
    case False
    have member_or:
      "switch = Suc position \<or>
        switch \<in> set (reverse_laurent_switch_trace (Suc position)
          following trace)"
      using Cons.prems False by simp
    then show ?thesis
    proof
      assume "switch = Suc position"
      then show ?thesis by simp
    next
      assume member:
        "switch \<in> set (reverse_laurent_switch_trace (Suc position)
          following trace)"
      have "switch \<le> Suc position + length trace"
        using Cons.IH[where position="Suc position" and active=following
            and switch=switch] member .
      then show ?thesis by simp
    qed
  qed
qed

lemma reverse_laurent_decimal_carry_mask_cons:
  "decimal_list_value (rev (map carry_bit (butlast (following # trace)))) =
    (if trace = [] then 0 else
      carry_bit following * 10 ^ (length trace - 1)) +
      decimal_list_value (rev (map carry_bit (butlast trace)))"
proof (cases trace)
  case Nil
  then show ?thesis by simp
next
  case (Cons digit rest)
  have list_identity:
    "rev (map carry_bit (butlast (following # trace))) =
      rev (map carry_bit (butlast trace)) @ [carry_bit following]"
    using Cons by simp
  show ?thesis using Cons list_identity
    by (simp add: decimal_list_value_append algebra_simps)
qed

lemma reverse_laurent_switch_interval_trace_exact:
  "reverse_laurent_switch_interval_sum (length trace) 1 active
      (reverse_laurent_switch_trace 0 active trace) =
    decimal_list_value (rev (map carry_bit (butlast trace)))"
proof (induction trace arbitrary: active)
  case Nil
  then show ?case
    by (simp add: reverse_laurent_switch_interval_sum_def)
next
  case (Cons following trace)
  let ?tail_switches = "reverse_laurent_switch_trace 0 following trace"
  have tail_exact:
    "reverse_laurent_switch_interval_sum (length trace) 1 following
        ?tail_switches =
      decimal_list_value (rev (map carry_bit (butlast trace)))"
    by (rule Cons.IH)
  have tail_positive:
    "\<forall>switch\<in>set ?tail_switches. 0 < switch"
    using reverse_laurent_switch_trace_positions_above[where position=0
        and incoming=following and trace=trace]
    by auto
  have tail_within:
    "\<forall>switch\<in>set ?tail_switches. switch \<le> length trace"
    using reverse_laurent_switch_trace_within_width[where position=0
        and active=following and trace=trace]
    by auto
  have tail_bounds:
    "\<forall>switch\<in>set ?tail_switches. 0 < switch \<and>
      switch < Suc (length trace)"
    using tail_positive tail_within by auto
  have tail_bounds_step:
    "\<forall>switch\<in>set ?tail_switches. 0 < switch \<and>
      switch < length (following # trace)"
    using tail_bounds by simp
  have trace_switches:
    "reverse_laurent_switch_trace 0 active (following # trace) =
      (if following = active then [] else [1]) @ map Suc ?tail_switches"
    by (simp add: reverse_laurent_switch_trace_shift)
  show ?case
  proof (cases trace)
    case Nil
    then show ?thesis using trace_switches
      by (cases "following = active")
        (simp_all add: reverse_laurent_switch_interval_sum_def
          reverse_laurent_true_carry_intervals.simps)
  next
    case (Cons digit rest)
    have width: "1 < length (following # trace)" using Cons by simp
    have peel:
      "reverse_laurent_switch_interval_sum (length (following # trace)) 1
          following (map Suc ?tail_switches) =
        (if following then 10 ^ (length trace - 1) else 0) +
          reverse_laurent_switch_interval_sum (length (following # trace))
            2 following (map Suc ?tail_switches)"
      using reverse_laurent_switch_interval_sum_peel[OF width tail_bounds_step]
      by simp
    have shifted:
      "reverse_laurent_switch_interval_sum (length (following # trace)) 2
          following (map Suc ?tail_switches) =
        reverse_laurent_switch_interval_sum (length trace) 1 following
          ?tail_switches"
      using reverse_laurent_switch_interval_sum_shift[where
          width="length trace" and start=1 and active=following and
          switches="?tail_switches"]
      by (simp add: numeral_2_eq_2)
    have interval_result:
      "reverse_laurent_switch_interval_sum (length (following # trace)) 1
          active (reverse_laurent_switch_trace 0 active
            (following # trace)) =
        (if following then 10 ^ (length trace - 1) else 0) +
          reverse_laurent_switch_interval_sum (length trace) 1 following
            ?tail_switches"
    proof (cases "following = active")
      case True
      have unchanged:
        "reverse_laurent_switch_trace 0 active (following # trace) =
          map Suc ?tail_switches"
        using trace_switches True by simp
      show ?thesis using unchanged peel shifted True by simp
    next
      case False
      have changed:
        "reverse_laurent_switch_trace 0 active (following # trace) =
          [1] @ map Suc ?tail_switches"
        using trace_switches False by simp
      have following_state: "following = (\<not> active)"
        using False by (cases active; cases following) simp_all
      have changed_switches:
        "reverse_laurent_switch_interval_sum (length (following # trace)) 1
            active ([1] @ map Suc ?tail_switches) =
          reverse_laurent_switch_interval_sum (length (following # trace)) 1
            following (map Suc ?tail_switches)"
        using following_state
        by (cases active; simp add: reverse_laurent_switch_interval_sum_def
            reverse_laurent_true_carry_intervals.simps)
      show ?thesis using changed changed_switches peel shifted by simp
    qed
    have trace_nonempty: "trace \<noteq> []" using Cons by auto
    have head_bit:
      "(if following then 10 ^ (length trace - 1) else 0) =
        (if trace = [] then 0 else
          carry_bit following * 10 ^ (length trace - 1))"
      using trace_nonempty by (cases following) (simp_all add: carry_bit_def)
    have carry_word:
      "decimal_list_value (rev (map carry_bit (butlast (following # trace)))) =
        (if trace = [] then 0 else
          carry_bit following * 10 ^ (length trace - 1)) +
          decimal_list_value (rev (map carry_bit (butlast trace)))"
      by (rule reverse_laurent_decimal_carry_mask_cons)
    have exact_by_parts:
      "reverse_laurent_switch_interval_sum (length (following # trace)) 1
          active (reverse_laurent_switch_trace 0 active (following # trace)) =
        decimal_list_value (rev (map carry_bit
          (butlast (following # trace))))"
    proof -
      have "reverse_laurent_switch_interval_sum (length (following # trace)) 1
          active (reverse_laurent_switch_trace 0 active (following # trace)) =
          (if following then 10 ^ (length trace - 1) else 0) +
            decimal_list_value (rev (map carry_bit (butlast trace)))"
        by (simp only: interval_result tail_exact)
      also have "... =
          (if trace = [] then 0 else
            carry_bit following * 10 ^ (length trace - 1)) +
            decimal_list_value (rev (map carry_bit (butlast trace)))"
        by (simp only: head_bit)
      also have "... =
          decimal_list_value (rev (map carry_bit
            (butlast (following # trace))))"
        by (rule carry_word[symmetric])
      finally show ?thesis .
    qed
    show ?thesis using exact_by_parts .
  qed
qed

lemma reverse_laurent_interval_projection_piece_exact:
  fixes width modulus lo hi :: nat
  assumes modulus: "0 < modulus"
  shows "reverse_laurent_interval_projection_piece width modulus
      (lo, hi) =
    reverse_laurent_interval_value width (lo, hi) mod modulus"
proof (cases "lo \<le> hi \<and> hi < width")
  case False
  then show ?thesis
    by (auto simp: reverse_laurent_interval_projection_piece_def
        reverse_laurent_interval_value_def)
next
  case True
  have interval_formula:
    "decimal_interval_sum width lo hi =
      10 ^ (width - Suc hi) *
        decimal_repunit (hi - lo + 1)"
  proof -
    have ordered: "lo \<le> hi" using True by auto
    have inside: "hi < width" using True by auto
    have formula:
      "decimal_interval_sum width lo hi =
        10 ^ (width - 1 - hi) *
          decimal_repunit (hi - lo + 1)"
      by (rule decimal_interval_sum_geometric[OF ordered inside])
    have exponent: "width - 1 - hi = width - Suc hi"
      using inside by arith
    show ?thesis using formula exponent by simp
  qed
  have repunit_residue:
    "((10 ^ (hi - lo + 1) mod (9 * modulus) - 1) div 9) mod modulus =
      decimal_repunit (hi - lo + 1) mod modulus"
  proof -
    have reduced_power:
      "((10 ^ (hi - lo + 1) mod (9 * modulus) - 1) div 9) mod modulus =
        ((10 ^ (hi - lo + 1) - 1) div 9) mod modulus"
      by (rule decimal_repunit_mod_reduced_power[OF modulus])
    also have
      "... = decimal_repunit (hi - lo + 1) mod modulus"
      by (simp only: decimal_repunit_closed_form[symmetric])
    finally show ?thesis .
  qed
  let ?shift = "10 ^ (width - Suc hi)"
  let ?base = "(10 ^ (hi - lo + 1) mod (9 * modulus) - 1) div 9"
  have piece:
    "reverse_laurent_interval_projection_piece width modulus
        (lo, hi) = ((?shift mod modulus) * (?base mod modulus)) mod modulus"
    using True by (simp add: reverse_laurent_interval_projection_piece_def)
  have interval:
    "reverse_laurent_interval_value width (lo, hi) mod modulus =
      (?shift * decimal_repunit (hi - lo + 1)) mod modulus"
    using True interval_formula
    by (simp add: reverse_laurent_interval_value_def)
  have product_mod:
    "((?shift mod modulus) * (?base mod modulus)) mod modulus =
      (?shift * decimal_repunit (hi - lo + 1)) mod modulus"
  proof (rule mod_mult_cong)
    show "(?shift mod modulus) mod modulus = ?shift mod modulus"
      by simp
    show "(?base mod modulus) mod modulus =
        decimal_repunit (hi - lo + 1) mod modulus"
      using repunit_residue by simp
  qed
  show ?thesis
  proof -
    have first:
      "reverse_laurent_interval_projection_piece width modulus
          (lo, hi) = ((?shift mod modulus) * (?base mod modulus)) mod modulus"
      by (rule piece)
    also have second:
      "... = (?shift * decimal_repunit (hi - lo + 1)) mod modulus"
      by (rule product_mod)
    also have third:
      "... = reverse_laurent_interval_value width (lo, hi) mod modulus"
      by (rule sym[OF interval])
    finally show ?thesis .
  qed
qed

lemma reverse_laurent_interval_projection_fold_exact:
  assumes modulus: "0 < modulus"
  shows "reverse_laurent_interval_projection_fold width modulus intervals =
    reverse_laurent_interval_sum width intervals mod modulus"
  using modulus
proof (induction intervals)
  case Nil
  then show ?case by simp
next
  case (Cons interval intervals)
  obtain lo hi where interval: "interval = (lo, hi)"
    by (cases interval) auto
  have piece:
    "reverse_laurent_interval_projection_piece width modulus interval =
      reverse_laurent_interval_value width interval mod modulus"
    using reverse_laurent_interval_projection_piece_exact[where width=width
        and modulus=modulus and lo=lo and hi=hi] modulus
    by (simp add: interval)
  have piece_residue:
    "reverse_laurent_interval_projection_piece width modulus interval mod
        modulus = reverse_laurent_interval_value width interval mod modulus"
    using piece by simp
  have tail_residue:
    "reverse_laurent_interval_projection_fold width modulus intervals mod
        modulus = reverse_laurent_interval_sum width intervals mod modulus"
    using Cons.IH[OF Cons.prems] by simp
  have combined:
    "(reverse_laurent_interval_projection_piece width modulus interval +
        reverse_laurent_interval_projection_fold width modulus intervals)
        mod modulus =
      (reverse_laurent_interval_value width interval +
        reverse_laurent_interval_sum width intervals) mod modulus"
    by (rule mod_add_cong[OF piece_residue tail_residue])
  show ?case using combined interval by simp
qed

theorem reverse_laurent_switch_interval_projection_exact:
  assumes modulus: "1 < modulus"
  shows "reverse_laurent_switch_interval_projection
      (punctured_run_width runs) modulus 1 False
      (reverse_laurent_switches runs) =
    reverse_laurent_internal_carry_mask (punctured_expand_runs runs) mod modulus"
proof -
  let ?trace = "reverse_laurent_carry_trace False runs"
  let ?switches = "reverse_laurent_switches runs"
  have modulus_positive: "0 < modulus" using modulus by arith
  have width:
    "punctured_run_width runs = length ?trace"
    using reverse_laurent_carry_trace_length[of False runs] by simp
  have switch_trace:
    "?switches = reverse_laurent_switch_trace 0 False ?trace"
    by (rule reverse_laurent_switches_are_canonical_carry_trace)
  have replay:
    "reverse_laurent_replay_switch_word (length ?trace) False
        (reverse_laurent_switch_trace 0 False ?trace) = ?trace"
    by (rule reverse_laurent_replay_switch_trace_exact)
  have interval_switch_mask:
    "reverse_laurent_switch_interval_sum (length ?trace) 1 False
        (reverse_laurent_switch_trace 0 False ?trace) =
      reverse_laurent_switch_internal_mask (length ?trace)
        (reverse_laurent_switch_trace 0 False ?trace)"
    using reverse_laurent_switch_interval_trace_exact[of ?trace False]
      replay
    by (simp add: reverse_laurent_switch_internal_mask_def)
  have source_mask:
    "reverse_laurent_switch_internal_mask (punctured_run_width runs)
        ?switches =
      reverse_laurent_internal_carry_mask (punctured_expand_runs runs)"
    by (rule reverse_laurent_switch_fold_recovers_internal_mask)
  have interval_mask:
    "reverse_laurent_switch_interval_sum (punctured_run_width runs) 1 False
        ?switches =
      reverse_laurent_internal_carry_mask (punctured_expand_runs runs)"
    using interval_switch_mask source_mask width switch_trace by simp
  have projection:
    "reverse_laurent_interval_projection_fold (punctured_run_width runs)
        modulus
        (reverse_laurent_true_carry_intervals (punctured_run_width runs)
          1 False ?switches) =
      reverse_laurent_switch_interval_sum (punctured_run_width runs) 1 False
        ?switches mod modulus"
    using reverse_laurent_interval_projection_fold_exact[where
        width="punctured_run_width runs" and modulus=modulus and
        intervals="reverse_laurent_true_carry_intervals
          (punctured_run_width runs) 1 False ?switches"]
      modulus_positive
    by (simp add: reverse_laurent_switch_interval_sum_def
        reverse_laurent_switch_interval_projection_def)
  show ?thesis using interval_mask projection
    by (simp add: reverse_laurent_switch_interval_projection_def)
qed

ML \<open>
  val checked = @{thms reverse_laurent_switch_interval_sum_shift
    reverse_laurent_switch_trace_within_width
    reverse_laurent_switch_interval_trace_exact
    reverse_laurent_interval_projection_piece_exact
    reverse_laurent_interval_projection_fold_exact
    reverse_laurent_switch_interval_projection_exact};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Reverse Laurent modular projection depends on an oracle";
\<close>

end
