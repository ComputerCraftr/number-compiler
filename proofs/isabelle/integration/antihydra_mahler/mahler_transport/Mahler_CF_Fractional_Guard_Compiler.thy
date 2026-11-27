theory Mahler_CF_Fractional_Guard_Compiler
  imports Mahler_CF_Ordered_Row_Blocks "HOL-Number_Theory.Modular_Inverse"
begin

text \<open>Only the three physically issued batch forms are admitted. Their
word, affine multiplier, correction and physical duration are kept together.\<close>

datatype mahler_cf_guard_batch = Zero_Run nat | Odd_Single | Odd_Then_Zero

fun mahler_cf_batch_word :: "mahler_cf_guard_batch \<Rightarrow> nat list" where
  "mahler_cf_batch_word (Zero_Run q) = replicate q 0"
| "mahler_cf_batch_word Odd_Single = [1]"
| "mahler_cf_batch_word Odd_Then_Zero = [1,0]"

fun mahler_cf_batch_gain :: "mahler_cf_guard_batch \<Rightarrow> real" where
  "mahler_cf_batch_gain (Zero_Run q) = 3^q"
| "mahler_cf_batch_gain Odd_Single = 3"
| "mahler_cf_batch_gain Odd_Then_Zero = 9"

fun mahler_cf_batch_modulus :: "mahler_cf_guard_batch \<Rightarrow> real" where
  "mahler_cf_batch_modulus (Zero_Run q) = 2^q"
| "mahler_cf_batch_modulus Odd_Single = 2"
| "mahler_cf_batch_modulus Odd_Then_Zero = 4"

fun mahler_cf_batch_correction :: "mahler_cf_guard_batch \<Rightarrow> real" where
  "mahler_cf_batch_correction (Zero_Run q) = 0"
| "mahler_cf_batch_correction Odd_Single = 1"
| "mahler_cf_batch_correction Odd_Then_Zero = 3"

lemma mahler_cf_batch_positive:
  "0 < mahler_cf_batch_gain batch" "0 < mahler_cf_batch_modulus batch"
  by (cases batch; simp_all)+

lemma mahler_cf_batch_apply:
  "mahler_cf_physical_apply (mahler_cf_batch_word batch) x =
    mahler_cf_lean_fraction (mahler_cf_batch_gain batch)
      (mahler_cf_batch_modulus batch) (mahler_cf_batch_correction batch) x"
  by (cases batch) (simp_all add: mahler_cf_apply_zero_row mahler_cf_lean_fraction_def
      power_divide field_simps algebra_simps)

lemma mahler_cf_batch_safe:
  assumes inlet: "mahler_cf_safe_fraction x"
    and terminal: "mahler_cf_safe_fraction (mahler_cf_physical_apply (mahler_cf_batch_word batch) x)"
  shows "mahler_cf_physical_safe (mahler_cf_batch_word batch) x"
proof (cases batch)
  case (Zero_Run q)
  then show ?thesis using inlet terminal
    by (simp only: mahler_cf_batch_word.simps mahler_cf_safe_zero_row mahler_cf_apply_zero_row)
next
  case Odd_Single
  then show ?thesis using inlet terminal
    by (simp add: mahler_cf_safe_fraction_def)
next
  case Odd_Then_Zero
  then show ?thesis using inlet terminal
    by (simp only: mahler_cf_batch_word.simps mahler_cf_safe_odd_even_batch
        mahler_cf_physical_apply.simps of_nat_0 of_nat_1; simp add: field_simps)
qed

record mahler_cf_compiled_guard =
  cf_gain :: real
  cf_modulus :: real
  cf_innovation :: real
  cf_lower :: real
  cf_upper :: real
  cf_word :: "nat list"
  cf_ticks :: nat

definition mahler_cf_guard_initial :: mahler_cf_compiled_guard where
  "mahler_cf_guard_initial = \<lparr>cf_gain=1, cf_modulus=1, cf_innovation=0,
    cf_lower=0, cf_upper=1/2, cf_word=[], cf_ticks=0\<rparr>"

definition mahler_cf_guard_step ::
  "mahler_cf_compiled_guard \<Rightarrow> mahler_cf_guard_batch \<Rightarrow> mahler_cf_compiled_guard" where
  "mahler_cf_guard_step st batch =
    (let a = mahler_cf_batch_gain batch; m = mahler_cf_batch_modulus batch;
         b = mahler_cf_batch_correction batch;
         g = a * cf_gain st; z = m * cf_modulus st;
         j = a * cf_innovation st + cf_modulus st * b
     in \<lparr>cf_gain=g, cf_modulus=z, cf_innovation=j,
        cf_lower=max (cf_lower st) (j/g),
        cf_upper=min (cf_upper st) ((2*j+z)/(2*g)),
        cf_word=cf_word st @ mahler_cf_batch_word batch,
        cf_ticks=cf_ticks st + length (mahler_cf_batch_word batch)\<rparr>)"

definition mahler_cf_guard_compile :: "mahler_cf_guard_batch list \<Rightarrow> mahler_cf_compiled_guard" where
  "mahler_cf_guard_compile batches = foldl mahler_cf_guard_step mahler_cf_guard_initial batches"

definition mahler_cf_guard_invariant :: "mahler_cf_compiled_guard \<Rightarrow> bool" where
  "mahler_cf_guard_invariant st \<longleftrightarrow>
    0 < cf_gain st \<and> 0 < cf_modulus st \<and>
    cf_ticks st = length (cf_word st) \<and>
    (\<forall>x. mahler_cf_physical_apply (cf_word st) x =
      mahler_cf_lean_fraction (cf_gain st) (cf_modulus st) (cf_innovation st) x) \<and>
    (\<forall>x. cf_lower st \<le> x \<and> x < cf_upper st \<longrightarrow>
      mahler_cf_physical_safe (cf_word st) x)"

lemma mahler_cf_guard_initial_invariant:
  "mahler_cf_guard_invariant mahler_cf_guard_initial"
  by (simp add: mahler_cf_guard_invariant_def mahler_cf_guard_initial_def
      mahler_cf_lean_fraction_def mahler_cf_safe_fraction_def)

lemma mahler_cf_physical_safe_endpoint:
  "mahler_cf_physical_safe word x \<Longrightarrow>
    mahler_cf_safe_fraction (mahler_cf_physical_apply word x)"
  by (induction word arbitrary: x) auto

lemma mahler_cf_guard_step_invariant:
  assumes inv: "mahler_cf_guard_invariant st"
  shows "mahler_cf_guard_invariant (mahler_cf_guard_step st batch)"
proof -
  have gain: "0 < cf_gain st" and modulus: "0 < cf_modulus st"
    and ticks: "cf_ticks st = length (cf_word st)"
    and action: "\<And>x. mahler_cf_physical_apply (cf_word st) x =
      mahler_cf_lean_fraction (cf_gain st) (cf_modulus st) (cf_innovation st) x"
    and prior: "\<And>x. cf_lower st \<le> x \<Longrightarrow> x < cf_upper st \<Longrightarrow>
      mahler_cf_physical_safe (cf_word st) x"
    using inv by (auto simp: mahler_cf_guard_invariant_def)
  have ag: "0 < mahler_cf_batch_gain batch" and am: "0 < mahler_cf_batch_modulus batch"
    by (rule mahler_cf_batch_positive)+
  have new_gain: "0 < cf_gain (mahler_cf_guard_step st batch)"
    using gain ag by (simp add: mahler_cf_guard_step_def Let_def)
  have new_modulus: "0 < cf_modulus (mahler_cf_guard_step st batch)"
    using modulus am by (simp add: mahler_cf_guard_step_def Let_def)
  have new_action: "\<And>x. mahler_cf_physical_apply (cf_word (mahler_cf_guard_step st batch)) x =
      mahler_cf_lean_fraction (cf_gain (mahler_cf_guard_step st batch))
        (cf_modulus (mahler_cf_guard_step st batch)) (cf_innovation (mahler_cf_guard_step st batch)) x"
    using mahler_cf_lean_action_composition[of "cf_modulus st" "mahler_cf_batch_modulus batch"]
      gain modulus ag am
    by (simp add: mahler_cf_guard_step_def Let_def mahler_cf_physical_apply_append
        action mahler_cf_batch_apply mahler_cf_lean_fraction_def field_simps algebra_simps)
  have new_safe: "\<And>x. cf_lower (mahler_cf_guard_step st batch) \<le> x \<Longrightarrow>
      x < cf_upper (mahler_cf_guard_step st batch) \<Longrightarrow>
      mahler_cf_physical_safe (cf_word (mahler_cf_guard_step st batch)) x"
  proof -
    fix x assume lo: "cf_lower (mahler_cf_guard_step st batch) \<le> x"
      and hi: "x < cf_upper (mahler_cf_guard_step st batch)"
    have nested: "cf_lower st \<le> cf_lower (mahler_cf_guard_step st batch)"
      "cf_upper (mahler_cf_guard_step st batch) \<le> cf_upper st"
      by (simp_all add: mahler_cf_guard_step_def Let_def)
    have lower: "cf_innovation (mahler_cf_guard_step st batch) /
        cf_gain (mahler_cf_guard_step st batch) \<le> x"
      using lo by (simp add: mahler_cf_guard_step_def Let_def)
    have upper: "x < (2 * cf_innovation (mahler_cf_guard_step st batch) +
        cf_modulus (mahler_cf_guard_step st batch)) /
        (2 * cf_gain (mahler_cf_guard_step st batch))"
      using hi by (simp add: mahler_cf_guard_step_def Let_def)
    have left: "0 \<le> cf_gain (mahler_cf_guard_step st batch)*x -
        cf_innovation (mahler_cf_guard_step st batch)"
      using lower new_gain by (simp add: divide_le_eq mult.commute; linarith)
    have right: "2 * (cf_gain (mahler_cf_guard_step st batch)*x -
        cf_innovation (mahler_cf_guard_step st batch)) <
        cf_modulus (mahler_cf_guard_step st batch)"
      using upper new_gain by (simp add: less_divide_eq mult.commute; linarith)
    have safe_action: "mahler_cf_safe_fraction (mahler_cf_lean_fraction
        (cf_gain (mahler_cf_guard_step st batch)) (cf_modulus (mahler_cf_guard_step st batch))
        (cf_innovation (mahler_cf_guard_step st batch)) x)"
      using left right new_modulus
      by (simp add: mahler_cf_safe_fraction_def mahler_cf_lean_fraction_def divide_less_eq; linarith)
    have terminal: "mahler_cf_safe_fraction
        (mahler_cf_physical_apply (mahler_cf_batch_word batch) (mahler_cf_physical_apply (cf_word st) x))"
      using safe_action new_action[of x]
      by (simp add: mahler_cf_guard_step_def Let_def mahler_cf_physical_apply_append)
    have prior_x: "mahler_cf_physical_safe (cf_word st) x"
      by (rule prior) (use lo hi nested in auto)
    have prior_end: "mahler_cf_safe_fraction (mahler_cf_physical_apply (cf_word st) x)"
      by (rule mahler_cf_physical_safe_endpoint[OF prior_x])
    have batch_safe: "mahler_cf_physical_safe (mahler_cf_batch_word batch)
        (mahler_cf_physical_apply (cf_word st) x)"
      by (rule mahler_cf_batch_safe[OF prior_end terminal])
    show "mahler_cf_physical_safe (cf_word (mahler_cf_guard_step st batch)) x"
      using prior_x batch_safe
      by (simp add: mahler_cf_guard_step_def Let_def mahler_cf_physical_safe_append)
  qed
  show ?thesis using new_gain new_modulus ticks new_action new_safe
    by (auto simp: mahler_cf_guard_invariant_def mahler_cf_guard_step_def Let_def)
qed

definition mahler_cf_guard_compose ::
  "mahler_cf_compiled_guard \<Rightarrow> mahler_cf_compiled_guard \<Rightarrow> mahler_cf_compiled_guard" where
  "mahler_cf_guard_compose first second =
    \<lparr>cf_gain = cf_gain second * cf_gain first,
     cf_modulus = cf_modulus first * cf_modulus second,
     cf_innovation = cf_gain second * cf_innovation first +
       cf_modulus first * cf_innovation second,
     cf_lower = max (cf_lower first)
       ((cf_innovation first + cf_modulus first * cf_lower second) / cf_gain first),
     cf_upper = min (cf_upper first)
       ((cf_innovation first + cf_modulus first * cf_upper second) / cf_gain first),
     cf_word = cf_word first @ cf_word second,
     cf_ticks = cf_ticks first + cf_ticks second\<rparr>"

lemma mahler_cf_guard_compose_invariant:
  assumes first: "mahler_cf_guard_invariant first"
      and second: "mahler_cf_guard_invariant second"
  shows "mahler_cf_guard_invariant (mahler_cf_guard_compose first second)"
proof -
  have fg: "0 < cf_gain first" and fm: "0 < cf_modulus first"
    and sg: "0 < cf_gain second" and sm: "0 < cf_modulus second"
    using first second by (auto simp: mahler_cf_guard_invariant_def)
  have fact: "\<And>x. mahler_cf_physical_apply (cf_word first) x =
      mahler_cf_lean_fraction (cf_gain first) (cf_modulus first) (cf_innovation first) x"
    and sact: "\<And>x. mahler_cf_physical_apply (cf_word second) x =
      mahler_cf_lean_fraction (cf_gain second) (cf_modulus second) (cf_innovation second) x"
    and fsafe: "\<And>x. cf_lower first \<le> x \<Longrightarrow> x < cf_upper first \<Longrightarrow>
      mahler_cf_physical_safe (cf_word first) x"
    and ssafe: "\<And>x. cf_lower second \<le> x \<Longrightarrow> x < cf_upper second \<Longrightarrow>
      mahler_cf_physical_safe (cf_word second) x"
    using first second by (auto simp: mahler_cf_guard_invariant_def)
  have action: "\<And>x. mahler_cf_physical_apply (cf_word (mahler_cf_guard_compose first second)) x =
      mahler_cf_lean_fraction (cf_gain (mahler_cf_guard_compose first second))
        (cf_modulus (mahler_cf_guard_compose first second))
        (cf_innovation (mahler_cf_guard_compose first second)) x"
    using mahler_cf_lean_action_composition[of "cf_modulus first" "cf_modulus second"] fm sm
    by (simp add: mahler_cf_guard_compose_def mahler_cf_physical_apply_append fact sact)
  have safe: "\<And>x. cf_lower (mahler_cf_guard_compose first second) \<le> x \<Longrightarrow>
      x < cf_upper (mahler_cf_guard_compose first second) \<Longrightarrow>
      mahler_cf_physical_safe (cf_word (mahler_cf_guard_compose first second)) x"
  proof -
    fix x assume lower: "cf_lower (mahler_cf_guard_compose first second) \<le> x"
      and upper: "x < cf_upper (mahler_cf_guard_compose first second)"
    have first_safe: "mahler_cf_physical_safe (cf_word first) x"
      by (rule fsafe) (use lower upper in \<open>auto simp: mahler_cf_guard_compose_def\<close>)
    have raw_lo: "(cf_innovation first + cf_modulus first * cf_lower second) /
        cf_gain first \<le> x"
      using lower by (simp add: mahler_cf_guard_compose_def)
    have lo_scaled: "cf_innovation first + cf_modulus first * cf_lower second \<le>
        cf_gain first * x"
      using raw_lo fg by (simp add: divide_le_eq mult.commute)
    have lo_product: "cf_modulus first * cf_lower second \<le>
        cf_gain first * x - cf_innovation first"
      using lo_scaled by linarith
    have lo: "cf_lower second \<le> mahler_cf_physical_apply (cf_word first) x"
      using lo_product fm by (simp add: fact mahler_cf_lean_fraction_def le_divide_eq mult.commute)
    have raw_hi: "x < (cf_innovation first + cf_modulus first * cf_upper second) /
        cf_gain first"
      using upper by (simp add: mahler_cf_guard_compose_def)
    have hi_scaled: "cf_gain first * x < cf_innovation first + cf_modulus first * cf_upper second"
      using raw_hi fg by (simp add: less_divide_eq mult.commute)
    have hi_product: "cf_gain first * x - cf_innovation first <
        cf_modulus first * cf_upper second"
      using hi_scaled by linarith
    have hi: "mahler_cf_physical_apply (cf_word first) x < cf_upper second"
      using hi_product fm by (simp add: fact mahler_cf_lean_fraction_def divide_less_eq mult.commute)
    show "mahler_cf_physical_safe (cf_word (mahler_cf_guard_compose first second)) x"
      using first_safe ssafe[OF lo hi]
      by (simp add: mahler_cf_guard_compose_def mahler_cf_physical_safe_append)
  qed
  show ?thesis using first second fg fm sg sm action safe
    by (auto simp: mahler_cf_guard_invariant_def mahler_cf_guard_compose_def)
qed

lemma mahler_cf_guard_fold_invariant:
  assumes "mahler_cf_guard_invariant st"
  shows "mahler_cf_guard_invariant (foldl mahler_cf_guard_step st batches)"
  using assms by (induction batches arbitrary: st) (auto intro: mahler_cf_guard_step_invariant)

theorem mahler_cf_guard_compiler_correct:
  "mahler_cf_guard_invariant (mahler_cf_guard_compile batches)"
  unfolding mahler_cf_guard_compile_def
  by (rule mahler_cf_guard_fold_invariant[OF mahler_cf_guard_initial_invariant])


lemma mahler_cf_guard_fold_word:
  "cf_word (foldl mahler_cf_guard_step st batches) =
    cf_word st @ concat (map mahler_cf_batch_word batches)"
  by (induction batches arbitrary: st)
    (simp_all add: mahler_cf_guard_step_def Let_def append_assoc)

lemma mahler_cf_guard_compile_word:
  "cf_word (mahler_cf_guard_compile (pre @ post)) =
    cf_word (mahler_cf_guard_compile pre) @ concat (map mahler_cf_batch_word post)"
  by (simp add: mahler_cf_guard_compile_def foldl_append mahler_cf_guard_fold_word)

theorem mahler_cf_compiled_stall_not_guarded:
  fixes pre post :: "mahler_cf_guard_batch list" and st finished :: mahler_cf_compiled_guard
    and F :: "real \<Rightarrow> real"
  defines "st \<equiv> mahler_cf_guard_compile pre"
    and "finished \<equiv> mahler_cf_guard_compile (pre @ post)"
    and "F \<equiv> (\<lambda>x. (cf_gain st*x - cf_innovation st)/cf_modulus st)"
  assumes prefix: "mahler_cf_prefix digits = (q,r,p,s)"
    and stalled: "\<not> (0 \<le> F (mahler_cf_low q r p s) \<and>
      F (mahler_cf_high q r p s) \<le> 1/2 \<and>
      (F (mahler_cf_high q r p s) \<le> 1/3 \<or>
       1/3 \<le> F (mahler_cf_low q r p s)))"
    and later: "concat (map mahler_cf_batch_word post) \<noteq> []"
  shows "\<not> mahler_cf_guard_contains_prefix (cf_lower finished) (cf_upper finished) digits"
proof -
  have st: "mahler_cf_guard_invariant st" and fin: "mahler_cf_guard_invariant finished"
    by (simp_all add: st_def finished_def mahler_cf_guard_compiler_correct)
  have gain: "0 < cf_gain st" and modulus: "0 < cf_modulus st"
    and action: "\<And>x. mahler_cf_physical_apply (cf_word st) x =
      mahler_cf_lean_fraction (cf_gain st) (cf_modulus st) (cf_innovation st) x"
    using st by (auto simp: mahler_cf_guard_invariant_def)
  have safe: "\<And>x. cf_lower finished \<le> x \<Longrightarrow> x < cf_upper finished \<Longrightarrow>
      mahler_cf_physical_safe (cf_word st @ concat (map mahler_cf_batch_word post)) x"
    using fin by (auto simp: mahler_cf_guard_invariant_def finished_def st_def mahler_cf_guard_compile_word)
  show ?thesis
    using mahler_cf_stalled_prefix_from_safe_continuation[
      where gain="cf_gain st" and modulus="cf_modulus st" and innovation="cf_innovation st"
        and pre="cf_word st" and suffix="concat (map mahler_cf_batch_word post)",
      OF gain modulus prefix] stalled later safe action by (simp add: F_def)
qed

lemma mahler_cf_compiled_later_ticks:
  assumes later: "cf_ticks (mahler_cf_guard_compile pre) <
    cf_ticks (mahler_cf_guard_compile (pre @ post))"
  shows "concat (map mahler_cf_batch_word post) \<noteq> []"
proof
  assume empty: "concat (map mahler_cf_batch_word post) = []"
  have a: "cf_ticks (mahler_cf_guard_compile pre) =
      length (cf_word (mahler_cf_guard_compile pre))"
    using mahler_cf_guard_compiler_correct[of pre] by (simp add: mahler_cf_guard_invariant_def)
  have b: "cf_ticks (mahler_cf_guard_compile (pre @ post)) =
      length (cf_word (mahler_cf_guard_compile (pre @ post)))"
    using mahler_cf_guard_compiler_correct[of "pre @ post"] by (simp add: mahler_cf_guard_invariant_def)
  show False using later a b empty mahler_cf_guard_compile_word[of pre post] by simp
qed

lemma mahler_cf_guard_scaled_update:
  fixes gain scale low high innovation modulus :: real
  assumes "0 < gain" "0 < scale"
  shows "max (low / gain) (innovation / (scale*gain)) =
      max (scale*low) innovation / (scale*gain)"
    "min (high / (2*gain)) ((2*innovation+modulus)/(2*(scale*gain))) =
      min (scale*high) (2*innovation+modulus) / (2*(scale*gain))"
  using mahler_cf_lean_scaled_guard_refinement[OF assms] .

lemma mahler_cf_zero_endpoint_cancel:
  fixes n d k :: nat
  assumes "0 < k"
  shows "2*(3^k*n) \<le> d*2^k \<longleftrightarrow>
    3^k*n \<le> d*2^(k-1)"
  using assms by (cases k) (simp_all add: power_Suc algebra_simps)

lemma mahler_cf_zero_endpoint_first:
  fixes n d :: nat
  shows "2*(3*n) \<le> d*2 \<longleftrightarrow> 3*n \<le> d"
    "2*(9*n) \<le> d*4 \<longleftrightarrow> 9*n \<le> 2*d"
  by simp_all

text \<open>The chart stores scaled rational guard endpoints. Its word is a proof
witness, while the executable retains only the action and guard values.\<close>

definition mahler_cf_chart_edge :: "bool \<Rightarrow> mahler_cf_guard_batch" where
  "mahler_cf_chart_edge is_odd = (if is_odd then Odd_Single else Zero_Run 1)"

lemma mahler_cf_chart_edge_scaled:
  fixes gain modulus innovation low high :: real and is_odd :: bool
  assumes gain: "0 < gain"
    and state: "cf_gain st = gain" "cf_modulus st = modulus"
      "cf_innovation st = innovation" "cf_lower st = low / gain"
      "cf_upper st = high / (2*gain)"
  defines "new_innovation \<equiv> 3*innovation+(if is_odd then modulus else 0)"
  shows "cf_gain (mahler_cf_guard_step st (mahler_cf_chart_edge is_odd)) = 3*gain"
    "cf_modulus (mahler_cf_guard_step st (mahler_cf_chart_edge is_odd)) = 2*modulus"
    "cf_innovation (mahler_cf_guard_step st (mahler_cf_chart_edge is_odd)) = new_innovation"
    "cf_lower (mahler_cf_guard_step st (mahler_cf_chart_edge is_odd)) =
      max (3*low) new_innovation / (3*gain)"
    "cf_upper (mahler_cf_guard_step st (mahler_cf_chart_edge is_odd)) =
      min (3*high) (2*new_innovation+2*modulus) / (2*(3*gain))"
    "cf_ticks (mahler_cf_guard_step st (mahler_cf_chart_edge is_odd)) = Suc (cf_ticks st)"
proof -
  have low_bound: "max (low / gain) (new_innovation / (3*gain)) =
      max (3*low) new_innovation / (3*gain)"
    using mahler_cf_guard_scaled_update(1)[where gain=gain and scale=3 and low=low
        and innovation=new_innovation] gain by simp
  have high_bound: "min (high / (2*gain)) ((2*new_innovation+2*modulus)/(2*(3*gain))) =
      min (3*high) (2*new_innovation+2*modulus) / (2*(3*gain))"
    using mahler_cf_guard_scaled_update(2)[where gain=gain and scale=3 and high=high
        and innovation=new_innovation and modulus="2*modulus"] gain by simp
  show "cf_gain (mahler_cf_guard_step st (mahler_cf_chart_edge is_odd)) = 3*gain"
    "cf_modulus (mahler_cf_guard_step st (mahler_cf_chart_edge is_odd)) = 2*modulus"
    "cf_innovation (mahler_cf_guard_step st (mahler_cf_chart_edge is_odd)) = new_innovation"
    "cf_lower (mahler_cf_guard_step st (mahler_cf_chart_edge is_odd)) =
      max (3*low) new_innovation / (3*gain)"
    "cf_upper (mahler_cf_guard_step st (mahler_cf_chart_edge is_odd)) =
      min (3*high) (2*new_innovation+2*modulus) / (2*(3*gain))"
    "cf_ticks (mahler_cf_guard_step st (mahler_cf_chart_edge is_odd)) = Suc (cf_ticks st)"
    using state low_bound high_bound
    by (cases is_odd; simp_all add: mahler_cf_guard_step_def mahler_cf_chart_edge_def
        Let_def new_innovation_def algebra_simps)+
qed

lemma mahler_cf_chart_complete_word:
  "mahler_cf_guard_invariant
    (mahler_cf_guard_compile (map mahler_cf_chart_edge choices))"
  by (rule mahler_cf_guard_compiler_correct)

lemma mahler_cf_chart_interval_sound:
  assumes valid: "mahler_cf_guard_invariant st"
    and lower: "cf_lower st \<le> left" and upper: "right \<le> cf_upper st"
  shows "\<forall>x. left \<le> x \<and> x < right \<longrightarrow>
      mahler_cf_physical_safe (cf_word st) x"
  using valid lower upper by (auto simp: mahler_cf_guard_invariant_def)

lemma mahler_cf_chart_interval_upper_equal:
  assumes valid: "mahler_cf_guard_invariant st" and lower: "cf_lower st \<le> left"
  shows "\<forall>x. left \<le> x \<and> x < cf_upper st \<longrightarrow>
      mahler_cf_physical_safe (cf_word st) x"
  using mahler_cf_chart_interval_sound[OF valid lower order_refl] .

lemma mahler_cf_chart_rejected_width:
  fixes gain low high left right :: real
  assumes gain: "0 < gain" and bound: "2*low \<ge> high" and span: "left < right"
  shows "\<not> (low / gain \<le> left \<and> right \<le> high / (2*gain))"
proof -
  have upper: "high / (2*gain) \<le> (2*low) / (2*gain)"
    by (rule divide_right_mono) (use gain bound in auto)
  have "high / (2*gain) \<le> low/gain" using upper gain by simp
  then show ?thesis using span by linarith
qed

lemma mahler_cf_chart_heads_unique:
  assumes first: "mahler_cf_physical_safe (b # bs) x"
      and second: "mahler_cf_physical_safe (c # cs) x"
  shows "b = c"
proof -
  have bounds: "b \<le> 1" "c \<le> 1"
    using first second by auto
  have bits: "(b=0 \<or> b=1) \<and> (c=0 \<or> c=1)"
    using bounds by arith
  have a: "mahler_cf_safe_fraction ((3*x-of_nat b)/2)"
    using first mahler_cf_physical_safe_inlet by auto
  have d: "mahler_cf_safe_fraction ((3*x-of_nat c)/2)"
    using second mahler_cf_physical_safe_inlet by auto
  show ?thesis using bits a d
    by (auto simp: mahler_cf_safe_fraction_def; linarith)
qed

lemma mahler_cf_chart_safe_words_unique:
  assumes "mahler_cf_physical_safe first x" "mahler_cf_physical_safe second x"
      "length first = length second"
  shows "first = second"
  using assms
proof (induction first arbitrary: second x)
  case Nil then show ?case by simp
next
  case (Cons b bs)
  then obtain c cs where second: "second = c#cs" by (cases second) auto
  have "b=c" using Cons.prems(1,2) second by (auto intro: mahler_cf_chart_heads_unique)
  moreover have "bs=cs" using Cons.IH Cons.prems second calculation by auto
  ultimately show ?case using second by simp
qed

lemma mahler_cf_chart_edge_exact:
  fixes is_odd :: bool
  assumes inv: "mahler_cf_guard_invariant st"
    and exact: "\<And>x. mahler_cf_physical_safe (cf_word st) x \<longleftrightarrow>
      cf_lower st \<le> x \<and> x < cf_upper st"
  shows "mahler_cf_physical_safe (cf_word (mahler_cf_guard_step st (mahler_cf_chart_edge is_odd))) x
    \<longleftrightarrow> cf_lower (mahler_cf_guard_step st (mahler_cf_chart_edge is_odd)) \<le> x \<and>
      x < cf_upper (mahler_cf_guard_step st (mahler_cf_chart_edge is_odd))"
proof
  assume safe: "mahler_cf_physical_safe (cf_word (mahler_cf_guard_step st (mahler_cf_chart_edge is_odd))) x"
  let ?next = "mahler_cf_guard_step st (mahler_cf_chart_edge is_odd)"
  have gain: "0 < cf_gain ?next" and modulus: "0 < cf_modulus ?next"
    using mahler_cf_guard_step_invariant[OF inv, of "mahler_cf_chart_edge is_odd"]
    by (auto simp: mahler_cf_guard_invariant_def)
  have before: "mahler_cf_physical_safe (cf_word st) x"
    using safe by (simp add: mahler_cf_guard_step_def mahler_cf_physical_safe_append Let_def)
  have old_guard: "cf_lower st \<le> x" "x < cf_upper st" using exact before by auto
  have endpoint: "mahler_cf_safe_fraction (mahler_cf_physical_apply (cf_word ?next) x)"
    by (rule mahler_cf_physical_safe_endpoint[OF safe])
  have action: "mahler_cf_physical_apply (cf_word ?next) x = mahler_cf_lean_fraction
      (cf_gain ?next) (cf_modulus ?next) (cf_innovation ?next) x"
    using mahler_cf_guard_step_invariant[OF inv, of "mahler_cf_chart_edge is_odd"]
    by (simp add: mahler_cf_guard_invariant_def)
  have terminal: "mahler_cf_safe_fraction (mahler_cf_lean_fraction
      (cf_gain ?next) (cf_modulus ?next) (cf_innovation ?next) x)"
    using endpoint action by simp
  have num_lo: "0 \<le> cf_gain ?next * x - cf_innovation ?next"
    using terminal modulus by (simp add: mahler_cf_safe_fraction_def mahler_cf_lean_fraction_def le_divide_eq)
  have lo_scaled: "cf_innovation ?next \<le> cf_gain ?next*x" using num_lo by linarith
  have lo: "cf_innovation ?next / cf_gain ?next \<le> x"
    using lo_scaled gain by (simp add: divide_le_eq mult.commute)
  have num_hi: "(cf_gain ?next * x - cf_innovation ?next) / cf_modulus ?next < 1/2"
    using terminal by (simp add: mahler_cf_safe_fraction_def mahler_cf_lean_fraction_def)
  have hi_scaled: "2*cf_gain ?next*x < 2*cf_innovation ?next+cf_modulus ?next"
    using num_hi modulus by (simp add: divide_less_eq; linarith)
  have hi: "x < (2*cf_innovation ?next + cf_modulus ?next) / (2*cf_gain ?next)"
    using hi_scaled gain by (simp add: less_divide_eq mult.assoc mult.commute mult.left_commute)
  show "cf_lower ?next \<le> x \<and> x < cf_upper ?next"
    using old_guard lo hi by (auto simp: mahler_cf_guard_step_def Let_def)
next
  assume bound: "cf_lower (mahler_cf_guard_step st (mahler_cf_chart_edge is_odd)) \<le> x \<and>
      x < cf_upper (mahler_cf_guard_step st (mahler_cf_chart_edge is_odd))"
  show "mahler_cf_physical_safe (cf_word (mahler_cf_guard_step st (mahler_cf_chart_edge is_odd))) x"
    using mahler_cf_guard_step_invariant[OF inv, of "mahler_cf_chart_edge is_odd"] bound
    by (auto simp: mahler_cf_guard_invariant_def)
qed

lemma mahler_cf_chart_exact_word:
  fixes choices :: "bool list" and state :: mahler_cf_compiled_guard
  defines "state \<equiv> mahler_cf_guard_compile (map mahler_cf_chart_edge choices)"
  shows "mahler_cf_physical_safe (cf_word state) x \<longleftrightarrow>
      cf_lower state \<le> x \<and> x < cf_upper state"
proof -
  have exact: "\<And>st. mahler_cf_guard_invariant st \<Longrightarrow>
      (\<And>x. mahler_cf_physical_safe (cf_word st) x \<longleftrightarrow>
        cf_lower st \<le> x \<and> x < cf_upper st) \<Longrightarrow>
      mahler_cf_physical_safe (cf_word (foldl mahler_cf_guard_step st
          (map mahler_cf_chart_edge choices))) x \<longleftrightarrow>
        cf_lower (foldl mahler_cf_guard_step st (map mahler_cf_chart_edge choices)) \<le> x \<and>
        x < cf_upper (foldl mahler_cf_guard_step st (map mahler_cf_chart_edge choices))"
  proof (induction choices arbitrary: x)
    case Nil then show ?case by simp
  next
    case (Cons choice rest)
    have valid: "mahler_cf_guard_invariant (mahler_cf_guard_step st (mahler_cf_chart_edge choice))"
      by (rule mahler_cf_guard_step_invariant[OF Cons.prems(1)])
    have result: "\<And>x. mahler_cf_physical_safe
        (cf_word (mahler_cf_guard_step st (mahler_cf_chart_edge choice))) x \<longleftrightarrow>
        cf_lower (mahler_cf_guard_step st (mahler_cf_chart_edge choice)) \<le> x \<and>
        x < cf_upper (mahler_cf_guard_step st (mahler_cf_chart_edge choice))"
      by (rule mahler_cf_chart_edge_exact[OF Cons.prems])
    show ?case using Cons.IH[OF valid result] by simp
  qed
  show ?thesis unfolding state_def mahler_cf_guard_compile_def
    by (rule exact[OF mahler_cf_guard_initial_invariant])
       (simp add: mahler_cf_guard_initial_def mahler_cf_safe_fraction_def)
qed

lemma mahler_cf_chart_interval_exact:
  fixes choices :: "bool list" and state :: mahler_cf_compiled_guard
  defines "state \<equiv> mahler_cf_guard_compile (map mahler_cf_chart_edge choices)"
  assumes ordered: "left < right"
  shows "(cf_lower state \<le> left \<and> right \<le> cf_upper state) \<longleftrightarrow>
    (\<forall>x. left \<le> x \<and> x < right \<longrightarrow> mahler_cf_physical_safe (cf_word state) x)"
proof
  assume guard: "cf_lower state \<le> left \<and> right \<le> cf_upper state"
  show "\<forall>x. left \<le> x \<and> x < right \<longrightarrow> mahler_cf_physical_safe (cf_word state) x"
    using guard mahler_cf_chart_exact_word[of choices] by (auto simp: state_def)
next
  assume safe: "\<forall>x. left \<le> x \<and> x < right \<longrightarrow> mahler_cf_physical_safe (cf_word state) x"
  have lower: "cf_lower state \<le> left"
    using safe ordered mahler_cf_chart_exact_word[of choices left] by (auto simp: state_def)
  have upper: "right \<le> cf_upper state"
  proof (rule ccontr)
    assume "\<not> right \<le> cf_upper state"
    then have between: "max left (cf_upper state) < right" using ordered by simp
    obtain x where x: "max left (cf_upper state) < x" "x < right"
      using dense[OF between] by blast
    have "left \<le> x" "cf_upper state \<le> x" using x by auto
    then show False using safe x mahler_cf_chart_exact_word[of choices x] by (auto simp: state_def)
  qed
  show "cf_lower state \<le> left \<and> right \<le> cf_upper state" using lower upper by simp
qed

lemma mahler_cf_guard_pullback:
  fixes gain modulus innovation x edge :: real
  assumes gain: "0 < gain" and modulus: "0 < modulus"
  shows "edge \<le> mahler_cf_lean_fraction gain modulus innovation x \<longleftrightarrow>
      (innovation + modulus*edge)/gain \<le> x"
    "mahler_cf_lean_fraction gain modulus innovation x < edge \<longleftrightarrow>
      x < (innovation + modulus*edge)/gain"
proof -
  have left: "edge \<le> (gain*x-innovation)/modulus \<longleftrightarrow>
      modulus*edge \<le> gain*x-innovation"
    using modulus by (simp add: le_divide_eq mult.commute)
  have left2: "(innovation + modulus*edge)/gain \<le> x \<longleftrightarrow>
      innovation + modulus*edge \<le> gain*x"
    using gain by (simp add: divide_le_eq mult.commute)
  show "edge \<le> mahler_cf_lean_fraction gain modulus innovation x \<longleftrightarrow>
      (innovation + modulus*edge)/gain \<le> x"
    using left left2 by (simp only: mahler_cf_lean_fraction_def; linarith)
  have right: "(gain*x-innovation)/modulus < edge \<longleftrightarrow>
      gain*x-innovation < modulus*edge"
    using modulus by (simp add: divide_less_eq mult.commute)
  have right2: "x < (innovation + modulus*edge)/gain \<longleftrightarrow>
      gain*x < innovation + modulus*edge"
    using gain by (simp add: less_divide_eq mult.commute)
  show "mahler_cf_lean_fraction gain modulus innovation x < edge \<longleftrightarrow>
      x < (innovation + modulus*edge)/gain"
    using right right2 by (simp only: mahler_cf_lean_fraction_def; linarith)
qed

lemma mahler_cf_guard_compose_exact:
  assumes invariant: "mahler_cf_guard_invariant first"
      and exact_first: "\<And>x. mahler_cf_physical_safe (cf_word first) x \<longleftrightarrow>
        cf_lower first \<le> x \<and> x < cf_upper first"
      and exact_second: "\<And>x. mahler_cf_physical_safe (cf_word second) x \<longleftrightarrow>
        cf_lower second \<le> x \<and> x < cf_upper second"
  shows "mahler_cf_physical_safe (cf_word (mahler_cf_guard_compose first second)) x \<longleftrightarrow>
    cf_lower (mahler_cf_guard_compose first second) \<le> x \<and>
      x < cf_upper (mahler_cf_guard_compose first second)"
proof -
  have gain: "0 < cf_gain first" and modulus: "0 < cf_modulus first"
    and action: "\<And>x. mahler_cf_physical_apply (cf_word first) x =
      mahler_cf_lean_fraction (cf_gain first) (cf_modulus first) (cf_innovation first) x"
    using invariant by (auto simp: mahler_cf_guard_invariant_def)
  show ?thesis using mahler_cf_guard_pullback(1)[OF gain modulus, where edge="cf_lower second" and x=x]
      mahler_cf_guard_pullback(2)[OF gain modulus, where edge="cf_upper second" and x=x]
    by (simp add: mahler_cf_guard_compose_def mahler_cf_physical_safe_append
        exact_first exact_second action; blast)
qed

fun mahler_cf_source_parities :: "nat \<Rightarrow> nat \<Rightarrow> nat list" where
  "mahler_cf_source_parities D 0 = []"
| "mahler_cf_source_parities D (Suc n) =
    D mod 2 # mahler_cf_source_parities (mahler_D_step D) n"

lemma mahler_cf_physical_source_parities:
  assumes "cylinder_guard D n x"
  shows "mahler_cf_physical_safe (mahler_cf_source_parities D n) x"
  using assms
proof (induction n arbitrary: D x)
  case 0 then show ?case by (simp add: cylinder_guard_def mahler_cf_safe_fraction_def)
next
  case (Suc n)
  have guard: "cylinder_guard D 1 x"
      "cylinder_guard (mahler_D_step D) n (fractional_endpoint D 1 x)"
    using Suc.prems source_guard_composition[of D 1 n x] by simp_all
  have inlet: "mahler_cf_safe_fraction x"
    using guard(1) by (simp add: cylinder_guard_def mahler_cf_safe_fraction_def)
  have endpoint: "fractional_endpoint D 1 x = (3*x-of_nat (D mod 2))/2"
    using fractional_step_diamond_action[of D x] by (simp add: field_simps; linarith)
  have tail: "mahler_cf_physical_safe (mahler_cf_source_parities (mahler_D_step D) n)
      ((3*x-of_nat (D mod 2))/2)"
    using Suc.IH[OF guard(2)] by (simp only: endpoint)
  show ?case using inlet tail by simp
qed

lemma mahler_cf_source_parities_length:
  "length (mahler_cf_source_parities D n) = n"
  by (induction n arbitrary: D) simp_all

lemma mahler_cf_physical_source_endpoint:
  assumes "cylinder_guard D n x"
  shows "mahler_cf_physical_apply (mahler_cf_source_parities D n) x = fractional_endpoint D n x"
  using assms
proof (induction n arbitrary: D x)
  case 0 then show ?case by (simp add: fractional_endpoint_def)
next
  case (Suc n)
  have guard: "cylinder_guard (mahler_D_step D) n (fractional_endpoint D 1 x)"
    using Suc.prems source_guard_composition[of D 1 n x] by simp
  have endpoint: "fractional_endpoint D 1 x = (3*x-of_nat (D mod 2))/2"
    using fractional_step_diamond_action[of D x] by (simp add: field_simps; linarith)
  have composition: "fractional_endpoint D (Suc n) x =
      fractional_endpoint (mahler_D_step D) n (fractional_endpoint D 1 x)"
    using fractional_endpoint_composition[of D 1 n x] by simp
  have tail: "mahler_cf_physical_apply (mahler_cf_source_parities (mahler_D_step D) n)
      ((3*x-of_nat (D mod 2))/2) =
      fractional_endpoint (mahler_D_step D) n (fractional_endpoint D 1 x)"
    by (subst endpoint[symmetric]) (rule Suc.IH[OF guard])
  show ?case using tail composition
    by (simp only: mahler_cf_source_parities.simps mahler_cf_physical_apply.simps)
qed

theorem mahler_cf_chart_source_action:
  fixes choices :: "bool list" and state :: mahler_cf_compiled_guard
  defines "state \<equiv> mahler_cf_guard_compile (map mahler_cf_chart_edge choices)"
  assumes point: "cf_lower state \<le> x" "x < cf_upper state"
    and source: "cylinder_guard D (cf_ticks state) x"
  shows "cf_word state = mahler_cf_source_parities D (cf_ticks state)"
    and "mahler_cf_physical_apply (cf_word state) x =
      fractional_endpoint D (cf_ticks state) x"
proof -
  have inv: "mahler_cf_guard_invariant state"
    by (simp add: state_def mahler_cf_guard_compiler_correct)
  have safe: "mahler_cf_physical_safe (cf_word state) x"
    using inv point by (auto simp: mahler_cf_guard_invariant_def)
  have source_safe: "mahler_cf_physical_safe (mahler_cf_source_parities D (cf_ticks state)) x"
    by (rule mahler_cf_physical_source_parities[OF source])
  have equal_length: "length (cf_word state) = length (mahler_cf_source_parities D (cf_ticks state))"
    using inv by (simp add: mahler_cf_guard_invariant_def mahler_cf_source_parities_length)
  show words: "cf_word state = mahler_cf_source_parities D (cf_ticks state)"
    by (rule mahler_cf_chart_safe_words_unique[OF safe source_safe equal_length])
  show "mahler_cf_physical_apply (cf_word state) x = fractional_endpoint D (cf_ticks state) x"
    using mahler_cf_physical_source_endpoint[OF source] words by simp
qed

lemma mahler_cf_inverse_power_transport:
  fixes modulus :: int and exponent :: nat
  assumes modulus: "1 < modulus" and coprime: "coprime (3::int) modulus"
  shows "modular_inverse modulus ((3::int)^exponent) =
    (modular_inverse modulus 3)^exponent mod modulus"
proof (induction exponent)
  case 0
  then show ?case using modulus by (simp add: modular_inverse_1)
next
  case (Suc k)
  have power_coprime: "coprime ((3::int)^k) modulus"
    using coprime by (simp add: coprime_power_left_iff)
  have product: "modular_inverse modulus ((3::int)^k * 3) =
      (modular_inverse modulus 3 * modular_inverse modulus (3^k)) mod modulus"
    by (rule modular_inverse_int_mult[OF power_coprime coprime]) (use modulus in simp)
  have step: "modular_inverse modulus ((3::int)^k * 3) =
      (modular_inverse modulus 3 * ((modular_inverse modulus 3)^k mod modulus)) mod modulus"
    using product Suc.IH by (simp only: Suc.IH)
  also have "... = (modular_inverse modulus 3 * (modular_inverse modulus 3)^k) mod modulus"
    by (rule mod_mult_right_eq)
  finally show ?case by (simp only: power_Suc mult.commute)
qed

lemma mahler_cf_inverse_unit_modulus:
  "modular_inverse (1::int) ((3::int)^k) = 0"
  by (simp add: modular_inverse_def)

lemma mahler_cf_three_dyadic_coprime:
  "coprime (3::int) (2^k)"
  by (simp add: coprime_power_right_iff)

ML \<open>
  val checked = @{thms mahler_cf_chart_source_action mahler_cf_guard_compose_exact
    mahler_cf_chart_edge_scaled mahler_cf_chart_interval_exact
    mahler_cf_chart_safe_words_unique mahler_cf_chart_rejected_width
    mahler_cf_guard_compose_invariant mahler_cf_inverse_unit_modulus mahler_cf_three_dyadic_coprime
    mahler_cf_inverse_power_transport mahler_cf_zero_endpoint_cancel
    mahler_cf_zero_endpoint_first mahler_cf_guard_compiler_correct
    mahler_cf_guard_compile_word
    mahler_cf_compiled_stall_not_guarded mahler_cf_compiled_later_ticks
    mahler_cf_guard_scaled_update};
  val _ = if null (Thm_Deps.all_oracles checked) then () else error "CF guard compiler oracle";
  val _ = if Thm_Deps.has_skip_proof checked then error "CF guard compiler skipped proof" else ();
\<close>

end
