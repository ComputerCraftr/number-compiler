theory Dyadic_Source_Lift
  imports S_Arithmetic_Skew
begin

text \<open>The production split is the largest power of two strictly below
the represented span.  This executable halving recursion has logarithmic
depth; it never enumerates the span or its candidate powers.\<close>

function power_floor :: "nat \<Rightarrow> nat" where
  "power_floor n = (if n < 2 then 1 else 2 * power_floor (n div 2))"
  by pat_completeness auto
termination
  by (relation "measure id") auto

declare power_floor.simps [simp del]

definition balanced_left_span :: "nat \<Rightarrow> nat" where
  "balanced_left_span n = power_floor (n-1)"

lemma power_floor_positive [simp]: "0 < power_floor n"
proof (induction n rule: less_induct)
  case (less n)
  show ?case
  proof (cases "n < 2")
    case True
    then show ?thesis by (subst power_floor.simps) simp
  next
    case False
    have q_less: "n div 2 < n" using False by simp
    then have "power_floor n = 2 * power_floor (n div 2)"
      using False by (subst power_floor.simps) simp
    with less.IH[OF q_less] show ?thesis by simp
  qed
qed

lemma power_floor_bounds_aux:
  "0 < n \<longrightarrow> power_floor n \<le> n \<and> n < 2 * power_floor n"
proof (induction n rule: less_induct)
  case (less n)
  show ?case
  proof (cases "0 < n")
    case False
    then show ?thesis by simp
  next
    case True
    show ?thesis
    proof (cases "n < 2")
      case True
      with \<open>0 < n\<close> show ?thesis
        by (simp add: power_floor.simps)
    next
      case False
      then have q: "0 < n div 2" by simp
      have lessq: "n div 2 < n" using False by simp
      have unfold: "power_floor n = 2 * power_floor (n div 2)"
        using False by (subst power_floor.simps) simp
      have bounds: "power_floor (n div 2) \<le> n div 2"
        "n div 2 < 2 * power_floor (n div 2)"
        using less.IH[OF lessq] q by auto
      have decomp: "n = 2 * (n div 2) + n mod 2" by simp
      have remainder: "n mod 2 < 2" by simp
      have first: "power_floor n \<le> n"
        using unfold bounds(1) decomp by linarith
      have second: "n < 2 * power_floor n"
        using unfold bounds(2) decomp remainder by linarith
      show ?thesis using True first second by simp
    qed
  qed
qed

lemma power_floor_bounds:
  assumes "0 < n"
  shows "power_floor n \<le> n" "n < 2 * power_floor n"
  using power_floor_bounds_aux[of n] assms by auto

lemma power_floor_is_power: "\<exists>e. power_floor n = 2^e"
proof (induction n rule: less_induct)
  case (less n)
  show ?case
  proof (cases "n < 2")
    case True
    have "power_floor n = 2^0"
      using True by (subst power_floor.simps) simp
    then show ?thesis by blast
  next
    case False
    have q_less: "n div 2 < n" using False by simp
    obtain e where ih: "power_floor (n div 2) = 2^e"
      using less.IH[OF q_less] by auto
    have "power_floor n = 2 * power_floor (n div 2)"
      using False by (subst power_floor.simps) simp
    then show ?thesis using ih
      by (auto simp: power_Suc intro!: exI[of _ "Suc e"])
  qed
qed

lemma power_floor_dominates_power_aux:
  "2^e \<le> n \<longrightarrow> 2^e \<le> power_floor n"
proof (induction n arbitrary: e rule: less_induct)
  case (less n)
  show ?case
  proof (cases "2^e \<le> n")
    case False
    then show ?thesis by simp
  next
    case True
    show ?thesis
    proof (cases "n < 2")
      case True
      with \<open>2^e \<le> n\<close> show ?thesis
        by (simp add: power_floor.simps)
    next
      case False
      have unfold: "power_floor n = 2 * power_floor (n div 2)"
        using False by (subst power_floor.simps) simp
      show ?thesis
      proof (cases e)
        case 0
        then have one: "(2::nat)^e = 1" by simp
        show ?thesis using one power_floor_positive[of n] by arith
      next
        case (Suc predecessor)
        have q_less: "n div 2 < n" using False by simp
        have q_bound: "2^predecessor \<le> n div 2"
          using True by (simp add: Suc power_Suc)
        have "2^predecessor \<le> power_floor (n div 2)"
          using less.IH[OF q_less, of predecessor] q_bound by auto
        with unfold Suc True show ?thesis
          by (simp add: power_Suc)
      qed
    qed
  qed
qed

lemma power_floor_dominates_power:
  assumes "2^e \<le> n"
  shows "2^e \<le> power_floor n"
  using power_floor_dominates_power_aux[of e n] assms by simp

lemma balanced_left_span_bounds:
  assumes "1 < n"
  shows "0 < balanced_left_span n" "balanced_left_span n < n"
proof -
  have "0 < n-1" using assms by simp
  then have "power_floor (n-1) \<le> n-1"
    by (rule power_floor_bounds)
  show "0 < balanced_left_span n"
    by (simp add: balanced_left_span_def)
  show "balanced_left_span n < n"
    using assms \<open>power_floor (n-1) \<le> n-1\<close>
    by (simp add: balanced_left_span_def)
qed

lemma balanced_left_span_largest:
  assumes "1 < n" "k < n" "k = 2^e"
  shows "k \<le> balanced_left_span n"
  using assms power_floor_dominates_power[of e "n-1"]
  by (simp add: balanced_left_span_def)

lemma balanced_left_span_large_pos [simp]:
  "64 < n \<Longrightarrow> 0 < balanced_left_span n"
  using balanced_left_span_bounds[of n] by simp

lemma balanced_left_span_large_lt [simp]:
  "64 < n \<Longrightarrow> balanced_left_span n < n"
  using balanced_left_span_bounds[of n] by simp


text \<open>A shared finite source-cylinder induction.  A family must prove
only its concrete one-step label stability and one-step dyadic translation.
The locale does not assume an orbit lift, a branch itinerary, or a powered
constructor.  The resulting word and endpoint laws are derived together from
those local equations.\<close>

fun dyadic_source_orbit :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
where
  "dyadic_source_orbit step source 0 = source"
| "dyadic_source_orbit step source (Suc n) =
    dyadic_source_orbit step (step source) n"

fun dyadic_source_word ::
    "(nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> 'label) \<Rightarrow>
      nat \<Rightarrow> nat \<Rightarrow> 'label list"
where
  "dyadic_source_word step label source 0 = []"
| "dyadic_source_word step label source (Suc n) =
    label source # dyadic_source_word step label (step source) n"

definition dyadic_gain_product ::
    "('label \<Rightarrow> nat) \<Rightarrow> 'label list \<Rightarrow> nat"
where
  "dyadic_gain_product gain word = prod_list (map gain word)"

lemma dyadic_constant_gain_product:
  "dyadic_gain_product (\<lambda>_. gain) word = gain^length word"
  by (induction word) (simp_all add: dyadic_gain_product_def)

lemma dyadic_source_orbit_funpow:
  "dyadic_source_orbit step source n = (step ^^ n) source"
  by (induction n arbitrary: source)
    (simp_all del: funpow.simps(2) add: funpow_Suc_right)

lemma dyadic_source_orbit_add:
  "dyadic_source_orbit step source (first+second) =
    dyadic_source_orbit step (dyadic_source_orbit step source first) second"
  by (induction first arbitrary: source) simp_all

lemma dyadic_source_word_append:
  "dyadic_source_word step label source (first+second) =
    dyadic_source_word step label source first @
      dyadic_source_word step label
        (dyadic_source_orbit step source first) second"
  by (induction first arbitrary: source) simp_all

lemma dyadic_source_word_length [simp]:
  "length (dyadic_source_word step label source n) = n"
  by (induction n arbitrary: source) simp_all

lemma dyadic_source_orbit_lower_bound:
  assumes half_bound: "\<And>x. x \<le> 2 * step x"
  shows "source \<le> 2^n * dyadic_source_orbit step source n"
proof (induction n arbitrary: source)
  case 0 then show ?case by simp
next
  case (Suc n)
  have "source \<le> 2 * step source" by (rule half_bound)
  also have "\<dots> \<le> 2 * (2^n * dyadic_source_orbit step (step source) n)"
    by (rule mult_left_mono[OF Suc.IH]) simp
  finally show ?case by (simp add: power_Suc algebra_simps)
qed

text \<open>
  An admitted high fiber can exclude an exact singleton cycle throughout a
  block. The runtime applies this only when branch gains are positive and
  offsets nonnegative, so its integral branch equation gives half_bound.
  Smaller high fibers keep singleton authority in their reuse keys.
\<close>

theorem dyadic_high_fiber_excludes_small_states:
  assumes half_bound: "\<And>x. x \<le> 2 * step x"
    and time: "j \<le> n" and high: "cycle_bound < high_fiber"
  shows "cycle_bound < dyadic_source_orbit step (residue + 2^n * high_fiber) j"
proof (rule ccontr)
  let ?v = "dyadic_source_orbit step (residue + 2^n * high_fiber) j"
  assume "\<not> cycle_bound < ?v"
  then have small: "?v \<le> cycle_bound" by simp
  have lower: "residue + 2^n * high_fiber \<le> 2^j * ?v"
    by (rule dyadic_source_orbit_lower_bound[OF half_bound])
  have powers: "(2::nat)^j \<le> 2^n"
    by (rule power_increasing[OF time]) simp
  have upper: "2^j * ?v \<le> 2^n * cycle_bound"
    by (rule mult_mono[OF powers small]) simp_all
  have strict: "2^n * cycle_bound < 2^n * high_fiber"
    using high by simp
  show False using lower upper strict by arith
qed

locale dyadic_source_action =
  fixes step :: "nat \<Rightarrow> nat"
    and label :: "nat \<Rightarrow> 'label"
    and gain :: "'label \<Rightarrow> nat"
  assumes label_translation:
      "\<And>source lift_amount.
        label (source + 2*lift_amount) = label source"
    and step_translation:
      "\<And>source lift_amount. step (source + 2*lift_amount) =
        step source + gain (label source) * lift_amount"
begin

lemma positive_precision_label:
  assumes "0 < precision"
  shows "label (source + 2^precision*lift_amount) = label source"
proof -
  obtain tail where precision: "precision = Suc tail"
    using assms by (cases precision) auto
  show ?thesis
    using label_translation[of source "2^tail*lift_amount"]
    by (simp add: precision power_Suc algebra_simps)
qed

lemma positive_precision_step:
  assumes "0 < precision"
  shows "step (source + 2^precision*lift_amount) =
    step source + 2^(precision-1) * gain (label source) * lift_amount"
proof -
  obtain tail where precision: "precision = Suc tail"
    using assms by (cases precision) auto
  show ?thesis
    using step_translation[of source "2^tail*lift_amount"]
    by (simp add: precision power_Suc algebra_simps)
qed

theorem source_lift_with_extra_precision:
  "dyadic_source_word step label
      (source + 2^(n+extra)*lift_amount) n =
      dyadic_source_word step label source n \<and>
   dyadic_source_orbit step (source + 2^(n+extra)*lift_amount) n =
      dyadic_source_orbit step source n +
      2^extra * dyadic_gain_product gain
        (dyadic_source_word step label source n) * lift_amount"
proof (induction n arbitrary: source lift_amount)
  case 0
  then show ?case
    by (simp add: dyadic_gain_product_def)
next
  case (Suc n)
  let ?g = "gain (label source)"
  have shifted_label:
      "label (source + 2^(Suc n+extra)*lift_amount) = label source"
    by (rule positive_precision_label) simp
  have shifted_step:
      "step (source + 2^(Suc n+extra)*lift_amount) =
       step source + 2^(n+extra) * (?g*lift_amount)"
    using positive_precision_step[of "Suc n+extra" source lift_amount]
    by (simp add: algebra_simps)
  note tail = Suc.IH[of "step source" "?g*lift_amount"]
  show ?case
    using shifted_label shifted_step tail
    by (simp add: dyadic_gain_product_def algebra_simps)
qed

corollary exact_precision_source_lift:
  "dyadic_source_word step label (source + 2^n*lift_amount) n =
      dyadic_source_word step label source n \<and>
   dyadic_source_orbit step (source + 2^n*lift_amount) n =
      dyadic_source_orbit step source n +
      dyadic_gain_product gain
        (dyadic_source_word step label source n) * lift_amount"
  using source_lift_with_extra_precision[of source n 0 lift_amount]
  by simp

text \<open>Source-only dyadic macro construction. Each recursive right call
uses the left return's transported low residue. No right endpoint or itinerary
is supplied. This is the arithmetic recursion normalized by the Python leaf
worklist; memo publication and resource accounting remain separate obligations.
The tuple contains the base endpoint, high-fiber gain and complete label word.
D4, D8 and D16 are levels 2, 3 and 4.\<close>

fun source_macro :: "nat \<Rightarrow> nat \<Rightarrow> nat * nat * 'label list" where
  "source_macro 0 source = (step source, gain (label source), [label source])"
| "source_macro (Suc level) source =
    (let modulus = 2^(2^level);
         (left_end, left_gain, left_word) = source_macro level (source mod modulus);
         middle = left_end + left_gain * (source div modulus);
         (right_end, right_gain, right_word) = source_macro level (middle mod modulus)
     in (right_end + right_gain * (middle div modulus),
         right_gain * left_gain, left_word @ right_word))"

text \<open>The endpoint/gain projection has its own executable recursion.  It
does not retain or append a label list.  Its proof below uses the older
word-bearing macro solely as an extensional specification; neither definition
claims that source admission or production construction is cheap.\<close>

fun source_macro_projection :: "nat \<Rightarrow> nat \<Rightarrow> nat * nat" where
  "source_macro_projection 0 source = (step source, gain (label source))"
| "source_macro_projection (Suc level) source =
    (let modulus = 2^(2^level);
         left = source_macro_projection level (source mod modulus);
         middle = fst left + snd left * (source div modulus);
         right = source_macro_projection level (middle mod modulus)
     in (fst right + snd right * (middle div modulus),
         snd right * snd left))"

lemma source_macro_projection_matches:
  "source_macro_projection level source =
    (case source_macro level source of (endpoint, multiplier, word) \<Rightarrow>
      (endpoint, multiplier))"
  by (induction level arbitrary: source)
    (simp_all add: Let_def split: prod.splits)

lemma source_residue_lift:
  "dyadic_source_word step label source n =
      dyadic_source_word step label (source mod 2^n) n \<and>
   dyadic_source_orbit step source n =
      dyadic_source_orbit step (source mod 2^n) n +
      dyadic_gain_product gain
        (dyadic_source_word step label (source mod 2^n) n) * (source div 2^n)"
  using exact_precision_source_lift[of "source mod 2^n" n "source div 2^n"]
  by (simp add: mult.commute)

theorem source_macro_correct:
  "source_macro level source =
    (dyadic_source_orbit step source (2^level),
     dyadic_gain_product gain (dyadic_source_word step label source (2^level)),
     dyadic_source_word step label source (2^level))"
proof (induction level arbitrary: source)
  case 0
  then show ?case by (simp add: dyadic_gain_product_def)
next
  case (Suc level)
  let ?n = "2^level"
  let ?middle = "dyadic_source_orbit step source ?n"
  note first = source_residue_lift[of source ?n]
  note second = source_residue_lift[of ?middle ?n]
  have first_word:
    "dyadic_source_word step label (source mod 2^?n) ?n =
      dyadic_source_word step label source ?n" using first by simp
  have first_end:
    "dyadic_source_orbit step (source mod 2^?n) ?n +
      dyadic_gain_product gain (dyadic_source_word step label source ?n)
        * (source div 2^?n) = ?middle" using first by simp
  have second_word:
    "dyadic_source_word step label (?middle mod 2^?n) ?n =
      dyadic_source_word step label ?middle ?n" using second by simp
  have second_end:
    "dyadic_source_orbit step (?middle mod 2^?n) ?n +
      dyadic_gain_product gain (dyadic_source_word step label ?middle ?n)
        * (?middle div 2^?n) = dyadic_source_orbit step ?middle ?n"
    using second by simp
  have unfolded:
    "source_macro (Suc level) source =
      (dyadic_source_orbit step ?middle ?n,
       dyadic_gain_product gain (dyadic_source_word step label ?middle ?n) *
         dyadic_gain_product gain (dyadic_source_word step label source ?n),
       dyadic_source_word step label source ?n @ dyadic_source_word step label ?middle ?n)"
    by (simp only: source_macro.simps Suc.IH Let_def case_prod_conv
      first_end second_end first_word second_word)
  show ?case
    by (subst unfolded) (simp add: power_Suc numeral_2_eq_2 mult_2
      dyadic_source_orbit_add dyadic_source_word_append dyadic_gain_product_def
      mult.commute)

qed

theorem source_macro_projection_correct:
  "source_macro_projection level source =
    (dyadic_source_orbit step source (2^level),
     dyadic_gain_product gain
       (dyadic_source_word step label source (2^level)))"
  using source_macro_projection_matches[of level source]
    source_macro_correct[of level source]
  by simp

corollary source_macro_projection_constant_gain:
  assumes fixed_gain: "gain = (\<lambda>_. constant_gain)"
  shows "source_macro_projection level source =
    (dyadic_source_orbit step source (2^level), constant_gain^(2^level))"
  using source_macro_projection_correct[of level source]
  by (simp add: fixed_gain dyadic_constant_gain_product)

corollary six_step_constant_three_lift:
  assumes fixed_gain: "gain = (\<lambda>_. 3)"
  shows "dyadic_source_orbit step (source + 64 * fiber) 6 =
    dyadic_source_orbit step source 6 + 729 * fiber"
  using exact_precision_source_lift[of source 6 fiber]
  by (simp add: fixed_gain dyadic_constant_gain_product)

lemma block_three_adic_high_fiber_forgetting:
  fixes fiber :: int
  assumes precision: "h \<le> 6 * blocks"
  shows "((3::int)^(6 * blocks) * fiber) mod 3^h = 0"
proof -
  have "(3::int)^h dvd 3^(6 * blocks)"
    using precision by (rule le_imp_power_dvd)
  then show ?thesis by simp
qed

lemma six_step_three_adic_high_fiber_forgetting:
  fixes fiber :: int
  assumes precision: "h \<le> 6"
  shows "(729 * fiber) mod 3^h = 0"
  using block_three_adic_high_fiber_forgetting[of h 1 fiber]
    precision by simp

end

text \<open>The locale proves semantic finite transport only.  A production
family must still authenticate its source, instantiate both one-step laws,
connect its family action to shared skew composition, and account for
construction and retained storage.\<close>

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms balanced_left_span_bounds balanced_left_span_largest
      dyadic_source_orbit_funpow dyadic_source_orbit_add dyadic_source_word_append
      dyadic_source_word_length
      dyadic_source_orbit_lower_bound dyadic_high_fiber_excludes_small_states
      dyadic_constant_gain_product
      dyadic_source_action.positive_precision_label
      dyadic_source_action.positive_precision_step
      dyadic_source_action.source_lift_with_extra_precision
      dyadic_source_action.exact_precision_source_lift
      dyadic_source_action.source_residue_lift
      dyadic_source_action.source_macro_correct
      dyadic_source_action.source_macro_projection_matches
      dyadic_source_action.source_macro_projection_correct
      dyadic_source_action.source_macro_projection_constant_gain
      dyadic_source_action.six_step_constant_three_lift
      dyadic_source_action.block_three_adic_high_fiber_forgetting
      dyadic_source_action.six_step_three_adic_high_fiber_forgetting})
    then () else error "Dyadic source lift depends on an oracle";
\<close>

end
