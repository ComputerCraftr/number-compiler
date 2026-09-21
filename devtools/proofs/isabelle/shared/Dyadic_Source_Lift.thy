theory Dyadic_Source_Lift
  imports S_Arithmetic_Skew
begin

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

lemma dyadic_source_word_append:
  "dyadic_source_word step label source (first+second) =
    dyadic_source_word step label source first @
      dyadic_source_word step label
        (dyadic_source_orbit step source first) second"
  by (induction first arbitrary: source) simp_all

lemma dyadic_source_word_length [simp]:
  "length (dyadic_source_word step label source n) = n"
  by (induction n arbitrary: source) simp_all

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

end

text \<open>The locale proves semantic finite transport only.  A production
family must still authenticate its source, instantiate both one-step laws,
connect its family action to shared skew composition, and account for
construction and retained storage.\<close>

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms dyadic_source_orbit_funpow dyadic_source_word_append
      dyadic_source_word_length
      dyadic_constant_gain_product
      dyadic_source_action.positive_precision_label
      dyadic_source_action.positive_precision_step
      dyadic_source_action.source_lift_with_extra_precision
      dyadic_source_action.exact_precision_source_lift})
    then () else error "Dyadic source lift depends on an oracle";
\<close>

end
