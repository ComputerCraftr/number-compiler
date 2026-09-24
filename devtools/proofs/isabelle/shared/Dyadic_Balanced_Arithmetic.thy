theory Dyadic_Balanced_Arithmetic
  imports Dyadic_Balanced_Worklist Dyadic_Prefix_Summary
begin

record dyadic_effect =
  effect_skew :: "int skew_transfer"
  effect_events :: nat
  effect_delta :: int
  effect_minimum :: int

definition effect_identity :: dyadic_effect where
  "effect_identity = \<lparr>effect_skew=shared_skew_identity,
    effect_events=0, effect_delta=0, effect_minimum=0\<rparr>"

definition effect_then :: "dyadic_effect \<Rightarrow> dyadic_effect \<Rightarrow> dyadic_effect" where
  "effect_then A B = \<lparr>
    effect_skew=shared_skew_then (effect_skew A) (effect_skew B),
    effect_events=effect_events A + effect_events B,
    effect_delta=effect_delta A + effect_delta B,
    effect_minimum=min (effect_minimum A) (effect_delta A + effect_minimum B)\<rparr>"

definition effect_admitted :: "dyadic_effect \<Rightarrow> bool" where
  "effect_admitted E \<longleftrightarrow>
    effect_minimum E \<le> 0 \<and> effect_minimum E \<le> effect_delta E"

lemma effect_then_assoc:
  "effect_then (effect_then A B) C = effect_then A (effect_then B C)"
  by (simp add: effect_then_def shared_skew_associative min.assoc
      min_add_distrib_right algebra_simps)

lemma effect_then_identity:
  assumes "effect_admitted E"
  shows "effect_then effect_identity E = E"
    "effect_then E effect_identity = E"
  using assms by (cases E; simp add: effect_admitted_def effect_then_def
      effect_identity_def min_def)+

lemma effect_then_admitted:
  assumes "effect_admitted A" "effect_admitted B"
  shows "effect_admitted (effect_then A B)"
  using assms by (auto simp: effect_admitted_def effect_then_def min_def)

locale dyadic_arithmetic_constructor = dyadic_source_action step label gain
  for step :: "nat \<Rightarrow> nat" and label :: "nat \<Rightarrow> 'label"
    and gain :: "'label \<Rightarrow> nat" +
  fixes shift :: "'label \<Rightarrow> int"
    and events :: "'label \<Rightarrow> nat"
    and weight :: "'label \<Rightarrow> int"
  assumes generator_equation:
    "\<And>x. int (gain (label x)) * int x + shift (label x) = 2 * int (step x)"
begin

definition effect_atom :: "'label \<Rightarrow> dyadic_effect" where
  "effect_atom b = \<lparr>
    effect_skew=\<lparr>upper=int (gain b), offset=shift b, lower=2\<rparr>,
    effect_events=events b, effect_delta=weight b,
    effect_minimum=min 0 (weight b)\<rparr>"

fun effect_word :: "'label list \<Rightarrow> dyadic_effect" where
  "effect_word [] = effect_identity"
| "effect_word (b#bs) = effect_then (effect_atom b) (effect_word bs)"

lemma effect_word_admitted [simp]: "effect_admitted (effect_word bs)"
proof (induction bs)
  case Nil
  then show ?case by (simp add: effect_admitted_def effect_identity_def)
next
  case (Cons b bs)
  have "effect_admitted (effect_atom b)"
    by (simp add: effect_admitted_def effect_atom_def)
  from effect_then_admitted[OF this Cons.IH] show ?case by simp
qed

lemma effect_word_append:
  "effect_word (xs @ ys) = effect_then (effect_word xs) (effect_word ys)"
  by (induction xs)
    (simp_all add: effect_then_assoc effect_then_identity)

lemma effect_word_denominator [simp]:
  "lower (effect_skew (effect_word bs)) = 2^length bs"
  by (induction bs) (simp_all add: effect_identity_def effect_then_def
      effect_atom_def shared_skew_identity_def shared_skew_then_def)

lemma effect_word_safety:
  "(effect_delta (effect_word bs), effect_minimum (effect_word bs)) =
    prefix_summary weight bs"
proof (induction bs)
  case Nil
  then show ?case by (simp add: effect_identity_def)
next
  case (Cons b bs)
  have minimum: "effect_minimum (effect_word bs) \<le> 0"
    using effect_word_admitted[of bs] by (simp add: effect_admitted_def)
  have absorb: "min (min 0 (weight b))
      (weight b + effect_minimum (effect_word bs)) =
    min 0 (weight b + effect_minimum (effect_word bs))"
    using minimum by (auto simp: min_def; linarith)
  show ?case
    by (simp add: Cons.IH[symmetric] effect_then_def effect_atom_def Let_def absorb)
qed

lemma effect_word_events:
  "effect_events (effect_word bs) = sum_list (map events bs)"
  by (induction bs) (simp_all add: effect_identity_def effect_then_def effect_atom_def)

definition source_effect :: "nat \<Rightarrow> nat \<Rightarrow> dyadic_effect" where
  "source_effect n x = effect_word (dyadic_source_word step label x n)"

lemma source_effect_low:
  "source_effect n (x mod 2^n) = source_effect n x"
  using source_residue_lift[of x n]
  by (simp add: source_effect_def)

lemma source_effect_append:
  "source_effect (a+b) x = effect_then (source_effect a x)
    (source_effect b (dyadic_source_orbit step x a))"
  by (simp add: source_effect_def dyadic_source_word_append effect_word_append)

lemma source_effect_equation:
  "upper (effect_skew (source_effect n x)) * int x +
      offset (effect_skew (source_effect n x)) =
    lower (effect_skew (source_effect n x)) * int (dyadic_source_orbit step x n)"
proof (induction n arbitrary: x)
  case 0
  then show ?case by (simp add: source_effect_def effect_identity_def shared_skew_identity_def)
next
  case (Suc n)
  have atom: "upper (effect_skew (effect_atom (label x))) * int x +
      offset (effect_skew (effect_atom (label x))) =
    lower (effect_skew (effect_atom (label x))) * int (step x)"
    by (simp add: effect_atom_def generator_equation)
  note composed = shared_skew_transport[OF atom Suc.IH[of "step x"]]
  show ?case using composed
    by (simp add: source_effect_def effect_then_def)
qed

definition effect_apply :: "dyadic_effect \<Rightarrow> nat \<Rightarrow> nat" where
  "effect_apply E x = nat ((upper (effect_skew E) * int x +
    offset (effect_skew E)) div lower (effect_skew E))"

lemma source_effect_apply:
  "effect_apply (source_effect n x) x = dyadic_source_orbit step x n"
  using source_effect_equation[of n x]
  by (simp add: effect_apply_def source_effect_def)

fun arithmetic_leaf_loop :: "nat \<Rightarrow> nat \<Rightarrow> dyadic_effect \<Rightarrow> nat * dyadic_effect" where
  "arithmetic_leaf_loop 0 x E = (x,E)"
| "arithmetic_leaf_loop (Suc n) x E =
    arithmetic_leaf_loop n (step x) (effect_then E (effect_atom (label x)))"

lemma arithmetic_leaf_loop_correct:
  assumes "effect_admitted E"
  shows "arithmetic_leaf_loop n x E =
    (dyadic_source_orbit step x n, effect_then E (source_effect n x))"
  using assms
proof (induction n arbitrary: x E)
  case 0
  then show ?case by (simp add: source_effect_def effect_then_identity)
next
  case (Suc n)
  have atom: "effect_admitted (effect_atom (label x))"
    by (simp add: effect_admitted_def effect_atom_def)
  have admitted: "effect_admitted (effect_then E (effect_atom (label x)))"
    by (rule effect_then_admitted[OF Suc.prems atom])
  show ?case using Suc.IH[OF admitted]
    by (simp add: source_effect_def effect_then_assoc)
qed

definition arithmetic_leaf :: "nat \<Rightarrow> nat \<Rightarrow> dyadic_effect" where
  "arithmetic_leaf n x = snd (arithmetic_leaf_loop n x effect_identity)"

lemma arithmetic_leaf_correct:
  "arithmetic_leaf n x = source_effect n x"
proof -
  have id: "effect_admitted effect_identity"
    by (simp add: effect_admitted_def effect_identity_def)
  show ?thesis using arithmetic_leaf_loop_correct[OF id, of n x]
    by (simp add: arithmetic_leaf_def effect_then_identity source_effect_def)
qed

definition arithmetic_transport :: "dyadic_effect \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "arithmetic_transport E x width = effect_apply E x mod 2^width"

definition arithmetic_join :: "nat \<Rightarrow> nat \<Rightarrow> dyadic_effect \<Rightarrow> dyadic_effect \<Rightarrow> dyadic_effect" where
  "arithmetic_join n x A B = effect_then A B"

sublocale balanced: dyadic_balanced_worklist arithmetic_leaf arithmetic_transport
    arithmetic_join cache_admit for cache_admit .

theorem balanced_spec_source_effect:
  "balanced.balanced_spec n x = source_effect n x"
proof (induction n arbitrary: x rule: less_induct)
  case (less n)
  show ?case
  proof (cases "n \<le> 64")
    case True
    then show ?thesis
      by (subst balanced.balanced_spec.simps)
        (simp add: arithmetic_leaf_correct)
  next
    case False
    let ?l = "balanced_left_span n"
    let ?r = "n - ?l"
    have bounds: "0 < ?l" "?l < n"
      using balanced_left_span_bounds[of n] False by auto
    have right_bound: "?r < n" using bounds by arith
    have widths: "?l + ?r = n" using bounds by arith
    have left: "balanced.balanced_spec ?l (x mod 2^?l) = source_effect ?l x"
      using less.IH[OF bounds(2), of "x mod 2^?l"]
      by (simp add: source_effect_low)
    have transported: "arithmetic_transport (source_effect ?l x) x ?r =
        dyadic_source_orbit step x ?l mod 2^?r"
      by (simp add: arithmetic_transport_def source_effect_apply)
    have right: "balanced.balanced_spec ?r
        (arithmetic_transport (source_effect ?l x) x ?r) =
      source_effect ?r (dyadic_source_orbit step x ?l)"
      using less.IH[OF right_bound,
        of "arithmetic_transport (source_effect ?l x) x ?r"]
      by (simp only: transported source_effect_low)
    have "balanced.balanced_spec n x = effect_then (source_effect ?l x)
        (source_effect ?r (dyadic_source_orbit step x ?l))"
      by (subst balanced.balanced_spec.simps)
        (simp only: False if_False Let_def left right arithmetic_join_def)
    also have "\<dots> = source_effect n x"
      using source_effect_append[of ?l ?r x] widths by simp
    finally show ?thesis .
  qed
qed

theorem execute_balanced_source_effect:
  "balanced.execute_balanced cache_admit n x = Some (source_effect n x)"
  by (simp add: balanced.execute_balanced_correct balanced_spec_source_effect)

definition construct_source_effect where
  "construct_source_effect cache_admit n source =
    balanced.execute_balanced cache_admit n (source mod 2^n)"

theorem construct_source_effect_correct:
  "construct_source_effect cache_admit n source = Some (source_effect n source)"
  by (simp add: construct_source_effect_def execute_balanced_source_effect
      source_effect_low)

theorem construct_source_effect_endpoint:
  "map_option (\<lambda>E. effect_apply E source)
      (construct_source_effect cache_admit n source) =
    Some (dyadic_source_orbit step source n)"
  by (simp add: construct_source_effect_correct source_effect_apply)

theorem execute_balanced_endpoint:
  "map_option (\<lambda>E. effect_apply E x) (balanced.execute_balanced cache_admit n x) =
    Some (dyadic_source_orbit step x n)"
  by (simp add: execute_balanced_source_effect source_effect_apply)

theorem execute_balanced_prefix_safety:
  "map_option (\<lambda>E. 0 \<le> balance + effect_minimum E)
      (balanced.execute_balanced cache_admit n x) =
    Some (prefix_guard weight balance (dyadic_source_word step label x n))"
proof -
  have minimum: "effect_minimum (source_effect n x) =
      snd (prefix_summary weight (dyadic_source_word step label x n))"
    using effect_word_safety[of "dyadic_source_word step label x n"]
    by (metis source_effect_def snd_conv)
  show ?thesis
    by (simp add: execute_balanced_source_effect minimum
        prefix_summary_guard_iff)
qed

lemma source_effect_reduced_numerator:
  fixes n width x :: nat
  defines "E \<equiv> source_effect n x"
  defines "modulus \<equiv> (2::int)^(n+width)"
  shows "((upper (effect_skew E) mod modulus * (int x mod modulus) +
      offset (effect_skew E) mod modulus) mod modulus) div
      lower (effect_skew E) =
    int (dyadic_source_orbit step x n) mod (2::int)^width"
proof -
  have denominator: "lower (effect_skew E) = (2::int)^n"
    by (simp add: E_def source_effect_def)
  have equation: "upper (effect_skew E) * int x + offset (effect_skew E) =
      (2::int)^n * int (dyadic_source_orbit step x n)"
    using source_effect_equation[of n x] by (simp add: E_def source_effect_def)
  have reduced: "(upper (effect_skew E) mod modulus * (int x mod modulus) +
      offset (effect_skew E) mod modulus) mod modulus =
      (upper (effect_skew E) * int x + offset (effect_skew E)) mod modulus"
  proof -
    have "(upper (effect_skew E) mod modulus * (int x mod modulus) +
        offset (effect_skew E) mod modulus) mod modulus =
        ((upper (effect_skew E) mod modulus * (int x mod modulus)) mod modulus +
          offset (effect_skew E) mod modulus) mod modulus"
      by (simp only: mod_add_left_eq)
    also have "\<dots> = ((upper (effect_skew E) * int x) mod modulus +
        offset (effect_skew E) mod modulus) mod modulus"
      by (simp only: mod_mult_eq)
    also have "\<dots> = (upper (effect_skew E) * int x +
        offset (effect_skew E)) mod modulus"
      by (rule mod_add_eq)
    finally show ?thesis .
  qed
  show ?thesis
    by (subst reduced)
      (simp add: equation denominator modulus_def power_add mod_mult_mult1)
qed

text \<open>Source words appear only in the semantic specification. The
executable leaf and postorder machine carry the complete numeric effect,
including the signed prefix minimum, without retaining that word.\<close>

end

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms effect_then_assoc effect_then_identity effect_then_admitted
      dyadic_arithmetic_constructor.arithmetic_leaf_correct
      dyadic_arithmetic_constructor.balanced_spec_source_effect
      dyadic_arithmetic_constructor.execute_balanced_source_effect
      dyadic_arithmetic_constructor.construct_source_effect_correct
      dyadic_arithmetic_constructor.construct_source_effect_endpoint
      dyadic_arithmetic_constructor.execute_balanced_endpoint
      dyadic_arithmetic_constructor.execute_balanced_prefix_safety
      dyadic_arithmetic_constructor.source_effect_reduced_numerator})
    then () else error "Balanced arithmetic refinement depends on an oracle";
\<close>
end
