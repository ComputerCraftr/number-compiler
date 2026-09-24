theory Collatz_Reduced_Precision
  imports Balanced_Dyadic_Families
begin

text \<open>Finite high-fiber equivalence for the actual physical Collatz law.
An even step consumes one binary source digit; an odd step preserves the
precision while multiplying the high-fiber displacement by three.  The
result is a source-domain theorem about complete finite branch and safety
effects.  It does not intern different source occurrences or implement a
memo reduction in Python.\<close>

lemma collatz_even_count_cons:
  "collatz_physical_even_count (Suc n) x =
    (if even x then Suc (collatz_physical_even_count n (physical_collatz x))
     else collatz_physical_even_count n (physical_collatz x))"
  by (simp add: collatz_physical_even_count_def)

theorem collatz_even_budget_word_shift:
  "collatz_physical_branch_word n
      (x + 2^Suc (collatz_physical_even_count n x) * high) =
    collatz_physical_branch_word n x"
proof (induction n arbitrary: x high)
  case 0
  then show ?case by simp
next
  case (Suc n)
  let ?tail = "physical_collatz x"
  let ?e = "collatz_physical_even_count n ?tail"
  show ?case
  proof (cases "even x")
    case True
    have count: "collatz_physical_even_count (Suc n) x = Suc ?e"
      using True by (simp add: collatz_even_count_cons)
    have same_bit: "odd (x + 2^Suc (collatz_physical_even_count (Suc n) x)
        * high) = odd x"
      by (simp add: power_Suc)
    have next_source:
      "physical_collatz
        (x + 2^Suc (collatz_physical_even_count (Suc n) x) * high) =
       ?tail + 2^Suc ?e * high"
      using physical_collatz_even_cylinder_step[OF True, of
        "Suc (collatz_physical_even_count (Suc n) x)" high]
      by (simp add: count)
    show ?thesis
      using same_bit next_source Suc.IH[of ?tail high] by simp
  next
    case False
    then have source_odd: "odd x" by simp
    have count: "collatz_physical_even_count (Suc n) x = ?e"
      using False by (simp add: collatz_even_count_cons)
    have same_bit: "odd (x + 2^Suc (collatz_physical_even_count (Suc n) x)
        * high) = odd x"
      by (simp add: power_Suc)
    have next_source:
      "physical_collatz
        (x + 2^Suc (collatz_physical_even_count (Suc n) x) * high) =
       ?tail + 2^Suc ?e * (3*high)"
      using physical_collatz_odd_cylinder_step[OF source_odd, of
        "Suc (collatz_physical_even_count (Suc n) x)" high]
      by (simp add: count)
    show ?thesis
      using same_bit next_source Suc.IH[of ?tail "3*high"] by simp
  qed
qed

definition collatz_effect_precision :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "collatz_effect_precision n source =
    min n (Suc (collatz_physical_even_count n source))"

theorem collatz_reduced_precision_branch_word:
  "collatz_physical_branch_word n
      (source + 2^(collatz_effect_precision n source) * high) =
    collatz_physical_branch_word n source"
proof (cases "n \<le> Suc (collatz_physical_even_count n source)")
  case True
  then have precision: "collatz_effect_precision n source = n"
    by (simp add: collatz_effect_precision_def)
  have "dyadic_source_word physical_collatz odd
      (source + 2^n * high) n =
    dyadic_source_word physical_collatz odd source n"
    using collatz_physical_dyadic_source.exact_precision_source_lift
      [of source n high] by simp
  with precision show ?thesis
    by (simp add: collatz_physical_branch_word_is_dyadic_source_word)
next
  case False
  then have precision: "collatz_effect_precision n source =
      Suc (collatz_physical_even_count n source)"
    by (simp add: collatz_effect_precision_def)
  show ?thesis
    using collatz_even_budget_word_shift[of n source high]
    by (simp only: precision)
qed

theorem collatz_reduced_precision_complete_effect:
  "collatz_balanced.source_effect n
      (source + 2^(collatz_effect_precision n source) * high) =
    collatz_balanced.source_effect n source"
  using collatz_reduced_precision_branch_word[of n source high]
  by (simp add: collatz_balanced.source_effect_def
      collatz_physical_branch_word_is_dyadic_source_word)

corollary collatz_reduced_precision_safety_fields:
  "effect_events (collatz_balanced.source_effect n
      (source + 2^(collatz_effect_precision n source) * high)) =
    effect_events (collatz_balanced.source_effect n source)"
  "effect_delta (collatz_balanced.source_effect n
      (source + 2^(collatz_effect_precision n source) * high)) =
    effect_delta (collatz_balanced.source_effect n source)"
  "effect_minimum (collatz_balanced.source_effect n
      (source + 2^(collatz_effect_precision n source) * high)) =
    effect_minimum (collatz_balanced.source_effect n source)"
  using collatz_reduced_precision_complete_effect[of n source high]
  by simp_all

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms collatz_even_count_cons collatz_even_budget_word_shift
      collatz_reduced_precision_branch_word
      collatz_reduced_precision_complete_effect
      collatz_reduced_precision_safety_fields}) then ()
    else error "Collatz reduced-precision proof depends on an oracle";
\<close>

end
