theory Collatz_Physical_Cylinder_Lift
  imports Collatz_Cylinder_Constructor
    Shared_S_Arithmetic.Dyadic_Source_Lift
begin

text \<open>This theory gives a source-derived finite physical Collatz
cylinder lift.  The branch word is computed from the exact source; it is not a
supplied itinerary.  A cylinder with at least one remaining dyadic digit has
the same next parity as its source representative.  Even steps consume one
digit and odd steps multiply the source displacement by three without
consuming a digit.

The results concern a finite number of physical steps only.  They assert no
Collatz convergence, no logarithmic source-discovery cost, and no refinement
of a particular Python scheduler or cache.\<close>

fun collatz_physical_branch_word :: "nat \<Rightarrow> nat \<Rightarrow> bool list" where
  "collatz_physical_branch_word 0 x = []"
| "collatz_physical_branch_word (Suc n) x =
    odd x # collatz_physical_branch_word n (physical_collatz x)"

definition collatz_physical_odd_count :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "collatz_physical_odd_count n x =
    count_list (collatz_physical_branch_word n x) True"

definition collatz_physical_even_count :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "collatz_physical_even_count n x =
    count_list (collatz_physical_branch_word n x) False"

lemma collatz_physical_branch_word_length [simp]:
  "length (collatz_physical_branch_word n x) = n"
  by (induction n arbitrary: x) simp_all

lemma collatz_physical_counts_partition:
  "collatz_physical_odd_count n x + collatz_physical_even_count n x = n"
proof (induction n arbitrary: x)
  case 0
  then show ?case
    by (simp add: collatz_physical_odd_count_def
        collatz_physical_even_count_def)
next
  case (Suc n)
  show ?case
  proof (cases "odd x")
    case True
    then show ?thesis using Suc.IH[of "physical_collatz x"]
      by (simp add: collatz_physical_odd_count_def
          collatz_physical_even_count_def)
  next
    case False
    then show ?thesis using Suc.IH[of "physical_collatz x"]
      by (simp add: collatz_physical_odd_count_def
          collatz_physical_even_count_def)
  qed
qed

corollary collatz_physical_even_count_le:
  "collatz_physical_even_count n x \<le> n"
  using collatz_physical_counts_partition[of n x] by arith

corollary collatz_physical_odd_count_le:
  "collatz_physical_odd_count n x \<le> n"
  using collatz_physical_counts_partition[of n x] by arith

lemma physical_collatz_even_cylinder_step:
  assumes source_even: "even r" and precision: "0 < p"
  shows "physical_collatz (r + 2^p*k) =
    physical_collatz r + 2^(p-1)*k"
proof -
  obtain a where r: "r = 2*a"
    using source_even by (elim evenE)
  obtain q where p: "p = Suc q"
    using precision by (cases p) auto
  show ?thesis
    by (simp add: r p physical_collatz_def power_Suc algebra_simps)
qed

lemma physical_collatz_odd_cylinder_step:
  assumes source_odd: "odd r" and precision: "0 < p"
  shows "physical_collatz (r + 2^p*k) =
    physical_collatz r + 2^p*(3*k)"
proof -
  obtain q where p: "p = Suc q"
    using precision by (cases p) auto
  show ?thesis using source_odd
    by (simp add: p physical_collatz_def power_Suc algebra_simps)
qed

definition collatz_physical_gain :: "bool \<Rightarrow> nat" where
  "collatz_physical_gain branch = (if branch then 6 else 1)"

lemma physical_collatz_dyadic_label_translation:
  "odd (source + 2*lift_amount) = odd source"
  by simp

lemma physical_collatz_dyadic_step_translation:
  "physical_collatz (source + 2*lift_amount) =
    physical_collatz source +
      collatz_physical_gain (odd source) * lift_amount"
proof (cases "even source")
  case True
  show ?thesis
    using physical_collatz_even_cylinder_step[of source 1 lift_amount]
      True by (simp add: collatz_physical_gain_def)
next
  case False
  then have source_odd: "odd source" by simp
  have argument:
      "source + 2*lift_amount = source + 2^1*lift_amount"
    by simp
  have translated:
      "physical_collatz (source + 2^1*lift_amount) =
       physical_collatz source + 2^1*(3*lift_amount)"
    by (rule physical_collatz_odd_cylinder_step[OF source_odd]) simp
  have "physical_collatz (source + 2*lift_amount) =
      physical_collatz (source + 2^1*lift_amount)"
    by (rule arg_cong[OF argument])
  also have "... = physical_collatz source + 2^1*(3*lift_amount)"
    by (rule translated)
  also have "... = physical_collatz source +
      collatz_physical_gain (odd source) * lift_amount"
    using source_odd
    by (simp add: collatz_physical_gain_def algebra_simps)
  finally show ?thesis .
qed

interpretation collatz_physical_dyadic_source: dyadic_source_action
    physical_collatz odd collatz_physical_gain
proof
  show "\<And>(source::nat) (lift_amount::nat).
      odd (source + 2 * lift_amount) = odd source"
    by (rule physical_collatz_dyadic_label_translation)
  show "\<And>(source::nat) (lift_amount::nat).
      physical_collatz (source + 2 * lift_amount) =
      physical_collatz source +
        collatz_physical_gain (odd source) * lift_amount"
    by (rule physical_collatz_dyadic_step_translation)
qed

lemma collatz_physical_branch_word_is_dyadic_source_word:
  "collatz_physical_branch_word n source =
    dyadic_source_word physical_collatz odd source n"
  by (induction n arbitrary: source) simp_all

lemma collatz_physical_gain_product:
  "dyadic_gain_product collatz_physical_gain
      (collatz_physical_branch_word n source) =
    6^(collatz_physical_odd_count n source)"
proof (induction n arbitrary: source)
  case 0
  then show ?case
    by (simp add: dyadic_gain_product_def
        collatz_physical_odd_count_def)
next
  case (Suc n)
  show ?case
  proof (cases "odd source")
    case True
    then show ?thesis using Suc.IH[of "physical_collatz source"]
      by (simp add: dyadic_gain_product_def collatz_physical_gain_def
          collatz_physical_odd_count_def power_Suc algebra_simps)
  next
    case False
    then show ?thesis using Suc.IH[of "physical_collatz source"]
      by (simp add: dyadic_gain_product_def collatz_physical_gain_def
          collatz_physical_odd_count_def)
  qed
qed

theorem collatz_physical_source_cylinder_lift:
  assumes precision: "n \<le> p"
  shows
    "collatz_physical_branch_word n (r + 2^p*k) =
       collatz_physical_branch_word n r \<and>
     (physical_collatz ^^ n) (r + 2^p*k) =
       (physical_collatz ^^ n) r +
       3^(collatz_physical_odd_count n r) *
       2^(p - collatz_physical_even_count n r) * k"
proof -
  obtain extra where p: "p = n+extra"
    using precision by (metis le_iff_add)
  note shared =
    collatz_physical_dyadic_source.source_lift_with_extra_precision[
      of r n extra k]
  have word:
      "collatz_physical_branch_word n (r + 2^p*k) =
       collatz_physical_branch_word n r"
    using shared p
    by (simp add: collatz_physical_branch_word_is_dyadic_source_word)
  have endpoint:
      "(physical_collatz ^^ n) (r + 2^p*k) =
       (physical_collatz ^^ n) r +
       2^extra * 6^(collatz_physical_odd_count n r) * k"
    using shared p collatz_physical_gain_product[of n r]
    by (simp add: collatz_physical_branch_word_is_dyadic_source_word
        dyadic_source_orbit_funpow)
  have exponent:
      "p - collatz_physical_even_count n r =
       extra + collatz_physical_odd_count n r"
    using collatz_physical_counts_partition[of n r] p by arith
  have coefficient:
      "(2::nat)^extra * 6^(collatz_physical_odd_count n r) =
       (3::nat)^(collatz_physical_odd_count n r) *
        2^(p - collatz_physical_even_count n r)"
  proof -
    have six_power:
        "(6::nat)^(collatz_physical_odd_count n r) =
         3^(collatz_physical_odd_count n r) *
          2^(collatz_physical_odd_count n r)"
    proof -
      have "(6::nat)^(collatz_physical_odd_count n r) =
          (3*2)^(collatz_physical_odd_count n r)"
        by simp
      also have "... = 3^(collatz_physical_odd_count n r) *
          2^(collatz_physical_odd_count n r)"
        by (rule power_mult_distrib)
      finally show ?thesis .
    qed
    show ?thesis using exponent six_power
      by (simp add: power_add algebra_simps)
  qed
  show ?thesis using word endpoint coefficient by simp
qed

corollary collatz_physical_exact_precision_lift:
  "collatz_physical_branch_word n (r + 2^n*k) =
       collatz_physical_branch_word n r \<and>
   (physical_collatz ^^ n) (r + 2^n*k) =
       (physical_collatz ^^ n) r +
       3^(collatz_physical_odd_count n r) *
       2^(n - collatz_physical_even_count n r) * k"
  by (rule collatz_physical_source_cylinder_lift) simp

corollary collatz_physical_exact_precision_gain:
  "(physical_collatz ^^ n) (r + 2^n*k) =
       (physical_collatz ^^ n) r +
       3^(collatz_physical_odd_count n r) *
       2^(collatz_physical_odd_count n r) * k"
proof -
  have exponent:
    "n - collatz_physical_even_count n r =
      collatz_physical_odd_count n r"
    using collatz_physical_counts_partition[of n r] by arith
  show ?thesis
    using collatz_physical_exact_precision_lift[of n r k] exponent by simp
qed

section \<open>Source-derived affine leaf and balanced remainder transport\<close>

fun collatz_physical_affine_offset :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "collatz_physical_affine_offset 0 x = 0"
| "collatz_physical_affine_offset (Suc n) x =
    (if odd x then
       3^(collatz_physical_odd_count n (physical_collatz x)) +
         collatz_physical_affine_offset n (physical_collatz x)
     else 2 * collatz_physical_affine_offset n (physical_collatz x))"

theorem collatz_physical_source_affine:
  "2^(collatz_physical_even_count n x) * (physical_collatz ^^ n) x =
    3^(collatz_physical_odd_count n x) * x +
      collatz_physical_affine_offset n x"
proof (induction n arbitrary: x)
  case 0
  then show ?case
    by (simp add: collatz_physical_odd_count_def
        collatz_physical_even_count_def)
next
  case (Suc n)
  show ?case
  proof (cases "odd x")
    case True
    show ?thesis using Suc.IH[of "physical_collatz x"] True
      by (simp del: funpow.simps(2)
          add: funpow_Suc_right physical_collatz_def
            collatz_physical_odd_count_def collatz_physical_even_count_def
            power_Suc algebra_simps)
  next
    case False
    have source_even: "even x" using False by simp
    have source_split: "x = 2 * (x div 2)" using source_even by simp
    show ?thesis using Suc.IH[of "physical_collatz x"] False source_split
      by (simp del: funpow.simps(2)
          add: funpow_Suc_right physical_collatz_def
            collatz_physical_odd_count_def collatz_physical_even_count_def
            power_Suc algebra_simps)
  qed
qed

definition collatz_physical_transport_residue ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "collatz_physical_transport_residue first precision source =
    (((physical_collatz ^^ first) (source mod 2^first) +
      3^(collatz_physical_odd_count first (source mod 2^first)) *
      2^(collatz_physical_odd_count first (source mod 2^first)) *
        (source div 2^first)) mod 2^precision)"

theorem collatz_physical_low_residue_transport:
  "collatz_physical_branch_word first source =
      collatz_physical_branch_word first (source mod 2^first) \<and>
   collatz_physical_transport_residue first precision source =
      (physical_collatz ^^ first) source mod 2^precision"
proof -
  let ?low = "source mod 2^first"
  let ?high = "source div 2^first"
  have source_decomposition: "source = ?low + 2^first * ?high"
    using mod_mult_div_eq[of source "2^first"] by simp
  note lift = collatz_physical_exact_precision_gain[of first ?low ?high]
  note branches = collatz_physical_exact_precision_lift[of first ?low ?high]
  show ?thesis
    using lift branches source_decomposition
    by (simp add: collatz_physical_transport_residue_def)
qed

lemma collatz_physical_branch_word_add:
  "collatz_physical_branch_word (first+second) source =
    collatz_physical_branch_word first source @
      collatz_physical_branch_word second
        ((physical_collatz ^^ first) source)"
proof (induction first arbitrary: source)
  case 0
  then show ?case by simp
next
  case (Suc first)
  show ?case using Suc.IH[of "physical_collatz source"]
    by (simp del: funpow.simps(2) add: funpow_Suc_right)
qed

theorem collatz_physical_balanced_selector_split:
  "collatz_physical_branch_word (first+second) source =
    collatz_physical_branch_word first (source mod 2^first) @
      collatz_physical_branch_word second
        (collatz_physical_transport_residue first second source)"
proof -
  let ?middle = "(physical_collatz ^^ first) source"
  let ?residue = "collatz_physical_transport_residue first second source"
  have first_word:
      "collatz_physical_branch_word first source =
       collatz_physical_branch_word first (source mod 2^first)"
    using collatz_physical_low_residue_transport[of first source second]
    by blast
  have residue: "?residue = ?middle mod 2^second"
    using collatz_physical_low_residue_transport[of first source second]
    by blast
  have middle_decomposition:
      "?middle = ?residue + 2^second * (?middle div 2^second)"
    using mod_mult_div_eq[of ?middle "2^second"] residue by simp
  have second_word:
      "collatz_physical_branch_word second ?middle =
       collatz_physical_branch_word second ?residue"
    using collatz_physical_exact_precision_lift[
        of second ?residue "?middle div 2^second"]
      middle_decomposition by simp
  show ?thesis
    using collatz_physical_branch_word_add[of first second source]
      first_word second_word by simp
qed

corollary collatz_physical_affine_leaf_division:
  "(physical_collatz ^^ n) x =
    (3^(collatz_physical_odd_count n x) * x +
      collatz_physical_affine_offset n x) div
        2^(collatz_physical_even_count n x)"
proof -
  have equation:
      "3^(collatz_physical_odd_count n x) * x +
        collatz_physical_affine_offset n x =
       2^(collatz_physical_even_count n x) *
        (physical_collatz ^^ n) x"
    using collatz_physical_source_affine[of n x] by (rule sym)
  show ?thesis
    by (subst equation) simp
qed

text \<open>The exact-precision theorem is the finite demanded-precision
split: its branch word is derived from the representative r, and every source
in r plus 2^n times the naturals follows that word for n physical steps.  A
production refinement must still connect this representative and precision to
an authenticated source image, construct balanced shared skew transfers, and
account for discovery, composition, publication, and retained storage.\<close>

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms collatz_physical_branch_word_length
      collatz_physical_counts_partition collatz_physical_even_count_le
      collatz_physical_odd_count_le physical_collatz_even_cylinder_step
      physical_collatz_odd_cylinder_step
      collatz_physical_source_cylinder_lift
      collatz_physical_exact_precision_lift
      collatz_physical_exact_precision_gain
      collatz_physical_source_affine
      collatz_physical_low_residue_transport
      collatz_physical_branch_word_add
      collatz_physical_balanced_selector_split
      collatz_physical_affine_leaf_division})
    then () else error "Physical Collatz cylinder lift depends on an oracle";
\<close>

end
