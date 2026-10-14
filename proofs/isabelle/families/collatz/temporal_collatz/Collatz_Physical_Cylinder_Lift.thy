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

text \<open>A normalized field-action symbol represents one physical tick on an
even source and the odd tick followed by its forced even tick on an odd
source.  The guard below validates each supplied symbol against the exact
current natural source before advancing that normalized occurrence.  It is a
finite-word refinement only; it does not discover future parity words or
refine a Python cache/parser.\<close>

definition collatz_guarded_normalized_source_step :: "bool \<Rightarrow> nat \<Rightarrow> nat" where
  "collatz_guarded_normalized_source_step branch x =
    (if branch then (physical_collatz ^^ 2) x else physical_collatz x)"

fun collatz_guarded_normalized_word_admitted :: "bool list \<Rightarrow> nat \<Rightarrow> bool" where
  "collatz_guarded_normalized_word_admitted [] x = True"
| "collatz_guarded_normalized_word_admitted (branch # tail) x =
    (branch = odd x \<and>
      collatz_guarded_normalized_word_admitted tail
        (collatz_guarded_normalized_source_step branch x))"

fun collatz_guarded_normalized_word_endpoint :: "bool list \<Rightarrow> nat \<Rightarrow> nat" where
  "collatz_guarded_normalized_word_endpoint [] x = x"
| "collatz_guarded_normalized_word_endpoint (branch # tail) x =
    collatz_guarded_normalized_word_endpoint tail
      (collatz_guarded_normalized_source_step branch x)"

lemma collatz_guarded_normalized_atom_exact:
  assumes branch: "branch = odd x"
  shows "collatz_joint_dyadic_endpoint (collatz_joint_dyadic_atom branch)
      (of_nat x) = of_nat (collatz_guarded_normalized_source_step branch x)"
proof -
  have normalized:
    "collatz_joint_dyadic_endpoint (collatz_joint_dyadic_atom branch)
        (of_nat x) = collatz_normalized_bit_step branch (of_nat x)"
    using collatz_joint_dyadic_word_endpoint_exact[of "[branch]" "of_nat x"]
    by simp
  show ?thesis
  proof (cases branch)
    case True
    have odd_x: "odd x" using branch True by simp
    have even_next: "even (3*x+1)" using odd_x by simp
    obtain q where q: "3*x+1 = 2*q"
      using even_next by (rule evenE)
    have cast_q: "(3::rat) * of_nat x + 1 = (2::rat) * of_nat q"
    proof -
      have cast_equality:
        "(of_nat (3*x+1) :: rat) = (of_nat (2*q) :: rat)"
        using q by simp
      show ?thesis using cast_equality by simp
    qed
    have source_step:
      "collatz_guarded_normalized_source_step True x = q"
    proof -
      have q': "3*x+1 = 2*q" using q by simp
      have first_tick: "physical_collatz x = 3*x+1"
        using odd_x by (simp add: physical_collatz_def)
      have second_tick: "physical_collatz (3*x+1) = q"
        using even_next q' by (simp add: physical_collatz_def)
      have two: "(2::nat) = Suc (Suc 0)" by simp
      have iterate_two:
        "(physical_collatz ^^ 2) x =
          physical_collatz (physical_collatz x)"
        by (simp only: two funpow.simps comp_apply id_apply)
      show ?thesis
        unfolding collatz_guarded_normalized_source_step_def
        using first_tick second_tick iterate_two
        by (simp only: if_True iterate_two first_tick second_tick)
    qed
    show ?thesis
      using normalized cast_q source_step True
      by (simp add: collatz_normalized_bit_step_def)
  next
    case False
    have even_x: "even x" using branch False by simp
    obtain q where q: "x = 2*q" using even_x by (auto elim: evenE)
    have cast_q: "of_nat x = (2::rat) * of_nat q" using q by simp
    have source_step:
      "collatz_guarded_normalized_source_step False x = q"
      using q by (simp add: collatz_guarded_normalized_source_step_def
          physical_collatz_def)
    show ?thesis
      using normalized cast_q source_step False
      by (simp add: collatz_normalized_bit_step_def)
  qed
qed

theorem collatz_guarded_normalized_word_refines_physical:
  assumes admitted: "collatz_guarded_normalized_word_admitted bits source"
  shows "collatz_joint_dyadic_endpoint (collatz_joint_dyadic_word bits)
      (of_nat source) =
        of_nat (collatz_guarded_normalized_word_endpoint bits source) \<and>
    collatz_guarded_normalized_word_endpoint bits source =
      (physical_collatz ^^ (length bits + count_list bits True)) source"
using admitted
proof (induction bits arbitrary: source)
  case Nil
  then show ?case
    by (simp add: collatz_joint_dyadic_endpoint_def
        collatz_joint_dyadic_identity_def)
next
  case (Cons branch tail)
  have split_guard:
    "branch = odd source \<and>
      collatz_guarded_normalized_word_admitted tail
        (collatz_guarded_normalized_source_step branch source)"
    using Cons.prems[unfolded
      collatz_guarded_normalized_word_admitted.simps] .
  have branch: "branch = odd source" using split_guard by blast
  have tail_admitted:
    "collatz_guarded_normalized_word_admitted tail
      (collatz_guarded_normalized_source_step branch source)"
    using split_guard by blast
  have tail_exact:
    "collatz_joint_dyadic_endpoint (collatz_joint_dyadic_word tail)
        (of_nat (collatz_guarded_normalized_source_step branch source)) =
          of_nat (collatz_guarded_normalized_word_endpoint tail
            (collatz_guarded_normalized_source_step branch source)) \<and>
     collatz_guarded_normalized_word_endpoint tail
        (collatz_guarded_normalized_source_step branch source) =
       (physical_collatz ^^ (length tail + count_list tail True))
        (collatz_guarded_normalized_source_step branch source)"
    by (rule Cons.IH[OF tail_admitted])
  have head_action:
    "collatz_joint_dyadic_endpoint (collatz_joint_dyadic_atom branch)
        (of_nat source) =
      of_nat (collatz_guarded_normalized_source_step branch source)"
    by (rule collatz_guarded_normalized_atom_exact[OF branch])
  have duration:
    "length (branch # tail) + count_list (branch # tail) True =
      (if branch then 2 else 1) + (length tail + count_list tail True)"
    by (cases branch) simp_all
  have head_ticks:
    "(physical_collatz ^^ (if branch then 2 else 1)) source =
      collatz_guarded_normalized_source_step branch source"
    by (simp add: collatz_guarded_normalized_source_step_def)
  have tail_ticks:
    "collatz_guarded_normalized_word_endpoint tail
        (collatz_guarded_normalized_source_step branch source) =
      (physical_collatz ^^ (length tail + count_list tail True))
        (collatz_guarded_normalized_source_step branch source)"
    using tail_exact by blast
  show ?case
  proof
    show "collatz_joint_dyadic_endpoint
        (collatz_joint_dyadic_word (branch # tail)) (of_nat source) =
        of_nat (collatz_guarded_normalized_word_endpoint (branch # tail) source)"
      using head_action tail_exact
      by (simp only: collatz_joint_dyadic_word.simps
          collatz_joint_dyadic_endpoint_then
          collatz_guarded_normalized_word_endpoint.simps)
    show "collatz_guarded_normalized_word_endpoint (branch # tail) source =
        (physical_collatz ^^
          (length (branch # tail) + count_list (branch # tail) True)) source"
    proof -
      have combine:
        "(physical_collatz ^^ (length tail + count_list tail True))
            (collatz_guarded_normalized_source_step branch source) =
          (physical_collatz ^^
            ((length tail + count_list tail True) +
              (if branch then 2 else 1))) source"
        using head_ticks by (simp add: funpow_add)
      show ?thesis
      proof -
        have "collatz_guarded_normalized_word_endpoint (branch # tail) source =
          collatz_guarded_normalized_word_endpoint tail
            (collatz_guarded_normalized_source_step branch source)"
          by (simp only: collatz_guarded_normalized_word_endpoint.simps)
        also have "... =
          (physical_collatz ^^ (length tail + count_list tail True))
            (collatz_guarded_normalized_source_step branch source)"
          by (rule tail_ticks)
        also have "... =
          (physical_collatz ^^
            ((length tail + count_list tail True) +
              (if branch then 2 else 1))) source"
          by (rule combine)
        also have "... =
          (physical_collatz ^^
            ((if branch then 2 else 1) +
              (length tail + count_list tail True))) source"
          by (simp add: add.commute)
        also have "... =
          (physical_collatz ^^
            (length (branch # tail) + count_list (branch # tail) True)) source"
          using duration by simp
        finally show ?thesis .
      qed
    qed
  qed
qed

text \<open>Guarded words compose only at the exact source endpoint.  These
lemmas expose the chronological seam used by source-certified temporal
programs; they do not authorize repeating a word at an unrelated source.\<close>

lemma collatz_guarded_normalized_word_admitted_append:
  "collatz_guarded_normalized_word_admitted (first @ second) source \<longleftrightarrow>
    collatz_guarded_normalized_word_admitted first source \<and>
    collatz_guarded_normalized_word_admitted second
      (collatz_guarded_normalized_word_endpoint first source)"
proof (induction first arbitrary: source)
  case Nil
  then show ?case by simp
next
  case (Cons branch tail)
  then show ?case by simp
qed

lemma collatz_guarded_normalized_word_endpoint_append:
  "collatz_guarded_normalized_word_endpoint (first @ second) source =
    collatz_guarded_normalized_word_endpoint second
      (collatz_guarded_normalized_word_endpoint first source)"
  by (induction first arbitrary: source) simp_all

fun collatz_guarded_normalized_successors :: "bool list \<Rightarrow> nat \<Rightarrow> nat list" where
  "collatz_guarded_normalized_successors [] source = []"
| "collatz_guarded_normalized_successors (branch # tail) source =
    collatz_guarded_normalized_source_step branch source #
      collatz_guarded_normalized_successors tail
        (collatz_guarded_normalized_source_step branch source)"

lemma collatz_joint_dyadic_atom_sum_endpoint:
  "collatz_joint_dyadic_sum (collatz_joint_dyadic_atom branch) x =
    collatz_joint_dyadic_endpoint (collatz_joint_dyadic_atom branch) x"
  by (cases branch)
    (simp_all add: collatz_joint_dyadic_sum_def
      collatz_joint_dyadic_endpoint_def collatz_joint_dyadic_atom_def)

theorem collatz_guarded_joint_action_sums_source_successors:
  assumes admitted: "collatz_guarded_normalized_word_admitted bits source"
  shows "collatz_joint_dyadic_sum (collatz_joint_dyadic_word bits)
      (of_nat source) =
    of_nat (sum_list (collatz_guarded_normalized_successors bits source))"
using admitted
proof (induction bits arbitrary: source)
  case Nil
  then show ?case
    by (simp add: collatz_joint_dyadic_sum_def
      collatz_joint_dyadic_identity_def)
next
  case (Cons branch tail)
  have split_guard:
    "branch = odd source \<and>
      collatz_guarded_normalized_word_admitted tail
        (collatz_guarded_normalized_source_step branch source)"
    using Cons.prems[unfolded
      collatz_guarded_normalized_word_admitted.simps] .
  have branch: "branch = odd source" using split_guard by blast
  have tail_admitted:
    "collatz_guarded_normalized_word_admitted tail
      (collatz_guarded_normalized_source_step branch source)"
    using split_guard by blast
  have tail_sum:
    "collatz_joint_dyadic_sum (collatz_joint_dyadic_word tail)
        (of_nat (collatz_guarded_normalized_source_step branch source)) =
      of_nat (sum_list (collatz_guarded_normalized_successors tail
        (collatz_guarded_normalized_source_step branch source)))"
    by (rule Cons.IH[OF tail_admitted])
  have head_endpoint:
    "collatz_joint_dyadic_endpoint (collatz_joint_dyadic_atom branch)
        (of_nat source) =
      of_nat (collatz_guarded_normalized_source_step branch source)"
    by (rule collatz_guarded_normalized_atom_exact[OF branch])
  have head_sum:
    "collatz_joint_dyadic_sum (collatz_joint_dyadic_atom branch)
        (of_nat source) =
      of_nat (collatz_guarded_normalized_source_step branch source)"
  proof -
    have action_eq:
      "collatz_joint_dyadic_sum (collatz_joint_dyadic_atom branch)
          (of_nat source) =
       collatz_joint_dyadic_endpoint (collatz_joint_dyadic_atom branch)
          (of_nat source)"
      by (rule collatz_joint_dyadic_atom_sum_endpoint)
    also have "... =
        of_nat (collatz_guarded_normalized_source_step branch source)"
      by (rule head_endpoint)
    finally show ?thesis .
  qed
  show ?case
    using head_sum head_endpoint tail_sum
    by (simp only: collatz_joint_dyadic_word.simps
      collatz_joint_dyadic_sum_then collatz_guarded_normalized_successors.simps
      sum_list.Cons of_nat_add)
qed

theorem collatz_guarded_normalized_word_physical_endpoint_with_pending_tick:
  assumes admitted: "collatz_guarded_normalized_word_admitted bits source"
    and pending: "pending = odd (collatz_guarded_normalized_word_endpoint bits source)"
  shows "of_nat ((physical_collatz ^^
      (length bits + count_list bits True + (if pending then 1 else 0))) source) =
    (if pending then
      3 * collatz_joint_dyadic_endpoint (collatz_joint_dyadic_word bits)
        (of_nat source) + 1
     else collatz_joint_dyadic_endpoint (collatz_joint_dyadic_word bits)
        (of_nat source))"
proof (cases pending)
  case False
  have exact:
    "collatz_joint_dyadic_endpoint (collatz_joint_dyadic_word bits)
        (of_nat source) =
      of_nat (collatz_guarded_normalized_word_endpoint bits source)"
    using collatz_guarded_normalized_word_refines_physical[OF admitted]
    by blast
  have endpoint_value:
    "collatz_guarded_normalized_word_endpoint bits source =
      (physical_collatz ^^
        (length bits + count_list bits True)) source"
    using collatz_guarded_normalized_word_refines_physical[OF admitted]
    by blast
  show ?thesis using exact endpoint_value False by simp
next
  case True
  let ?duration = "length bits + count_list bits True"
  have exact:
    "collatz_joint_dyadic_endpoint (collatz_joint_dyadic_word bits)
        (of_nat source) =
      of_nat (collatz_guarded_normalized_word_endpoint bits source)"
    using collatz_guarded_normalized_word_refines_physical[OF admitted]
    by blast
  have endpoint_odd:
    "odd ((physical_collatz ^^ ?duration) source)"
  proof -
    have endpoint_value:
      "collatz_guarded_normalized_word_endpoint bits source =
        (physical_collatz ^^ ?duration) source"
      using collatz_guarded_normalized_word_refines_physical[OF admitted]
      by blast
    show ?thesis using True pending endpoint_value by simp
  qed
  have final_tick:
    "(physical_collatz ^^ (?duration + 1)) source =
      3 * (physical_collatz ^^ ?duration) source + 1"
    using endpoint_odd
  proof -
    have iteration:
      "(physical_collatz ^^ (?duration + 1)) source =
        physical_collatz ((physical_collatz ^^ ?duration) source)"
      by (simp add: funpow_add)
    show ?thesis using iteration endpoint_odd
      by (simp add: physical_collatz_def)
  qed
  have endpoint_value:
    "(physical_collatz ^^ ?duration) source =
      collatz_guarded_normalized_word_endpoint bits source"
  proof -
    have forward:
      "collatz_guarded_normalized_word_endpoint bits source =
        (physical_collatz ^^ ?duration) source"
      using collatz_guarded_normalized_word_refines_physical[OF admitted]
      by blast
    show ?thesis by (rule sym[OF forward])
  qed
  show ?thesis using final_tick endpoint_value exact True
    by (simp add: of_nat_mult of_nat_add)
qed

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

section \<open>Bounded production leaf loop\<close>

text \<open>The Python residue macro now evaluates at most four literal generator
steps before the chronological worklist composes larger blocks. This record
models those generator fields, including the exact skew numerator and
denominator. Its proof concerns a bounded source residue; it does not assert
that discovering all later residues is sublinear.\<close>

record collatz_physical_leaf_state =
  physical_leaf_current :: nat
  physical_leaf_skew :: "nat skew_transfer"
  physical_leaf_labels :: "bool list"
  physical_leaf_odd_count :: nat
  physical_leaf_delta :: int
  physical_leaf_minimum :: int

definition collatz_physical_leaf_initial ::
    "nat \<Rightarrow> collatz_physical_leaf_state" where
  "collatz_physical_leaf_initial source = \<lparr>
    physical_leaf_current = source,
    physical_leaf_skew = shared_skew_identity,
    physical_leaf_labels = [],
    physical_leaf_odd_count = 0,
    physical_leaf_delta = 0,
    physical_leaf_minimum = 0\<rparr>"

definition collatz_physical_leaf_step ::
    "collatz_physical_leaf_state \<Rightarrow> collatz_physical_leaf_state" where
  "collatz_physical_leaf_step state =
    (let q = physical_leaf_current state;
         b = odd q;
         generator = \<lparr>upper = collatz_physical_gain b,
           offset = (if b then 2 else 0), lower = 2\<rparr>
     in \<lparr>
       physical_leaf_current = physical_collatz q,
       physical_leaf_skew = shared_skew_then (physical_leaf_skew state) generator,
       physical_leaf_labels = physical_leaf_labels state @ [b],
       physical_leaf_odd_count = physical_leaf_odd_count state + (if b then 1 else 0),
       physical_leaf_delta = physical_leaf_delta state + (if b then 1 else 0),
       physical_leaf_minimum = min (physical_leaf_minimum state)
         (physical_leaf_delta state + (if b then 1 else 0))\<rparr>)"

fun collatz_physical_admitted_leaf_loop ::
    "nat \<Rightarrow> nat \<Rightarrow> collatz_physical_leaf_state" where
  "collatz_physical_admitted_leaf_loop source 0 =
    collatz_physical_leaf_initial source"
| "collatz_physical_admitted_leaf_loop source (Suc n) =
    collatz_physical_leaf_step (collatz_physical_admitted_leaf_loop source n)"

lemma collatz_physical_generator_skew:
  "collatz_physical_gain (odd q) * q + (if odd q then 2 else 0) =
    2 * physical_collatz q"
proof (cases "odd q")
  case True
  then show ?thesis
    by (simp add: collatz_physical_gain_def physical_collatz_def)
next
  case False
  then have "q = 2 * (q div 2)" by simp
  with False show ?thesis
    by (simp add: collatz_physical_gain_def physical_collatz_def)
qed

lemma collatz_physical_branch_word_Suc_right:
  "collatz_physical_branch_word (Suc n) source =
    collatz_physical_branch_word n source @
      [odd ((physical_collatz ^^ n) source)]"
  using collatz_physical_branch_word_add[of n 1 source]
  by simp

theorem collatz_physical_admitted_leaf_loop_refinement:
  fixes source n :: nat
  defines "state \<equiv> collatz_physical_admitted_leaf_loop source n"
  shows "physical_leaf_current state = (physical_collatz ^^ n) source"
    and "physical_leaf_labels state =
      collatz_physical_branch_word n source"
    and "lower (physical_leaf_skew state) = 2^n"
    and "upper (physical_leaf_skew state) =
      dyadic_gain_product collatz_physical_gain
        (collatz_physical_branch_word n source)"
    and "physical_leaf_odd_count state =
      collatz_physical_odd_count n source"
    and "physical_leaf_delta state =
      int (collatz_physical_odd_count n source)"
    and "physical_leaf_minimum state = 0"
    and "upper (physical_leaf_skew state) * source +
      offset (physical_leaf_skew state) =
      lower (physical_leaf_skew state) * physical_leaf_current state"
proof -
  have invariant: "
    physical_leaf_current (collatz_physical_admitted_leaf_loop source k) =
      (physical_collatz ^^ k) source \<and>
    physical_leaf_labels (collatz_physical_admitted_leaf_loop source k) =
      collatz_physical_branch_word k source \<and>
    lower (physical_leaf_skew (collatz_physical_admitted_leaf_loop source k)) = 2^k \<and>
    upper (physical_leaf_skew (collatz_physical_admitted_leaf_loop source k)) =
      dyadic_gain_product collatz_physical_gain
        (collatz_physical_branch_word k source) \<and>
    physical_leaf_odd_count (collatz_physical_admitted_leaf_loop source k) =
      collatz_physical_odd_count k source \<and>
    physical_leaf_delta (collatz_physical_admitted_leaf_loop source k) =
      int (collatz_physical_odd_count k source) \<and>
    physical_leaf_minimum (collatz_physical_admitted_leaf_loop source k) = 0 \<and>
    upper (physical_leaf_skew (collatz_physical_admitted_leaf_loop source k)) * source +
      offset (physical_leaf_skew (collatz_physical_admitted_leaf_loop source k)) =
      lower (physical_leaf_skew (collatz_physical_admitted_leaf_loop source k)) *
        physical_leaf_current (collatz_physical_admitted_leaf_loop source k)"
    for k
  proof (induction k)
    case 0
    then show ?case
      by (simp add: collatz_physical_leaf_initial_def shared_skew_identity_def
          collatz_physical_odd_count_def dyadic_gain_product_def)
  next
    case (Suc k)
    let ?state = "collatz_physical_admitted_leaf_loop source k"
    let ?q = "physical_leaf_current ?state"
    let ?b = "odd ?q"
    have one_step:
      "collatz_physical_gain ?b * ?q + (if ?b then 2 else 0) =
        2 * physical_collatz ?q"
      by (rule collatz_physical_generator_skew)
    have old:
      "upper (physical_leaf_skew ?state) * source +
        offset (physical_leaf_skew ?state) =
        lower (physical_leaf_skew ?state) * ?q"
      using Suc.IH by blast
    have transport:
      "collatz_physical_gain ?b * upper (physical_leaf_skew ?state) * source +
       collatz_physical_gain ?b * offset (physical_leaf_skew ?state) +
       lower (physical_leaf_skew ?state) * (if ?b then 2 else 0) =
       (2 * lower (physical_leaf_skew ?state)) * physical_collatz ?q"
    proof -
      have "collatz_physical_gain ?b * upper (physical_leaf_skew ?state) * source +
          collatz_physical_gain ?b * offset (physical_leaf_skew ?state) +
          lower (physical_leaf_skew ?state) * (if ?b then 2 else 0) =
        collatz_physical_gain ?b *
          (upper (physical_leaf_skew ?state) * source +
           offset (physical_leaf_skew ?state)) +
          lower (physical_leaf_skew ?state) * (if ?b then 2 else 0)"
        by (simp add: algebra_simps)
      also have "... = lower (physical_leaf_skew ?state) *
          (collatz_physical_gain ?b * ?q + (if ?b then 2 else 0))"
        using old by (simp add: algebra_simps)
      also have "... =
          (2 * lower (physical_leaf_skew ?state)) * physical_collatz ?q"
        using one_step by (simp add: algebra_simps)
      finally show ?thesis .
    qed
    show ?case
      using Suc.IH transport
      by (simp del: collatz_physical_branch_word.simps(2) funpow.simps(2)
          add: collatz_physical_leaf_step_def Let_def
          shared_skew_then_def collatz_physical_branch_word_Suc_right
          collatz_physical_odd_count_def dyadic_gain_product_def
          funpow_Suc_right funpow_swap1 power_Suc algebra_simps)
  qed
  show "physical_leaf_current state = (physical_collatz ^^ n) source"
    using invariant[of n] unfolding state_def by simp
  show "physical_leaf_labels state = collatz_physical_branch_word n source"
    using invariant[of n] unfolding state_def by simp
  show "lower (physical_leaf_skew state) = 2^n"
    using invariant[of n] unfolding state_def by simp
  show "upper (physical_leaf_skew state) =
      dyadic_gain_product collatz_physical_gain
        (collatz_physical_branch_word n source)"
    using invariant[of n] unfolding state_def by simp
  show "physical_leaf_odd_count state = collatz_physical_odd_count n source"
    using invariant[of n] unfolding state_def by simp
  show "physical_leaf_delta state = int (collatz_physical_odd_count n source)"
    using invariant[of n] unfolding state_def by simp
  show "physical_leaf_minimum state = 0"
    using invariant[of n] unfolding state_def by simp
  show "upper (physical_leaf_skew state) * source +
      offset (physical_leaf_skew state) =
      lower (physical_leaf_skew state) * physical_leaf_current state"
    using invariant[of n] unfolding state_def by blast
qed

corollary collatz_physical_d4_base_refinement:
  assumes "n \<le> 4"
  shows "physical_leaf_labels
      (collatz_physical_admitted_leaf_loop residue n) =
        collatz_physical_branch_word n residue"
    and "physical_leaf_delta
      (collatz_physical_admitted_leaf_loop residue n) =
        int (collatz_physical_odd_count n residue)"
    and "physical_leaf_minimum
      (collatz_physical_admitted_leaf_loop residue n) = 0"
    and "upper (physical_leaf_skew
      (collatz_physical_admitted_leaf_loop residue n)) * residue +
      offset (physical_leaf_skew
        (collatz_physical_admitted_leaf_loop residue n)) =
      2^n * (physical_collatz ^^ n) residue"
  using collatz_physical_admitted_leaf_loop_refinement[of residue n]
  by simp_all

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
      collatz_guarded_normalized_atom_exact
      collatz_guarded_normalized_word_refines_physical
      collatz_guarded_normalized_word_admitted_append
      collatz_guarded_normalized_word_endpoint_append
      collatz_joint_dyadic_atom_sum_endpoint
      collatz_guarded_joint_action_sums_source_successors
      collatz_guarded_normalized_word_physical_endpoint_with_pending_tick
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
      collatz_physical_generator_skew
      collatz_physical_branch_word_Suc_right
      collatz_physical_admitted_leaf_loop_refinement
      collatz_physical_d4_base_refinement
      collatz_physical_affine_leaf_division})
    then () else error "Physical Collatz cylinder lift depends on an oracle";
\<close>

end
