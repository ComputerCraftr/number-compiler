theory Collatz_Physical_One_Cycle
  imports Collatz_Physical_Cylinder_Lift
begin

text \<open>The exact physical Collatz orbit 1,4,2 returns after three
steps.  These lemmas justify a finite-cycle summary only after the executable
constructor has established exact source equality with one of those three
phase states.  Congruence to a phase state at finite precision is deliberately
insufficient.\<close>

definition collatz_one_cycle_phase :: "nat \<Rightarrow> nat" where
  "collatz_one_cycle_phase n =
    (if n mod 3 = 0 then 1 else if n mod 3 = 1 then 4 else 2)"

definition collatz_cycle_admitted :: "nat \<Rightarrow> bool" where
  "collatz_cycle_admitted source \<longleftrightarrow>
    source = 1 \<or> source = 4 \<or> source = 2"

definition collatz_cycle_phase :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "collatz_cycle_phase source n =
    collatz_one_cycle_phase
      (n + (if source = 1 then 0 else if source = 4 then 1 else 2))"

definition collatz_cycle_odd_count :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "collatz_cycle_odd_count source n =
    (if source = 1 then (n+2) div 3
     else if source = 4 then n div 3
     else (n+1) div 3)"

lemma physical_collatz_one_cycle_values [simp]:
  "physical_collatz 1 = 4"
  "physical_collatz 4 = 2"
  "physical_collatz 2 = 1"
  by (simp_all add: physical_collatz_def)

lemma physical_collatz_one_two_steps [simp]:
  "(physical_collatz ^^ 2) 1 = 2"
  by (simp only: numeral_2_eq_2 funpow.simps comp_apply id_apply
      physical_collatz_one_cycle_values)

lemma physical_collatz_one_one_step [simp]:
  "(physical_collatz ^^ 1) 1 = 4"
  by (simp add: physical_collatz_def)

lemma physical_collatz_one_cycle_chunks:
  "(physical_collatz ^^ (3*q)) 1 = 1"
proof (induction q)
  case 0
  then show ?case by simp
next
  case (Suc q)
  have "(physical_collatz ^^ (3 * Suc q)) 1 =
      (physical_collatz ^^ (3*q+3)) 1"
    by (simp add: add.commute)
  also have "... = (physical_collatz ^^ (3*q))
      ((physical_collatz ^^ 3) 1)"
    by (simp only: funpow_add comp_apply)
  also have "... = (physical_collatz ^^ (3*q)) 1"
    using physical_collatz_three_cycle by simp
  also have "... = 1"
    by (rule Suc.IH)
  finally show ?case .
qed

theorem physical_collatz_one_cycle_phase:
  "(physical_collatz ^^ n) 1 = collatz_one_cycle_phase n"
proof -
  let ?q = "n div 3"
  let ?r = "n mod 3"
  have decomposition: "n = 3*?q + ?r"
    using mod_mult_div_eq[of n 3] by (simp add: algebra_simps)
  have remainder: "?r < 3" by simp
  have remainder_cases: "?r = 0 \<or> ?r = 1 \<or> ?r = 2"
    using remainder by arith
  have decomposition_commuted: "n = ?r + 3*?q"
    using decomposition by arith
  have "(physical_collatz ^^ n) 1 =
      (physical_collatz ^^ (?r + 3*?q)) 1"
    by (rule arg_cong[OF decomposition_commuted])
  also have "... =
      (physical_collatz ^^ ?r) ((physical_collatz ^^ (3*?q)) 1)"
    by (simp only: funpow_add comp_apply)
  also have "... = (physical_collatz ^^ ?r) 1"
    by (rule arg_cong[OF physical_collatz_one_cycle_chunks[of ?q]])
  also have "... = collatz_one_cycle_phase n"
  proof -
    from remainder_cases show ?thesis
    proof (elim disjE)
      assume remainder_zero: "?r = 0"
      have left: "(physical_collatz ^^ ?r) 1 = 1"
        using remainder_zero by simp
      have right: "collatz_one_cycle_phase n = 1"
        using remainder_zero by (simp add: collatz_one_cycle_phase_def)
      show ?thesis using left right by simp
    next
      assume remainder_one: "?r = 1"
      have exponent:
          "(physical_collatz ^^ ?r) 1 = (physical_collatz ^^ 1) 1"
        by (rule arg_cong[OF remainder_one])
      have left: "(physical_collatz ^^ ?r) 1 = 4"
        using exponent physical_collatz_one_one_step by simp
      have right: "collatz_one_cycle_phase n = 4"
        using remainder_one by (simp add: collatz_one_cycle_phase_def)
      show ?thesis using left right by simp
    next
      assume remainder_two: "?r = 2"
      have exponent:
          "(physical_collatz ^^ ?r) 1 = (physical_collatz ^^ 2) 1"
        by (rule arg_cong[OF remainder_two])
      have left: "(physical_collatz ^^ ?r) 1 = 2"
        using exponent physical_collatz_one_two_steps by simp
      have right: "collatz_one_cycle_phase n = 2"
        using remainder_two by (simp add: collatz_one_cycle_phase_def)
      show ?thesis using left right by simp
    qed
  qed
  finally show ?thesis .
qed

lemma physical_collatz_shifted_source:
  "(physical_collatz ^^ n) (physical_collatz source) =
    (physical_collatz ^^ Suc n) source"
  by (induction n arbitrary: source) simp_all

lemma physical_collatz_twice_shifted_source:
  "(physical_collatz ^^ n)
      (physical_collatz (physical_collatz source)) =
    (physical_collatz ^^ (n+2)) source"
  using physical_collatz_shifted_source[of n "physical_collatz source"]
    physical_collatz_shifted_source[of "Suc n" source]
  by simp

theorem physical_collatz_cycle_phase:
  assumes "collatz_cycle_admitted source"
  shows "(physical_collatz ^^ n) source = collatz_cycle_phase source n"
proof -
  from assms have source_cases:
      "source = 1 \<or> source = 4 \<or> source = 2"
    by (simp add: collatz_cycle_admitted_def)
  from source_cases show ?thesis
  proof (elim disjE)
    assume source_one: "source = 1"
    show ?thesis using physical_collatz_one_cycle_phase[of n] source_one
      by (simp add: collatz_cycle_phase_def)
  next
    assume source_four: "source = 4"
    have source_is_shift: "source = physical_collatz 1"
    proof -
      have "source = 4" by (rule source_four)
      also have "... = physical_collatz 1"
        by (rule physical_collatz_one_cycle_values(1)[symmetric])
      finally show ?thesis .
    qed
    have "(physical_collatz ^^ n) source =
        (physical_collatz ^^ n) (physical_collatz 1)"
      by (rule arg_cong[OF source_is_shift])
    also have "... = (physical_collatz ^^ Suc n) 1"
      by (rule physical_collatz_shifted_source)
    also have "... = collatz_one_cycle_phase (Suc n)"
      by (rule physical_collatz_one_cycle_phase)
    also have "... = collatz_cycle_phase source n"
      using source_four by (simp add: collatz_cycle_phase_def)
    finally show ?thesis .
  next
    assume source_two: "source = 2"
    have twice_is_two:
        "physical_collatz (physical_collatz 1) = 2"
    proof -
      have "physical_collatz (physical_collatz 1) = physical_collatz 4"
        by (rule arg_cong[OF physical_collatz_one_cycle_values(1)])
      also have "... = 2"
        by (rule physical_collatz_one_cycle_values(2))
      finally show ?thesis .
    qed
    have source_is_shift:
        "source = physical_collatz (physical_collatz 1)"
    proof -
      have "source = 2" by (rule source_two)
      also have "... = physical_collatz (physical_collatz 1)"
        by (rule twice_is_two[symmetric])
      finally show ?thesis .
    qed
    have "(physical_collatz ^^ n) source =
        (physical_collatz ^^ n)
          (physical_collatz (physical_collatz 1))"
      by (rule arg_cong[OF source_is_shift])
    also have "... = (physical_collatz ^^ (n+2)) 1"
      by (rule physical_collatz_twice_shifted_source)
    also have "... = collatz_one_cycle_phase (n+2)"
      by (rule physical_collatz_one_cycle_phase)
    also have "... = collatz_cycle_phase source n"
      using source_two by (simp add: collatz_cycle_phase_def)
    finally show ?thesis .
  qed
qed

lemma collatz_physical_odd_count_add:
  "collatz_physical_odd_count (first+second) source =
    collatz_physical_odd_count first source +
      collatz_physical_odd_count second
        ((physical_collatz ^^ first) source)"
  using collatz_physical_branch_word_add[of first second source]
  by (simp add: collatz_physical_odd_count_def)

lemma collatz_cycle_three_steps:
  assumes "collatz_cycle_admitted source"
  shows "(physical_collatz ^^ 3) source = source"
  using assms
  by (auto simp: collatz_cycle_admitted_def physical_collatz_def
      numeral_3_eq_3)

lemma collatz_cycle_chunks:
  assumes "collatz_cycle_admitted source"
  shows "(physical_collatz ^^ (3*q)) source = source"
proof (induction q)
  case 0
  then show ?case by simp
next
  case (Suc q)
  have "(physical_collatz ^^ (3 * Suc q)) source =
      (physical_collatz ^^ (3*q+3)) source"
    by (rule arg_cong) (simp add: add.commute)
  also have "... =
      (physical_collatz ^^ (3*q)) ((physical_collatz ^^ 3) source)"
    by (simp only: funpow_add comp_apply)
  also have "... = (physical_collatz ^^ (3*q)) source"
    by (rule arg_cong[OF collatz_cycle_three_steps[OF assms]])
  also have "... = source"
    by (rule Suc.IH)
  finally show ?case .
qed

lemma collatz_cycle_literal_odd_counts [simp]:
  "collatz_physical_odd_count 1 1 = 1"
  "collatz_physical_odd_count 2 1 = 1"
  "collatz_physical_odd_count 3 1 = 1"
  "collatz_physical_odd_count 1 4 = 0"
  "collatz_physical_odd_count 2 4 = 0"
  "collatz_physical_odd_count 3 4 = 1"
  "collatz_physical_odd_count 1 2 = 0"
  "collatz_physical_odd_count 2 2 = 1"
  "collatz_physical_odd_count 3 2 = 1"
  by code_simp+

lemma collatz_cycle_chunk_odd_count:
  assumes "collatz_cycle_admitted source"
  shows "collatz_physical_odd_count (3*q) source = q"
proof (induction q)
  case 0
  then show ?case
    by (simp add: collatz_physical_odd_count_def)
next
  case (Suc q)
  have endpoint: "(physical_collatz ^^ (3*q)) source = source"
    by (rule collatz_cycle_chunks[OF assms])
  have three: "collatz_physical_odd_count 3 source = 1"
  proof -
    from assms have source_cases:
        "source = 1 \<or> source = 4 \<or> source = 2"
      by (simp add: collatz_cycle_admitted_def)
    from source_cases show ?thesis
    proof (elim disjE)
      assume source_one: "source = 1"
      show ?thesis
        by (subst source_one) (rule collatz_cycle_literal_odd_counts(3))
    next
      assume source_four: "source = 4"
      show ?thesis
        by (subst source_four) (rule collatz_cycle_literal_odd_counts(6))
    next
      assume source_two: "source = 2"
      show ?thesis
        by (subst source_two) (rule collatz_cycle_literal_odd_counts(9))
    qed
  qed
  have split:
      "collatz_physical_odd_count (3*q+3) source =
       collatz_physical_odd_count (3*q) source +
        collatz_physical_odd_count 3
          ((physical_collatz ^^ (3*q)) source)"
    by (rule collatz_physical_odd_count_add)
  have "collatz_physical_odd_count (3 * Suc q) source =
      collatz_physical_odd_count (3*q+3) source"
    by (rule arg_cong) (simp add: add.commute)
  also have "... = collatz_physical_odd_count (3*q) source +
      collatz_physical_odd_count 3
        ((physical_collatz ^^ (3*q)) source)"
    by (rule split)
  also have "... = q+1"
    using Suc.IH endpoint three by simp
  also have "... = Suc q" by simp
  finally show ?case .
qed

theorem collatz_physical_cycle_odd_count:
  assumes "collatz_cycle_admitted source"
  shows "collatz_physical_odd_count n source =
    collatz_cycle_odd_count source n"
proof -
  let ?q = "n div 3"
  let ?r = "n mod 3"
  have decomposition: "n = 3*?q + ?r"
    using mod_mult_div_eq[of n 3] by (simp add: algebra_simps)
  have remainder: "?r < 3" by simp
  have remainder_cases: "?r = 0 \<or> ?r = 1 \<or> ?r = 2"
    using remainder by arith
  have split:
      "collatz_physical_odd_count n source =
       collatz_physical_odd_count (3*?q) source +
        collatz_physical_odd_count ?r
          ((physical_collatz ^^ (3*?q)) source)"
  proof -
    have "collatz_physical_odd_count n source =
        collatz_physical_odd_count (3*?q+?r) source"
      by (rule arg_cong[OF decomposition])
    also have "... = collatz_physical_odd_count (3*?q) source +
        collatz_physical_odd_count ?r
          ((physical_collatz ^^ (3*?q)) source)"
      by (rule collatz_physical_odd_count_add)
    finally show ?thesis .
  qed
  have endpoint: "(physical_collatz ^^ (3*?q)) source = source"
    by (rule collatz_cycle_chunks[OF assms])
  have chunks: "collatz_physical_odd_count (3*?q) source = ?q"
    by (rule collatz_cycle_chunk_odd_count[OF assms])
  have core:
      "collatz_physical_odd_count n source = ?q +
        collatz_physical_odd_count ?r source"
    using split endpoint chunks by simp
  from assms have source_cases:
      "source = 1 \<or> source = 4 \<or> source = 2"
    by (simp add: collatz_cycle_admitted_def)
  from remainder_cases show ?thesis
  proof (elim disjE)
    assume remainder_zero: "?r = 0"
    have remainder_count: "collatz_physical_odd_count ?r source = 0"
      using remainder_zero by (simp add: collatz_physical_odd_count_def)
    have div_plus_one: "(n+1) div 3 = ?q"
    proof -
      have "(n+1) div 3 = (3*?q+?r+1) div 3"
        by (rule arg_cong[OF decomposition])
      then show ?thesis using remainder_zero by simp
    qed
    have div_plus_two: "(n+2) div 3 = ?q"
    proof -
      have "(n+2) div 3 = (3*?q+?r+2) div 3"
        by (rule arg_cong[OF decomposition])
      then show ?thesis using remainder_zero by simp
    qed
    show ?thesis using source_cases core remainder_count
        div_plus_one div_plus_two
      by (auto simp: collatz_cycle_odd_count_def)
  next
    assume remainder_one: "?r = 1"
    have remainder_count:
        "collatz_physical_odd_count ?r source =
          (if source = 1 then 1 else 0)"
    proof -
      from source_cases show ?thesis
      proof (elim disjE)
        assume source_one: "source = 1"
        show ?thesis
          unfolding remainder_one source_one by code_simp
      next
        assume source_four: "source = 4"
        show ?thesis
          unfolding remainder_one source_four by code_simp
      next
        assume source_two: "source = 2"
        show ?thesis
          unfolding remainder_one source_two by code_simp
      qed
    qed
    have div_plus_one: "(n+1) div 3 = ?q"
    proof -
      have "(n+1) div 3 = (3*?q+?r+1) div 3"
        by (rule arg_cong[OF decomposition])
      then show ?thesis using remainder_one by simp
    qed
    have div_plus_two: "(n+2) div 3 = ?q+1"
    proof -
      have "(n+2) div 3 = (3*?q+?r+2) div 3"
        by (rule arg_cong[OF decomposition])
      then show ?thesis using remainder_one by simp
    qed
    show ?thesis using source_cases core remainder_count
        div_plus_one div_plus_two
      by (auto simp: collatz_cycle_odd_count_def)
  next
    assume remainder_two: "?r = 2"
    have remainder_count:
        "collatz_physical_odd_count ?r source =
          (if source = 4 then 0 else 1)"
    proof -
      from source_cases show ?thesis
      proof (elim disjE)
        assume source_one: "source = 1"
        show ?thesis
          unfolding remainder_two source_one by code_simp
      next
        assume source_four: "source = 4"
        show ?thesis
          unfolding remainder_two source_four by code_simp
      next
        assume source_two: "source = 2"
        show ?thesis
          unfolding remainder_two source_two by code_simp
      qed
    qed
    have div_plus_one: "(n+1) div 3 = ?q+1"
    proof -
      have "(n+1) div 3 = (3*?q+?r+1) div 3"
        by (rule arg_cong[OF decomposition])
      then show ?thesis using remainder_two by simp
    qed
    have div_plus_two: "(n+2) div 3 = ?q+1"
    proof -
      have "(n+2) div 3 = (3*?q+?r+2) div 3"
        by (rule arg_cong[OF decomposition])
      then show ?thesis using remainder_two by simp
    qed
    show ?thesis using source_cases core remainder_count
        div_plus_one div_plus_two
      by (auto simp: collatz_cycle_odd_count_def)
  qed
qed

corollary collatz_physical_one_cycle_chunk_odd_count:
  "collatz_physical_odd_count (3*q) 1 = q"
  using collatz_cycle_chunk_odd_count[of 1 q]
  by (simp add: collatz_cycle_admitted_def)

corollary collatz_physical_one_cycle_odd_count:
  "collatz_physical_odd_count n 1 = (n+2) div 3"
  using collatz_physical_cycle_odd_count[of 1 n]
  by (simp add: collatz_cycle_admitted_def collatz_cycle_odd_count_def)

lemma collatz_one_cycle_low_residue_is_not_admission:
  "(9::nat) mod 8 = 1 mod 8 \<and>
   (physical_collatz ^^ 3) 9 \<noteq> 9"
  by (simp add: physical_collatz_def numeral_3_eq_3)

text \<open>The returning-action theorem is restricted to the admitted
three-element exact cycle.  Each member has its own phase and odd-count law.
A runtime may reach it after an exact bounded prefix from another seed, but
that prefix and the exact source equality remain executable refinement
obligations.  These finite identities do not prove Collatz convergence or
authorize cycle admission from a truncated residue.\<close>

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms physical_collatz_one_cycle_values
      physical_collatz_one_two_steps physical_collatz_one_one_step
      physical_collatz_one_cycle_chunks physical_collatz_one_cycle_phase
      physical_collatz_shifted_source physical_collatz_twice_shifted_source
      physical_collatz_cycle_phase
      collatz_physical_odd_count_add
      collatz_physical_one_cycle_chunk_odd_count
      collatz_physical_one_cycle_odd_count
      collatz_cycle_three_steps collatz_cycle_chunks
      collatz_cycle_literal_odd_counts
      collatz_cycle_chunk_odd_count collatz_physical_cycle_odd_count
      collatz_one_cycle_low_residue_is_not_admission})
    then () else error "Physical Collatz one-cycle proof depends on an oracle";
\<close>

end
