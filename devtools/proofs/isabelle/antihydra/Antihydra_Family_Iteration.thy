theory Antihydra_Family_Iteration
  imports Antihydra_Source_Barrier
begin

text \<open>This is the family-first arithmetic object used before any
physical TM admission.  Its primary coordinate is total.  The ledger and its
minimum are projections of the generated parity word and do not feed back
into the primary recurrence.\<close>

definition antihydra_family_step :: "nat \<Rightarrow> nat" where
  "antihydra_family_step a = a + a div 2"

fun antihydra_family_orbit :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "antihydra_family_orbit a 0 = a"
| "antihydra_family_orbit a (Suc n) =
    antihydra_family_orbit (antihydra_family_step a) n"

fun antihydra_family_bits :: "nat \<Rightarrow> nat \<Rightarrow> nat list" where
  "antihydra_family_bits a 0 = []"
| "antihydra_family_bits a (Suc n) =
    a mod 2 # antihydra_family_bits (antihydra_family_step a) n"

definition antihydra_family_balance :: "nat \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> int"
where
  "antihydra_family_balance a initial n =
    initial + ledger_word_delta (antihydra_family_bits a n)"

definition antihydra_family_minimum :: "nat \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> int"
where
  "antihydra_family_minimum a initial n =
    initial + ledger_word_minprefix (antihydra_family_bits a n)"

definition antihydra_arithmetic_block :: "nat \<Rightarrow> nat \<Rightarrow> antihydra_skew"
where
  "antihydra_arithmetic_block a n = skew_word (antihydra_family_bits a n)"

definition antihydra_block_safe :: "nat \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> bool"
where
  "antihydra_block_safe a initial n \<longleftrightarrow>
    0 \<le> antihydra_family_minimum a initial n"

definition antihydra_guarded_block_apply ::
    "nat \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> (nat \<times> int) option"
where
  "antihydra_guarded_block_apply a initial n =
    (if antihydra_block_safe a initial n then
       Some (antihydra_family_orbit a n,
         antihydra_family_balance a initial n)
     else None)"

fun antihydra_ledger_prefixes_safe :: "int \<Rightarrow> nat list \<Rightarrow> bool" where
  "antihydra_ledger_prefixes_safe initial [] = (0\<le>initial)"
| "antihydra_ledger_prefixes_safe initial (b#bs) =
    (0\<le>initial \<and>
      antihydra_ledger_prefixes_safe (initial + (2-3*int b)) bs)"

theorem antihydra_family_step_is_total_skew:
  "antihydra_family_step a = antihydra_h_step a"
  by (cases a rule: nat_mod_two_cases;
      simp add: antihydra_family_step_def antihydra_h_step_def algebra_simps)

theorem antihydra_family_step_skew_equation:
  "2 * int (antihydra_family_step a) = 3 * int a - int (a mod 2)"
  by (cases a rule: nat_mod_two_cases;
      simp add: antihydra_family_step_def algebra_simps mod_Suc)

theorem antihydra_family_centered_orbit:
  "antihydra_family_orbit (D+1) n = mahler_orbit D n + 1"
proof (induct n arbitrary: D)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have first: "antihydra_family_step (D+1) = mahler_D_step D + 1"
    using centered_return_commutes[of D]
      antihydra_family_step_is_total_skew[of "D+1"] by simp
  have shifted:
    "mahler_orbit D (Suc n) = mahler_orbit (mahler_D_step D) n"
    by (rule mahler_orbit_shift)
  show ?case
    using Suc.hyps[of "mahler_D_step D"] first shifted by simp
qed

corollary antihydra_source_eight_centered_orbit:
  "antihydra_family_orbit 8 n = mahler_orbit 7 n + 1"
  using antihydra_family_centered_orbit[of 7 n] by simp

lemma antihydra_family_bits_length [simp]:
  "length (antihydra_family_bits a n) = n"
  by (induct n arbitrary: a) simp_all

lemma antihydra_family_bits_binary:
  "b \<in> set (antihydra_family_bits a n) \<Longrightarrow> b<2"
  by (induct n arbitrary: a) auto

lemma ledger_word_minprefix_nonpositive:
  "ledger_word_minprefix bs \<le> 0"
  by (induct bs) (simp_all add: min_def)

theorem ledger_word_minprefix_exact_guard:
  "0 \<le> initial + ledger_word_minprefix bs \<longleftrightarrow>
    antihydra_ledger_prefixes_safe initial bs"
proof (induct bs arbitrary: initial)
  case Nil
  then show ?case by simp
next
  case (Cons b bs)
  let ?d = "2-3*int b"
  let ?m = "ledger_word_minprefix bs"
  have mnonpos: "?m\<le>0" by (rule ledger_word_minprefix_nonpositive)
  have tail:
    "0 \<le> initial+?d+?m \<longleftrightarrow>
      antihydra_ledger_prefixes_safe (initial+?d) bs"
    using Cons.hyps[of "initial+?d"] by (simp add: algebra_simps)
  have minimum:
    "min (min 0 ?d) (?d+?m) = min 0 (?d+?m)"
    using mnonpos by (simp add: min_def; linarith)
  show ?case
    using tail minimum
    by (simp add: min_def; linarith)
qed

lemma antihydra_family_bits_append:
  "antihydra_family_bits a (m+n) =
    antihydra_family_bits a m @
      antihydra_family_bits (antihydra_family_orbit a m) n"
proof (induct m arbitrary: a)
  case 0
  then show ?case by simp
next
  case (Suc m)
  then show ?case by simp
qed

lemma antihydra_family_orbit_add:
  "antihydra_family_orbit a (m+n) =
    antihydra_family_orbit (antihydra_family_orbit a m) n"
  by (induct m arbitrary: a) simp_all

lemma skew_word_A [simp]: "sk_A (skew_word bs) = 3^length bs"
  by (induct bs) (simp_all add: skew_identity_def skew_atom_def skew_then_def)

lemma skew_word_D [simp]: "sk_D (skew_word bs) = 2^length bs"
  by (induct bs) (simp_all add: skew_identity_def skew_atom_def skew_then_def)

lemma family_skew_selectors [simp]:
  "sk_A (skew_then x y) = sk_A y*sk_A x"
  "sk_D (skew_then x y) = sk_D y*sk_D x"
  "sk_J (skew_then x y) = sk_A y*sk_J x+sk_J y*sk_D x"
  "sk_A (skew_atom b) = 3"
  "sk_D (skew_atom b) = 2"
  "sk_J (skew_atom b) = -int b"
  by (simp_all add: skew_then_def skew_atom_def)

theorem antihydra_arithmetic_block_skew_application:
  "sk_D (antihydra_arithmetic_block a n) *
      int (antihydra_family_orbit a n) =
    skew_numerator (antihydra_arithmetic_block a n) (int a)"
proof (induct n arbitrary: a)
  case 0
  then show ?case
    by (simp add: antihydra_arithmetic_block_def skew_identity_def
        skew_numerator_def)
next
  case (Suc n)
  let ?b = "a mod 2"
  let ?next = "antihydra_family_step a"
  have binary: "?b<2" by simp
  have first: "2*int ?next = 3*int a-int ?b"
    by (rule antihydra_family_step_skew_equation)
  have IH:
    "sk_D (antihydra_arithmetic_block ?next n) *
        int (antihydra_family_orbit ?next n) =
      skew_numerator (antihydra_arithmetic_block ?next n) (int ?next)"
    by (rule Suc.hyps)
  have IH_expanded:
    "2^n * int (antihydra_family_orbit ?next n) =
      sk_J (antihydra_arithmetic_block ?next n) + 3^n * int ?next"
    using IH
    by (simp add: antihydra_arithmetic_block_def skew_numerator_def
        algebra_simps)
  have block_step:
    "antihydra_arithmetic_block a (Suc n) =
      skew_then (skew_atom ?b) (antihydra_arithmetic_block ?next n)"
    by (simp add: antihydra_arithmetic_block_def)
  have orbit_step:
    "antihydra_family_orbit a (Suc n) =
      antihydra_family_orbit ?next n"
    by simp
  have Arest: "sk_A (antihydra_arithmetic_block ?next n) = 3^n"
    by (simp add: antihydra_arithmetic_block_def)
  have Drest: "sk_D (antihydra_arithmetic_block ?next n) = 2^n"
    by (simp add: antihydra_arithmetic_block_def)
  have reduced:
    "sk_D (antihydra_arithmetic_block ?next n) * 2 *
        int (antihydra_family_orbit ?next n) =
      sk_A (antihydra_arithmetic_block ?next n) * 3 * int a +
        (sk_A (antihydra_arithmetic_block ?next n) * -int ?b +
          sk_J (antihydra_arithmetic_block ?next n) * 2)"
  proof -
    have "sk_D (antihydra_arithmetic_block ?next n) * 2 *
        int (antihydra_family_orbit ?next n) =
      2 * (2^n * int (antihydra_family_orbit ?next n))"
      using Drest by (simp add: algebra_simps)
    also have "... = 2 *
        (sk_J (antihydra_arithmetic_block ?next n) + 3^n * int ?next)"
      using IH_expanded by simp
    also have "... = 2*sk_J (antihydra_arithmetic_block ?next n) +
        3^n * (2*int ?next)"
      by (simp add: algebra_simps)
    also have "... = 2*sk_J (antihydra_arithmetic_block ?next n) +
        3^n * (3*int a-int ?b)"
      using first by simp
    also have "... =
      sk_A (antihydra_arithmetic_block ?next n) * 3 * int a +
        (sk_A (antihydra_arithmetic_block ?next n) * -int ?b +
          sk_J (antihydra_arithmetic_block ?next n) * 2)"
      using Arest by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  show ?case
    unfolding block_step orbit_step skew_numerator_def
    apply (simp only: family_skew_selectors)
    by (rule reduced)
qed

theorem antihydra_arithmetic_block_composition:
  "antihydra_arithmetic_block a (m+n) =
    skew_then (antihydra_arithmetic_block a m)
      (antihydra_arithmetic_block (antihydra_family_orbit a m) n)"
  unfolding antihydra_arithmetic_block_def
  using antihydra_family_bits_append[of a m n] skew_word_append by simp

theorem antihydra_arithmetic_block_ledger_projection:
  "sk_delta (antihydra_arithmetic_block a n) =
      antihydra_family_balance a 0 n"
  "sk_minprefix (antihydra_arithmetic_block a n) =
      antihydra_family_minimum a 0 n"
  unfolding antihydra_arithmetic_block_def antihydra_family_balance_def
    antihydra_family_minimum_def
  using skew_word_induces_ledger_geometry[of "antihydra_family_bits a n"]
  by simp_all

theorem antihydra_block_safe_exactly_all_prefixes:
  "antihydra_block_safe a initial n \<longleftrightarrow>
    antihydra_ledger_prefixes_safe initial (antihydra_family_bits a n)"
  unfolding antihydra_block_safe_def antihydra_family_minimum_def
  by (rule ledger_word_minprefix_exact_guard)

theorem antihydra_family_primary_independent_of_ledger:
  "fst (antihydra_family_orbit a n, antihydra_family_balance a initial n) =
    antihydra_family_orbit a n"
  by simp

theorem antihydra_guarded_before_failure_agrees:
  assumes safe: "antihydra_block_safe a initial n"
  shows "antihydra_guarded_block_apply a initial n =
    Some (antihydra_family_orbit a n,
      antihydra_family_balance a initial n)"
  using safe by (simp add: antihydra_guarded_block_apply_def)

theorem antihydra_first_failed_block_refuses:
  assumes unsafe: "\<not> antihydra_block_safe a initial n"
  shows "antihydra_guarded_block_apply a initial n = None"
  using unsafe by (simp add: antihydra_guarded_block_apply_def)

corollary antihydra_source_eight_guarded_prefix:
  assumes "antihydra_block_safe 8 0 n"
  shows "antihydra_guarded_block_apply 8 0 n =
    Some (mahler_orbit 7 n+1, antihydra_family_balance 8 0 n)"
  using antihydra_guarded_before_failure_agrees[OF assms]
    antihydra_source_eight_centered_orbit[of n] by simp

text \<open>The guarded option above isolates the precise arithmetic boundary:
safe prefixes agree with the total family iteration, while the first unsafe
block is refused.  It does not identify cylinder roof counts with a literal
six-state TM run, and it does not prove that every source-eight prefix is safe.\<close>

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms antihydra_family_step_is_total_skew
      antihydra_family_step_skew_equation antihydra_family_centered_orbit
      antihydra_source_eight_centered_orbit
      antihydra_family_bits_length antihydra_family_bits_binary
      ledger_word_minprefix_nonpositive ledger_word_minprefix_exact_guard
      antihydra_family_bits_append antihydra_family_orbit_add
      skew_word_A skew_word_D antihydra_arithmetic_block_skew_application
      antihydra_arithmetic_block_composition
      antihydra_arithmetic_block_ledger_projection
      antihydra_block_safe_exactly_all_prefixes
      antihydra_family_primary_independent_of_ledger
      antihydra_guarded_before_failure_agrees antihydra_first_failed_block_refuses
      antihydra_source_eight_guarded_prefix}) then ()
    else error "Antihydra family iteration proof depends on an oracle";
\<close>

end
