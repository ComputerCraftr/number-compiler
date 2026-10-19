theory Collatz_Units_Carry_Transfer
  imports Collatz_Boundary_Macros
begin

text \<open>This five-state units transfer specifies the low-decimal projection
consumed by the production named-border carry-matrix observation.  Its state
is the exact residue modulo five; its additive output is the local decimal
tens carry.  The refinement below applies to an admitted normalized Collatz
word, while issuance and source guards remain with the producer-owned border
macro and port join.  This theory makes no claim about the other,
independently guarded upper-digit ports of the 100-state border relation.\<close>

definition collatz_units_target :: "bool \<Rightarrow> nat \<Rightarrow> nat" where
  "collatz_units_target odd_step r =
    (if odd_step then (4*r + 3) mod 5 else (3*r) mod 5)"

definition collatz_units_tens_carry :: "bool \<Rightarrow> nat \<Rightarrow> nat" where
  "collatz_units_tens_carry odd_step r =
    (if odd_step then
      (3 * (if odd r then r else r + 5) + 1) div 10
     else 0)"

definition collatz_source_tens_carry :: "nat \<Rightarrow> nat" where
  "collatz_source_tens_carry x =
    (if odd x then (3 * (x mod 10) + 1) div 10 else 0)"

lemma collatz_units_target_refines_source:
  assumes branch: "odd_step = odd x"
      and residue: "r = x mod 5"
  shows "collatz_units_target odd_step r =
    collatz_guarded_normalized_source_step odd_step x mod 5"
proof -
  have iterate_two:
    "(physical_collatz ^^ 2) x = physical_collatz (physical_collatz x)"
  proof -
    have two: "(2::nat) = Suc (Suc 0)" by simp
    show ?thesis
      by (simp only: two funpow.simps comp_apply id_apply)
  qed
  have odd_two:
    "(physical_collatz ^^ 2) x = (3*x+1) div 2"
    if odd_x: "odd x"
  proof -
    have even_successor: "even (3*x+1)" using odd_x by simp
    have first: "physical_collatz x = 3*x+1"
      using odd_x by (simp add: physical_collatz_def)
    have second: "physical_collatz (3*x+1) = (3*x+1) div 2"
      using even_successor by (simp add: physical_collatz_def)
    show ?thesis using iterate_two first second by simp
  qed
  have normalized:
    "collatz_guarded_normalized_source_step (odd x) x =
      (if odd x then (3*x+1) div 2 else x div 2)"
  proof (cases "odd x")
    case True
    then show ?thesis using odd_two
      by (simp add: collatz_guarded_normalized_source_step_def)
  next
    case False
    then show ?thesis
      by (simp add: collatz_guarded_normalized_source_step_def
          physical_collatz_def)
  qed
  show ?thesis
  proof (cases "odd x")
    case True
    have odd_selector: "odd_step = True"
      using branch True by simp
    have step:
      "collatz_guarded_normalized_source_step True x = (3*x+1) div 2"
      using normalized True by simp
    have numerator_even: "even (3*x+1)" using True by simp
    have twice: "2 * ((3*x+1) div 2) = 3*x+1"
      using numerator_even by simp
    have numerator_residue:
      "(3*x+1) mod 5 = (3*r+1) mod 5"
      using collatz_modular_numerator_residue
        [where source=x and m=5 and s=r and branch=True] residue
      by simp
    have half_transport:
      "((2*((3*x+1) div 2) mod 5) *
        collatz_modular_half_inverse 5) mod 5 =
        ((3*x+1) div 2) mod 5"
      by (rule collatz_modular_half_transport) simp
    have half_endpoint:
      "(((3*x+1) mod 5) * 3) mod 5 =
        ((3*x+1) div 2) mod 5"
      using half_transport twice
      by (simp add: collatz_modular_half_inverse_def)
    have target_algebra:
      "(3*(3*r+1)) mod 5 = (4*r+3) mod 5"
    proof -
      have expanded: "3*(3*r+1) = 5*r + (4*r+3)"
        by (simp add: algebra_simps)
      show ?thesis
        unfolding expanded
        by (rule mod_mult_self4)
    qed
    have selected_target:
      "(((3*r+1) mod 5) * 3) mod 5 = (4*r+3) mod 5"
    proof -
      have scaled:
        "(((3*r+1) mod 5) * 3) mod 5 =
          (3*(3*r+1)) mod 5"
      proof -
        have "(((3*r+1) mod 5) * 3) mod 5 =
            ((3*r+1)*3) mod 5"
          by (simp only: mod_mult_left_eq)
        also have "... = (3*(3*r+1)) mod 5"
          by (simp only: mult.commute)
        finally show ?thesis .
      qed
      also have "... = (4*r+3) mod 5"
        by (rule target_algebra)
      finally show ?thesis .
    qed
    have target:
      "((3*x+1) div 2) mod 5 = (4*r+3) mod 5"
      using half_endpoint numerator_residue selected_target by simp
    show ?thesis
      unfolding odd_selector step
      using target by (simp add: collatz_units_target_def)
  next
    case False
    have even_selector: "odd_step = False"
      using branch False by simp
    have even_x: "even x" using False by simp
    have step: "collatz_guarded_normalized_source_step False x = x div 2"
      using even_x
      by (simp add: collatz_guarded_normalized_source_step_def
          physical_collatz_def)
    have twice: "2 * (x div 2) = x" using even_x by simp
    have half_transport:
      "((2*(x div 2) mod 5) * collatz_modular_half_inverse 5) mod 5 =
        (x div 2) mod 5"
      by (rule collatz_modular_half_transport) simp
    have half_endpoint:
      "((x mod 5) * 3) mod 5 = (x div 2) mod 5"
      using half_transport twice
      by (simp add: collatz_modular_half_inverse_def)
    have target: "(3*r) mod 5 = (x div 2) mod 5"
      using half_endpoint residue by (simp add: mult.commute)
    show ?thesis
      unfolding even_selector step
      using target by (simp add: collatz_units_target_def)
  qed
qed

lemma collatz_odd_units_digit_from_mod5:
  fixes x r :: nat
  assumes odd_source: "odd x"
      and residue: "r = x mod 5"
      and bounded: "r < 5"
  shows "x mod 10 = (if odd r then r else r + 5)"
proof -
  have residue_mod: "(x mod 10) mod 5 = r"
  proof -
    have five_dvd_ten: "(5::nat) dvd 10" by simp
    have "(x mod 10) mod 5 = x mod 5"
      by (rule mod_mod_cancel[OF five_dvd_ten])
    then show ?thesis using residue by simp
  qed
  have odd_digit: "odd (x mod 10)"
  proof -
    have two_dvd_ten: "(2::nat) dvd 10" by simp
    have parity_mod: "(x mod 10) mod 2 = x mod 2"
      by (rule mod_mod_cancel[OF two_dvd_ten])
    show ?thesis using odd_source parity_mod
      by (simp add: odd_iff_mod_2_eq_one)
  qed
  have digit_bound: "x mod 10 < 10" by simp
  have residue_cases: "r = 0 \<or> r = 1 \<or> r = 2 \<or> r = 3 \<or> r = 4"
    using bounded by arith
  have digit_cases:
    "x mod 10 = 0 \<or> x mod 10 = 1 \<or> x mod 10 = 2 \<or>
     x mod 10 = 3 \<or> x mod 10 = 4 \<or> x mod 10 = 5 \<or>
     x mod 10 = 6 \<or> x mod 10 = 7 \<or> x mod 10 = 8 \<or>
     x mod 10 = 9"
    using digit_bound by arith
  show ?thesis
    using residue_mod odd_digit residue_cases digit_cases
    by auto
qed

lemma collatz_units_carry_refines_source:
  assumes branch: "odd_step = odd x"
      and residue: "r = x mod 5"
      and bounded: "r < 5"
  shows "collatz_units_tens_carry odd_step r =
    collatz_source_tens_carry x"
proof (cases "odd x")
  case True
  have units:
    "x mod 10 = (if odd r then r else r + 5)"
    using collatz_odd_units_digit_from_mod5[OF True residue bounded] .
  show ?thesis
    using branch True units
    by (simp add: collatz_units_tens_carry_def
        collatz_source_tens_carry_def)
next
  case False
  then show ?thesis using branch
    by (simp add: collatz_units_tens_carry_def
        collatz_source_tens_carry_def)
qed

fun collatz_units_word :: "bool list \<Rightarrow> nat \<Rightarrow> nat \<times> nat" where
  "collatz_units_word [] r = (r, 0)"
| "collatz_units_word (branch # tail) r =
    (let next = collatz_units_target branch r;
         (endpoint, carries) = collatz_units_word tail next
     in (endpoint, collatz_units_tens_carry branch r + carries))"

fun collatz_source_tens_carry_word :: "bool list \<Rightarrow> nat \<Rightarrow> nat" where
  "collatz_source_tens_carry_word [] x = 0"
| "collatz_source_tens_carry_word (branch # tail) x =
    collatz_source_tens_carry x +
      collatz_source_tens_carry_word tail
        (collatz_guarded_normalized_source_step branch x)"

lemma collatz_units_word_append:
  "collatz_units_word (first @ second) r =
    (case collatz_units_word first r of (middle, before) \<Rightarrow>
      (case collatz_units_word second middle of (endpoint, after) \<Rightarrow>
        (endpoint, before + after)))"
  by (induction first arbitrary: r) (simp_all split: prod.splits)

theorem collatz_units_word_refines_admitted_source:
  assumes admitted: "collatz_guarded_normalized_word_admitted bits source"
  shows "collatz_units_word bits (source mod 5) =
    (collatz_guarded_normalized_word_endpoint bits source mod 5,
      collatz_source_tens_carry_word bits source)"
  using admitted
proof (induction bits arbitrary: source)
  case Nil
  then show ?case by simp
next
  case (Cons branch tail)
  from Cons.prems have parity: "branch = odd source" by simp
  have tail_admitted:
    "collatz_guarded_normalized_word_admitted tail
      (collatz_guarded_normalized_source_step branch source)"
  proof -
    have parts:
      "branch = odd source \<and>
        collatz_guarded_normalized_word_admitted tail
          (collatz_guarded_normalized_source_step branch source)"
      using Cons.prems[unfolded collatz_guarded_normalized_word_admitted.simps] .
    show ?thesis by (rule conjunct2[OF parts])
  qed
  then have bounded: "source mod 5 < 5" by simp
  have target:
    "collatz_units_target branch (source mod 5) =
      collatz_guarded_normalized_source_step branch source mod 5"
    by (rule collatz_units_target_refines_source[OF parity refl])
  have carry:
    "collatz_units_tens_carry branch (source mod 5) =
      collatz_source_tens_carry source"
    by (rule collatz_units_carry_refines_source[OF parity refl bounded])
  have ih:
    "collatz_units_word tail
        (collatz_guarded_normalized_source_step branch source mod 5) =
      (collatz_guarded_normalized_word_endpoint tail
          (collatz_guarded_normalized_source_step branch source) mod 5,
        collatz_source_tens_carry_word tail
          (collatz_guarded_normalized_source_step branch source))"
    using Cons.IH tail_admitted by blast
  show ?case
    using ih target carry
    by (simp add: collatz_guarded_normalized_word_admitted.simps
        collatz_guarded_normalized_word_endpoint.simps
        collatz_source_tens_carry_word.simps)
qed

theorem collatz_units_word_source_endpoint:
  assumes admitted: "collatz_guarded_normalized_word_admitted bits source"
  shows "fst (collatz_units_word bits (source mod 5)) =
    collatz_guarded_normalized_word_endpoint bits source mod 5"
  using collatz_units_word_refines_admitted_source[OF admitted] by simp

theorem collatz_units_word_source_carries:
  assumes admitted: "collatz_guarded_normalized_word_admitted bits source"
  shows "snd (collatz_units_word bits (source mod 5)) =
    collatz_source_tens_carry_word bits source"
  using collatz_units_word_refines_admitted_source[OF admitted] by simp

ML \<open>
  val checked = @{thms collatz_units_target_refines_source
    collatz_odd_units_digit_from_mod5 collatz_units_carry_refines_source
    collatz_units_word_append collatz_units_word_refines_admitted_source
    collatz_units_word_source_endpoint collatz_units_word_source_carries};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Collatz units transfer depends on an oracle";
\<close>

end
