theory Reverse_Guarded_Laurent_Forcing
  imports Reverse_Laurent_Source_Refinement
begin

text \<open>
For one admitted reverse/add letter, the width-growth bit selects the
fixed-width reversal factor.  When the current source is already divisible
by eleven, either factor gives an integral Laurent defect.  This theorem
certifies the individual forcing letter.  It does not claim that a finite
forcing word is generated indefinitely by a physical source.
\<close>

definition reverse_guarded_laurent_defect ::
    "nat \<Rightarrow> nat list \<Rightarrow> int" where
  "reverse_guarded_laurent_defect growth ss =
    (int (10 ^ growth * reverse_add_pair_term ss) -
      int (reverse_add_pair_reverse ss)) div 99"

lemma reverse_guarded_laurent_defect_integral:
  assumes growth: "growth < 2"
      and source_width_case:
        "reverse_add_pair_term ss mod 11 = 0 \<or>
         (even (length (digits ss)) \<and> growth = 1) \<or>
         (odd (length (digits ss)) \<and> growth = 0)"
  shows "int (10 ^ growth * reverse_add_pair_term ss) -
      int (reverse_add_pair_reverse ss) =
    99 * reverse_guarded_laurent_defect growth ss"
proof -
  let ?source = "reverse_add_pair_term ss"
  let ?reverse = "reverse_add_pair_reverse ss"
  let ?scaled = "10 ^ growth * ?source"
  have reverse_mod9: "?reverse mod 9 = ?source mod 9"
    by (simp add: reverse_add_pair_reverse_def reverse_add_pair_term_def
        decimal_list_value_reverse_mod9)
  have scaled_mod9: "?scaled mod 9 = ?source mod 9"
  proof -
    have cases: "growth = 0 \<or> growth = 1"
      using growth by arith
    have power_mod:
      "(10::nat) ^ growth mod 9 = 1 mod 9"
      using cases by (elim disjE; simp_all)
    have source_mod: "?source mod 9 = ?source mod 9" by simp
    have product:
      "(10 ^ growth * ?source) mod 9 = (1 * ?source) mod 9"
      by (rule mod_mult_cong[OF power_mod source_mod])
    show ?thesis using product by simp
  qed
  have reverse_mod11:
    "?reverse mod 11 =
      ((if even (length (digits ss)) then 10 else 1) * ?source) mod 11"
    by (simp add: reverse_add_pair_reverse_def reverse_add_pair_term_def
        decimal_list_value_reverse_mod11)
  have scaled_mod11: "?scaled mod 11 = ?reverse mod 11"
    using source_width_case
  proof (elim disjE)
    assume divisible: "?source mod 11 = 0"
    have source_zero: "?source mod 11 = (0::nat) mod 11"
      using divisible by simp
    have power_congruent:
      "(10 ^ growth::nat) mod 11 = (10 ^ growth::nat) mod 11" by simp
    have scaled_zero: "?scaled mod 11 = 0"
    proof -
      have product:
        "(10 ^ growth * ?source) mod 11 = (10 ^ growth * 0) mod 11"
        by (rule mod_mult_cong[OF power_congruent source_zero])
      show ?thesis using product by simp
    qed
    have reverse_zero: "?reverse mod 11 = 0"
    proof -
      have coefficient_congruent:
        "(if even (length (digits ss)) then 10 else 1) mod 11 =
          (if even (length (digits ss)) then 10 else 1) mod 11" by simp
      have product:
        "((if even (length (digits ss)) then 10 else 1) * ?source) mod 11 =
          ((if even (length (digits ss)) then 10 else 1) * 0) mod 11"
        by (rule mod_mult_cong[OF coefficient_congruent source_zero])
      show ?thesis using reverse_mod11 product by simp
    qed
    show ?thesis using scaled_zero reverse_zero by simp
  next
    assume even_width: "even (length (digits ss)) \<and> growth = 1"
    then have factor: "(10::nat) ^ growth = 10" by simp
    show ?thesis
      using reverse_mod11 factor even_width by simp
  next
    assume odd_width: "odd (length (digits ss)) \<and> growth = 0"
    then have factor: "(10::nat) ^ growth = 1" by simp
    show ?thesis
      using reverse_mod11 factor odd_width by simp
  qed
  have scaled_mod99: "?scaled mod 99 = ?reverse mod 99"
  proof (rule mod_9_11_equal_mod99)
    show "?scaled mod 9 = ?reverse mod 9"
      using scaled_mod9 reverse_mod9 by simp
    show "?scaled mod 11 = ?reverse mod 11"
      by (rule scaled_mod11)
  qed
  have integer_mod99:
    "(int ?scaled - int ?reverse) mod (99::int) = 0"
  proof -
    have same:
      "int (?scaled mod 99) = int (?reverse mod 99)"
      using scaled_mod99 by simp
    have cast:
      "(int ?scaled) mod 99 = (int ?reverse) mod 99"
      using same by (simp only: of_nat_mod of_nat_numeral)
    have difference:
      "(int ?scaled - int ?reverse) mod (99::int) =
        (int ?reverse - int ?reverse) mod 99"
      by (rule mod_diff_cong[OF cast]) simp
    show ?thesis using difference by simp
  qed
  have quotient:
    "(int ?scaled - int ?reverse) div 99 * 99 +
       (int ?scaled - int ?reverse) mod 99 =
      int ?scaled - int ?reverse"
    by (rule div_mult_mod_eq)
  show ?thesis
    using integer_mod99 quotient
    by (simp add: reverse_guarded_laurent_defect_def mult.commute)
qed

theorem reverse_guarded_laurent_one_tick:
  assumes valid: "valid_pair ss"
      and source_width_case:
        "reverse_add_pair_term ss mod 11 = 0 \<or>
         (even (length (digits ss)) \<and> growth = 1) \<or>
         (odd (length (digits ss)) \<and> growth = 0)"
      and growth: "growth < 2"
  shows "int (reverse_add_pair_term (step ss)) =
      (1 + 10 ^ growth) * int (reverse_add_pair_term ss) -
        99 * reverse_guarded_laurent_defect growth ss"
proof -
  have source_step:
    "reverse_add_pair_term (step ss) =
      reverse_add_pair_term ss + reverse_add_pair_reverse ss"
    by (rule reverse_add_completed_pair_successor[OF valid])
  have defect:
    "int (10 ^ growth * reverse_add_pair_term ss) -
        int (reverse_add_pair_reverse ss) =
      99 * reverse_guarded_laurent_defect growth ss"
    by (rule reverse_guarded_laurent_defect_integral[OF growth source_width_case])
  have exact:
    "10 ^ growth * int (reverse_add_pair_term ss) -
      int (reverse_add_pair_reverse ss) =
      99 * reverse_guarded_laurent_defect growth ss"
    using defect by simp
  have successor:
    "int (reverse_add_pair_term (step ss)) =
      int (reverse_add_pair_term ss) + int (reverse_add_pair_reverse ss)"
    using source_step by simp
  have product:
    "10 ^ growth * int (reverse_add_pair_term ss) =
      int (reverse_add_pair_reverse ss) + 99 * reverse_guarded_laurent_defect growth ss"
    using exact by linarith
  show ?thesis
    by (simp add: distrib_right successor product)
qed

ML \<open>
  val checked = @{thms reverse_guarded_laurent_defect_integral
    reverse_guarded_laurent_one_tick};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Guarded reverse Laurent forcing depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked
    then error "Skipped guarded reverse Laurent forcing proof" else ();
\<close>

end
