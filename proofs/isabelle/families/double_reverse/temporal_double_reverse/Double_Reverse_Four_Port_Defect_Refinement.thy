theory Double_Reverse_Four_Port_Defect_Refinement
  imports Double_Reverse_Four_Port_Numeric_Refinement
begin

text \<open>This theory proves the concrete source-carry refinement for the
four-port temporal defect. The carry mask is reconstructed from source digits,
then connected to the exact two-macro integer recurrence. No temporal closure
is inferred from the finite action.\<close>

definition double_reverse_source_carry_mask :: "nat list \<Rightarrow> nat" where
  "double_reverse_source_carry_mask source =
    double_reverse_msf_value (map threshold5_digit source)"

definition double_reverse_source_carry_prefix :: "nat list \<Rightarrow> nat" where
  "double_reverse_source_carry_prefix source =
    double_reverse_msf_value (map threshold5_digit (butlast source))"

lemma double_reverse_source_carry_mask_cons:
  "double_reverse_source_carry_mask (digit # digits) =
    threshold5_digit digit * 10 ^ length digits +
      double_reverse_source_carry_mask digits"
  by (simp add: double_reverse_source_carry_mask_def
      double_reverse_msf_value_cons)

lemma double_reverse_source_carry_prefix_cons:
  "double_reverse_source_carry_prefix (digit # digits) =
    threshold5_digit digit * (10 ^ length digits div 10) +
      double_reverse_source_carry_prefix digits"
  by (cases digits)
    (simp_all add: double_reverse_source_carry_prefix_def
      double_reverse_msf_value_cons)

lemma double_reverse_source_carry_mask_split:
  assumes nonempty: "source \<noteq> []"
  shows "double_reverse_source_carry_mask source =
    10 * double_reverse_source_carry_prefix source +
      threshold5_digit (last source)"
proof -
  have split: "source = butlast source @ [last source]"
    by (rule sym, rule append_butlast_last_id[OF nonempty])
  have mapped_source:
    "map threshold5_digit source =
      map threshold5_digit (butlast source @ [last source])"
    by (rule arg_cong[OF split])
  have mapped:
    "map threshold5_digit source =
      map threshold5_digit (butlast source) @ [threshold5_digit (last source)]"
    using mapped_source by (simp only: map_append list.map)
  show ?thesis
    unfolding double_reverse_source_carry_mask_def
      double_reverse_source_carry_prefix_def
    using mapped
    by (simp only: mapped double_reverse_msf_value_append_digit)
qed

lemma double_reverse_source_carry_mask_div10:
  assumes nonempty: "source \<noteq> []"
  shows "double_reverse_source_carry_mask source div 10 =
    double_reverse_source_carry_prefix source"
proof -
  have split: "double_reverse_source_carry_mask source =
      10 * double_reverse_source_carry_prefix source +
        threshold5_digit (last source)"
    by (rule double_reverse_source_carry_mask_split[OF nonempty])
  have carry_small: "threshold5_digit (last source) < 10"
    by (simp add: threshold5_digit_def)
  show ?thesis using split carry_small
    by (simp add: div_add1_eq mult.commute)
qed

lemma double_reverse_forward_pass_msf_carry_cut:
  assumes decimal: "list_all (\<lambda>digit. digit < 10) source"
      and incoming: "incoming \<le> 1"
  shows "double_reverse_msf_value
      (fst (double_reverse_forward_pass source incoming)) +
      10 * double_reverse_source_carry_mask source =
    2 * double_reverse_msf_value source +
      incoming * (10 ^ length source div 10) +
      double_reverse_source_carry_prefix source"
  using decimal incoming
proof (induction source arbitrary: incoming)
  case Nil
  then show ?case
    by (simp add: double_reverse_source_carry_mask_def
        double_reverse_source_carry_prefix_def double_reverse_msf_value_def)
next
  case (Cons digit rest)
  have digit_bound: "digit < 10" using Cons.prems(1) by simp
  have rest_decimal: "list_all (\<lambda>item. item < 10) rest"
    using Cons.prems(1) by simp
  have first_carry: "threshold5_digit digit \<le> 1"
    by (simp add: threshold5_digit_def)
  have one_cell:
    "(2 * digit + incoming) mod 10 + 10 * threshold5_digit digit =
      2 * digit + incoming"
    using decimal_double_digit_carry[OF digit_bound Cons.prems(2)]
    by (simp add: threshold5_digit_def)
  obtain tail_output tail_outgoing where tail_pass:
    "double_reverse_forward_pass rest (threshold5_digit digit) =
      (tail_output, tail_outgoing)"
    by (cases "double_reverse_forward_pass rest (threshold5_digit digit)") auto
  have first_pass:
    "double_reverse_forward_pass [digit] incoming =
      ([(2 * digit + incoming) mod 10], threshold5_digit digit)"
    using double_reverse_forward_single_digit[OF digit_bound Cons.prems(2)]
    unfolding threshold5_digit_def by simp
  have split:
    "double_reverse_forward_pass (digit # rest) incoming =
      ((2 * digit + incoming) mod 10 # tail_output, tail_outgoing)"
    using double_reverse_forward_pass_append[of "[digit]" rest incoming]
      first_pass tail_pass by (simp add: Let_def)
  have tail_exact:
    "double_reverse_msf_value tail_output +
        10 * double_reverse_source_carry_mask rest =
      2 * double_reverse_msf_value rest +
        threshold5_digit digit * (10 ^ length rest div 10) +
        double_reverse_source_carry_prefix rest"
    using Cons.IH[OF rest_decimal first_carry] tail_pass by simp
  have prefix:
    "double_reverse_source_carry_prefix (digit # rest) =
      threshold5_digit digit * (10 ^ length rest div 10) +
        double_reverse_source_carry_prefix rest"
    by (rule double_reverse_source_carry_prefix_cons)
  have output_cons:
    "double_reverse_msf_value
        (fst (double_reverse_forward_pass (digit # rest) incoming)) =
      (2 * digit + incoming) mod 10 * 10 ^ length rest +
        double_reverse_msf_value tail_output"
  proof -
    have tail_length: "length tail_output = length rest"
      using double_reverse_forward_pass_length[of rest "threshold5_digit digit"]
        tail_pass by simp
    show ?thesis
      by (simp only: split fst_conv double_reverse_msf_value_cons tail_length)
  qed
  have source_cons:
    "double_reverse_msf_value (digit # rest) =
      digit * 10 ^ length rest + double_reverse_msf_value rest"
    by (rule double_reverse_msf_value_cons)
  have mask_cons:
    "double_reverse_source_carry_mask (digit # rest) =
      threshold5_digit digit * 10 ^ length rest +
        double_reverse_source_carry_mask rest"
    by (rule double_reverse_source_carry_mask_cons)
  have head_cell:
    "(2 * digit + incoming) mod 10 * 10 ^ length rest +
        10 * threshold5_digit digit * 10 ^ length rest =
      (2 * digit + incoming) * 10 ^ length rest"
    using arg_cong[OF one_cell, where f="\<lambda>value. value * 10 ^ length rest"]
    by (simp add: algebra_simps)
  have source_power:
    "(10::nat) ^ length (digit # rest) div 10 = 10 ^ length rest"
    by (simp add: power_Suc)
  show ?case
    using output_cons source_cons mask_cons prefix tail_exact head_cell source_power
    by (simp add: algebra_simps)
qed

lemma double_reverse_four_port_closed_word_value_by_pass:
  assumes decimal: "list_all (\<lambda>digit. digit < 10) source"
  shows "double_reverse_msf_value
      (double_reverse_four_port_closed_word
        (double_reverse_four_port_row source 0 0)) =
    (if double_reverse_forward_out
          (double_reverse_four_port_row source 0 0) = 0
     then 2 * double_reverse_msf_value
          (fst (double_reverse_forward_pass source 0))
     else 2 + 20 * double_reverse_msf_value
          (fst (double_reverse_forward_pass source 0)))"
proof -
  let ?middle = "fst (double_reverse_forward_pass source 0)"
  let ?forward = "snd (double_reverse_forward_pass source 0)"
  let ?reverse_result = "double_reverse_reverse_pass ?middle 0"
  let ?output = "fst ?reverse_result"
  let ?reverse = "snd ?reverse_result"
  let ?q = "double_reverse_msf_value ?middle"
  have forward_bound: "?forward \<le> 1"
    using double_reverse_forward_pass_final_carry[OF decimal, of 0]
    by (cases source) (simp_all add: threshold5_digit_def)
  have middle_decimal: "list_all (\<lambda>digit. digit < 10) ?middle"
    by (rule double_reverse_forward_pass_output_digits[OF decimal]) simp
  have reverse_bound: "?reverse \<le> 1"
    using double_reverse_reverse_pass_final_carry[OF middle_decimal, of 0]
    by (cases ?middle) (simp_all add: threshold5_digit_def)
  have reverse_value:
    "double_reverse_msf_value ?output +
        10 ^ length ?middle * ?reverse = 2 * ?q"
    using double_reverse_reverse_pass_value[OF middle_decimal, of 0]
    by (simp add: double_reverse_msf_value_def)
  have output_length: "length ?output = length ?middle"
    using double_reverse_reverse_pass_length[of ?middle 0] by simp
  have row:
    "double_reverse_four_port_row source 0 0 =
      \<lparr>double_reverse_forward_out=?forward,
       double_reverse_reverse_out=?reverse,
       double_reverse_output_word=?output\<rparr>"
    unfolding double_reverse_four_port_row_def
    by (simp add: Let_def case_prod_beta)
  have closed_prefix:
    "double_reverse_msf_value
      ((if ?reverse = 1 then [1] else []) @ ?output) = 2 * ?q"
    using reverse_bound reverse_value output_length
    by (cases ?reverse)
      (simp_all add: double_reverse_msf_value_cons add.commute)
  have closed:
    "double_reverse_four_port_closed_word
        (double_reverse_four_port_row source 0 0) =
      (if ?reverse = 1 then [1] else []) @ ?output @
        (if ?forward = 1 then [2] else [])"
    using row by (simp add: double_reverse_four_port_closed_word_def)
  show ?thesis
  proof (cases ?forward)
    case 0
    then show ?thesis using closed_prefix closed row
      by simp
  next
    case (Suc count)
    have forward_one: "?forward = 1"
      using forward_bound Suc by simp
    have grown_word:
      "double_reverse_four_port_closed_word
          (double_reverse_four_port_row source 0 0) =
        ((if ?reverse = 1 then [1] else []) @ ?output) @ [2]"
      using closed forward_one by simp
    have grown_value:
      "double_reverse_msf_value
          (double_reverse_four_port_closed_word
            (double_reverse_four_port_row source 0 0)) = 2 + 20 * ?q"
    proof -
      have "double_reverse_msf_value
          (double_reverse_four_port_closed_word
            (double_reverse_four_port_row source 0 0)) =
        10 * double_reverse_msf_value
          ((if ?reverse = 1 then [1] else []) @ ?output) + 2"
        by (simp only: grown_word double_reverse_msf_value_append_digit)
      then show ?thesis by (simp only: closed_prefix)
    qed
    show ?thesis using grown_value row forward_one by simp
  qed
qed

theorem double_reverse_four_port_source_affine_carry:
  assumes canonical: "double_reverse_canonical_source source"
  shows "int (double_reverse_T_run 2 (double_reverse_msf_value source)) =
    (if threshold5_digit (last source) = 0 then
       4 * int (double_reverse_msf_value source) -
         198 * int (double_reverse_source_carry_mask source div 10)
     else
       40 * int (double_reverse_msf_value source) -
         198 * int (double_reverse_source_carry_mask source))"
proof -
  have nonempty: "source \<noteq> []"
    using canonical unfolding double_reverse_canonical_source_def by simp
  have decimal: "list_all (\<lambda>digit. digit < 10) source"
    using canonical unfolding double_reverse_canonical_source_def by simp
  let ?middle = "fst (double_reverse_forward_pass source 0)"
  let ?growth = "threshold5_digit (last source)"
  let ?mask = "double_reverse_source_carry_mask source"
  let ?prefix = "double_reverse_source_carry_prefix source"
  let ?value = "double_reverse_msf_value source"
  let ?q = "double_reverse_msf_value ?middle"
  have growth_bound: "?growth \<le> 1"
    by (simp add: threshold5_digit_def)
  have pass_growth:
    "snd (double_reverse_forward_pass source 0) = ?growth"
    using double_reverse_forward_pass_final_carry[OF decimal, of 0]
      nonempty by simp
  have carry_split: "?mask = 10 * ?prefix + ?growth"
    using double_reverse_source_carry_mask_split[OF nonempty] by simp
  have carry_cut:
    "?q + 10 * ?mask = 2 * ?value + ?prefix"
    using double_reverse_forward_pass_msf_carry_cut[OF decimal, of 0]
    by (simp add: double_reverse_source_carry_prefix_def)
  have endpoint_by_row:
    "int (double_reverse_T_run 2 ?value) =
      (if ?growth = 0 then 2 * int ?q else 2 + 20 * int ?q)"
  proof -
    have t2:
      "double_reverse_msf_value
          (double_reverse_four_port_closed_word
            (double_reverse_four_port_row source 0 0)) =
        double_reverse_T_run 2 ?value"
      by (rule double_reverse_four_port_closed_word_numeric_t2[OF canonical])
    have row_value:
      "double_reverse_msf_value
          (double_reverse_four_port_closed_word
            (double_reverse_four_port_row source 0 0)) =
        (if ?growth = 0 then 2 * ?q else 2 + 20 * ?q)"
    proof -
      have pass_value:
        "double_reverse_msf_value
            (double_reverse_four_port_closed_word
              (double_reverse_four_port_row source 0 0)) =
          (if double_reverse_forward_out
                (double_reverse_four_port_row source 0 0) = 0
           then 2 * ?q else 2 + 20 * ?q)"
        using double_reverse_four_port_closed_word_value_by_pass[OF decimal]
        by simp
      have row_growth:
        "double_reverse_forward_out (double_reverse_four_port_row source 0 0) =
          ?growth"
        using pass_growth
        by (simp add: double_reverse_four_port_row_def Let_def case_prod_beta)
      show ?thesis using pass_value row_growth by simp
    qed
    have endpoint_nat:
      "double_reverse_T_run 2 ?value =
        (if ?growth = 0 then 2 * ?q else 2 + 20 * ?q)"
      by (rule trans[OF t2[symmetric] row_value])
    show ?thesis
      using arg_cong[OF endpoint_nat, where f=int] by simp
  qed
  show ?thesis
  proof (cases ?growth)
    case 0
    have mask: "?mask = 10 * ?prefix"
      using carry_split 0 by simp
    have prefix: "?mask div 10 = ?prefix"
      using double_reverse_source_carry_mask_div10[OF nonempty] .
    have cut_int:
      "int ?q + 10 * int ?mask = 2 * int ?value + int ?prefix"
      using arg_cong[OF carry_cut, where f=int] by simp
    have endpoint: "int (double_reverse_T_run 2 ?value) = 2 * int ?q"
      using endpoint_by_row 0 by simp
    show ?thesis using endpoint cut_int mask prefix 0
      by (simp; linarith)
  next
    case (Suc count)
    have growth: "?growth = 1"
      using growth_bound Suc by simp
    have mask: "?mask = 10 * ?prefix + 1"
      using carry_split growth by simp
    have cut_int:
      "int ?q + 10 * int ?mask = 2 * int ?value + int ?prefix"
      using arg_cong[OF carry_cut, where f=int] by simp
    have endpoint:
      "int (double_reverse_T_run 2 ?value) = 2 + 20 * int ?q"
      using endpoint_by_row growth by simp
    show ?thesis using endpoint cut_int mask growth
      by (simp; linarith)
  qed
qed

theorem double_reverse_four_port_two_macro_defect_exact:
  assumes first_source: "double_reverse_canonical_source source"
      and second_source: "double_reverse_canonical_source next_source"
      and successor:
        "next_source = double_reverse_four_port_closed_word
          (double_reverse_four_port_row source 0 0)"
      and one_birth:
        "threshold5_digit (last source) +
          threshold5_digit (last next_source) = 1"
  defines "g0 \<equiv> threshold5_digit (last source)"
      and "g1 \<equiv> threshold5_digit (last next_source)"
      and "c0 \<equiv> double_reverse_source_carry_mask source"
      and "c1 \<equiv> double_reverse_source_carry_mask next_source"
  shows "int (double_reverse_msf_value
        (double_reverse_four_port_closed_word
          (double_reverse_four_port_row next_source 0 0))) =
      160 * int (double_reverse_msf_value source) -
        198 * int (4 * c0 + (if g1 = 0 then c1 div 10 else c1))"
proof -
  have g0_bound: "g0 \<le> 1"
    unfolding g0_def by (simp add: threshold5_digit_def)
  have g1_bound: "g1 \<le> 1"
    unfolding g1_def by (simp add: threshold5_digit_def)
  have g0_g1: "g0 = 1 \<and> g1 = 0 \<or> g0 = 0 \<and> g1 = 1"
    using one_birth g0_bound g1_bound unfolding g0_def g1_def by presburger
  have next_exact:
    "int (double_reverse_msf_value next_source) =
      int (double_reverse_T_run 2 (double_reverse_msf_value source))"
    using successor
      double_reverse_four_port_closed_word_numeric_t2[OF first_source]
    by simp
  have final_exact:
    "int (double_reverse_msf_value
        (double_reverse_four_port_closed_word
          (double_reverse_four_port_row next_source 0 0))) =
      int (double_reverse_T_run 2 (double_reverse_msf_value next_source))"
    by (rule arg_cong[OF double_reverse_four_port_closed_word_numeric_t2
      [OF second_source]])
  have first_affine:
    "int (double_reverse_msf_value next_source) =
      (if g0 = 0 then
         4 * int (double_reverse_msf_value source) - 198 * int (c0 div 10)
       else 40 * int (double_reverse_msf_value source) - 198 * int c0)"
    using double_reverse_four_port_source_affine_carry[OF first_source]
      next_exact unfolding g0_def c0_def by simp
  have second_affine:
    "int (double_reverse_msf_value
        (double_reverse_four_port_closed_word
          (double_reverse_four_port_row next_source 0 0))) =
      (if g1 = 0 then
         4 * int (double_reverse_msf_value next_source) - 198 * int (c1 div 10)
       else 40 * int (double_reverse_msf_value next_source) - 198 * int c1)"
    using double_reverse_four_port_source_affine_carry[OF second_source]
      final_exact unfolding g1_def c1_def by simp
  have source_nonempty: "source \<noteq> []"
    using first_source unfolding double_reverse_canonical_source_def by simp
  have c0_split:
    "c0 = 10 * double_reverse_source_carry_prefix source + g0"
    using double_reverse_source_carry_mask_split[OF source_nonempty]
    unfolding c0_def g0_def .
  have c0_div:
    "c0 div 10 = double_reverse_source_carry_prefix source"
    using double_reverse_source_carry_mask_div10[OF source_nonempty]
    unfolding c0_def .
  show ?thesis
  proof (cases "g0 = 1")
    case True
    then have g0: "g0=1" and g1: "g1=0" using g0_g1 by auto
    have second_value:
      "int (double_reverse_msf_value
          (double_reverse_four_port_closed_word
            (double_reverse_four_port_row next_source 0 0))) =
        4 * int (double_reverse_msf_value next_source) - 198 * int (c1 div 10)"
      using second_affine g1 by simp
    show ?thesis using first_affine second_value g0 g1
      by (simp add: algebra_simps)
  next
    case False
    then have g0: "g0=0" and g1: "g1=1" using g0_g1 by auto
    have c0_ten: "c0 = 10 * (c0 div 10)"
      using c0_split c0_div g0 by simp
    have second_value:
      "int (double_reverse_msf_value
          (double_reverse_four_port_closed_word
            (double_reverse_four_port_row next_source 0 0))) =
        40 * int (double_reverse_msf_value next_source) - 198 * int c1"
      using second_affine g1 by simp
    show ?thesis using first_affine second_value c0_ten g0 g1
      by (simp add: algebra_simps)
  qed
qed

text \<open>The carry correction in the source-affine action prevents its
coefficient from being read as an exact normalized mantissa rotation.  This
bounded seed calculation records the concrete counterexample; it asserts no
eventual period for the seed orbit.\<close>

theorem double_reverse_seed_168_four_step_rotation_correction:
  "double_reverse_T_run 4 168 = 16188 \<and>
   (1400::nat) * 16188 = (1349::nat) * ((100::nat) * 168) \<and>
   (5::nat) * 16188 \<noteq> (8::nat) * ((100::nat) * 168) \<and>
   (25::nat) * 16188 \<noteq> (4::nat) * ((100::nat) * 168)"
proof -
  have step1: "double_reverse_T 168 = 1722"
    by (simp add: double_reverse_T_def double_reverse_reverse10.simps
        double_reverse_decimal_digits.simps)
  have step2: "double_reverse_T 1722 = 4542"
    by (simp add: double_reverse_T_def double_reverse_reverse10.simps
        double_reverse_decimal_digits.simps)
  have step3: "double_reverse_T 4542 = 4908"
    by (simp add: double_reverse_T_def double_reverse_reverse10.simps
        double_reverse_decimal_digits.simps)
  have step4: "double_reverse_T 4908 = 16188"
    by (simp add: double_reverse_T_def double_reverse_reverse10.simps
        double_reverse_decimal_digits.simps)
  have four_as_suc: "(4::nat) = Suc (Suc (Suc (Suc 0)))" by simp
  have iterated:
    "(double_reverse_T ^^ Suc (Suc (Suc (Suc 0)))) 168 = 16188"
    by (simp add: funpow.simps step1 step2 step3 step4)
  have endpoint: "double_reverse_T_run 4 168 = 16188"
    unfolding double_reverse_T_run_def
    using iterated four_as_suc by (simp only: four_as_suc iterated)
  show ?thesis using endpoint by simp
qed

lemmas double_reverse_four_port_defect_refinement_audit_bundle =
  double_reverse_source_carry_mask_cons
  double_reverse_source_carry_prefix_cons
  double_reverse_source_carry_mask_split
  double_reverse_source_carry_mask_div10
  double_reverse_forward_pass_msf_carry_cut
  double_reverse_four_port_closed_word_value_by_pass
  double_reverse_four_port_source_affine_carry
  double_reverse_four_port_two_macro_defect_exact
  double_reverse_seed_168_four_step_rotation_correction

ML \<open>
  val checked = @{thms double_reverse_four_port_defect_refinement_audit_bundle};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Double-reverse four-port defect refinement depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked
    then error "Skipped double-reverse four-port defect refinement proof" else ();
\<close>

end
