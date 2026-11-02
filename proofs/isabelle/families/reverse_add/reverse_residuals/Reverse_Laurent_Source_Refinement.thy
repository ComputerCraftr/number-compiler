theory Reverse_Laurent_Source_Refinement
  imports Reverse_Symmetric_Publisher_Bridge
    Reverse_Mod7_Controlled_Action Reverse_Mod99_Accumulator_Moore
begin

text \<open>The Laurent observer below is a source-bound scalar refinement.
It starts from the actual symmetric pair field, reconstructs its canonical
Q19 half, and uses the existing two-port publisher theorem to identify the
physical successor. The modular laws do not select a future carry word or
authorize a temporal skip.\<close>

definition reverse_laurent_source_half :: "nat list \<Rightarrow> nat list" where
  "reverse_laurent_source_half ss = take ((length ss + 1) div 2) ss"

definition reverse_laurent_source_odd :: "nat list \<Rightarrow> bool" where
  "reverse_laurent_source_odd ss = odd (length ss)"

lemma reverse_laurent_half_reconstructs_symmetric_source:
  assumes symmetric: "rev ss = ss"
  shows "punctured_q19_decode_half (reverse_laurent_source_half ss)
      (reverse_laurent_source_odd ss) = ss"
proof (cases "even (length ss)")
  case even_length: True
  then obtain k where length: "length ss = 2 * k"
    by (rule evenE)
  have half:
    "reverse_laurent_source_half ss = take k ss"
    using length by (simp add: reverse_laurent_source_half_def)
  have suffix: "drop k ss = rev (take k ss)"
  proof -
    have "drop k ss = drop k (rev ss)"
      using symmetric by simp
    also have "... = rev (take (length ss - k) ss)"
      by (simp add: drop_rev)
    also have "... = rev (take k ss)"
      using length by simp
    finally show ?thesis .
  qed
  have split: "take k ss @ drop k ss = ss"
    by simp
  show ?thesis
    using even_length half suffix split
    by (simp add: punctured_q19_decode_half_def
        reverse_laurent_source_odd_def)
next
  case odd_length: False
  have is_odd: "odd (length ss)"
    using odd_length by simp
  then obtain k where length: "length ss = 2 * k + 1"
    by (rule oddE)
  have half:
    "reverse_laurent_source_half ss = take (Suc k) ss"
    using length by (simp add: reverse_laurent_source_half_def)
  have index: "k < length ss"
    using length by simp
  have take_split: "take (Suc k) ss = take k ss @ [ss!k]"
    by (rule take_Suc_conv_app_nth[OF index])
  have suffix: "drop (Suc k) ss = rev (take k ss)"
  proof -
    have "drop (Suc k) ss = drop (Suc k) (rev ss)"
      using symmetric by simp
    also have "... = rev (take (length ss - Suc k) ss)"
      by (simp add: drop_rev)
    also have "... = rev (take k ss)"
      using length by simp
    finally show ?thesis .
  qed
  have split: "take (Suc k) ss @ drop (Suc k) ss = ss"
    by simp
  have last_half: "butlast (take (Suc k) ss) = take k ss"
    by (simp add: take_split)
  show ?thesis
    using odd_length half take_split suffix split last_half
    by (simp add: punctured_q19_decode_half_def
        reverse_laurent_source_odd_def)
qed

theorem reverse_laurent_q19_publisher_refines_source:
  assumes valid: "valid_pair ss"
  shows "reverse_two_port_publisher
      (punctured_q19_decode_half (reverse_laurent_source_half ss)
        (reverse_laurent_source_odd ss)) = step ss"
proof -
  have symmetric: "rev ss = ss"
    using valid by (simp add: valid_pair_def)
  have reconstruction:
    "punctured_q19_decode_half (reverse_laurent_source_half ss)
        (reverse_laurent_source_odd ss) = ss"
    by (rule reverse_laurent_half_reconstructs_symmetric_source[OF symmetric])
  show ?thesis
    using reverse_two_port_publisher_refines_step[OF valid] reconstruction
    by simp
qed

corollary reverse_laurent_q19_carry_normalization_refines_source:
  assumes valid: "valid_pair ss"
  shows "digits (reverse_two_port_publisher
        (punctured_q19_decode_half (reverse_laurent_source_half ss)
          (reverse_laurent_source_odd ss))) = digits (step ss)"
    and "carry_out False (reverse_two_port_publisher
        (punctured_q19_decode_half (reverse_laurent_source_half ss)
          (reverse_laurent_source_odd ss))) = carry_out False (step ss)"
  using reverse_laurent_q19_publisher_refines_source[OF valid] by simp_all

definition reverse_laurent_defect :: "nat list \<Rightarrow> int" where
  "reverse_laurent_defect ss =
    (int (reverse_add_pair_reverse ss) -
      int (reverse_add_pair_term ss)) div 99"

lemma reverse_laurent_defect_exact:
  assumes source_mod11: "reverse_add_pair_term ss mod 11 = 0"
  shows "int (reverse_add_pair_reverse ss) -
      int (reverse_add_pair_term ss) = 99 * reverse_laurent_defect ss"
proof -
  let ?x = "reverse_add_pair_term ss"
  let ?rx = "reverse_add_pair_reverse ss"
  have reverse_mod9: "?rx mod 9 = ?x mod 9"
    by (simp add: reverse_add_pair_reverse_def reverse_add_pair_term_def
        decimal_list_value_reverse_mod9)
  have reverse_mod11: "?rx mod 11 = 0"
  proof -
    have reverse_rule:
      "?rx mod 11 =
        ((if even (length (digits ss)) then 10 else 1) * ?x) mod 11"
      by (simp add: reverse_add_pair_reverse_def reverse_add_pair_term_def
          decimal_list_value_reverse_mod11)
    have product_zero: "(10 * ?x) mod 11 = 0"
      using source_mod11 by (simp add: mod_mult_right_eq[symmetric])
    show ?thesis using reverse_rule source_mod11 product_zero
      by (cases "even (length (digits ss))"; simp)
  qed
  have both_mod99: "?rx mod 99 = ?x mod 99"
  proof (rule mod_9_11_equal_mod99)
    show "?rx mod 9 = ?x mod 9" by (rule reverse_mod9)
    show "?rx mod 11 = ?x mod 11"
      using reverse_mod11 source_mod11 by simp
  qed
  have integer_residue: "(int ?rx) mod 99 = (int ?x) mod 99"
  proof -
    have cast: "int (?rx mod 99) = int (?x mod 99)"
      by (rule arg_cong[where f="\<lambda>value::nat. int value", OF both_mod99])
    show ?thesis using cast
      by (simp only: of_nat_mod of_nat_numeral)
  qed
  have difference_residue:
    "(int ?rx - int ?x) mod (99::int) = 0"
  proof -
    have same_difference:
      "(int ?rx - int ?x) mod (99::int) =
        (int ?x - int ?x) mod (99::int)"
      by (rule mod_diff_cong[OF integer_residue]) simp
    show ?thesis using same_difference by simp
  qed
  have division:
    "(int ?rx - int ?x) div 99 * 99 +
       (int ?rx - int ?x) mod 99 = int ?rx - int ?x"
    by (rule div_mult_mod_eq)
  show ?thesis
    using difference_residue division
    by (simp add: reverse_laurent_defect_def mult.commute)
qed

lemma reverse_laurent_defect_mod7_from_mod693_residues:
  assumes source_mod11: "reverse_add_pair_term ss mod 11 = 0"
  shows "((int (reverse_add_pair_reverse ss mod 693) -
      int (reverse_add_pair_term ss mod 693)) mod 693) div 99 =
    reverse_laurent_defect ss mod 7"
proof -
  have reverse_residue:
    "int (reverse_add_pair_reverse ss mod 693) =
      int (reverse_add_pair_reverse ss) mod 693"
    by (simp only: of_nat_mod of_nat_numeral)
  have source_residue:
    "int (reverse_add_pair_term ss mod 693) =
      int (reverse_add_pair_term ss) mod 693"
    by (simp only: of_nat_mod of_nat_numeral)
  have residue_difference:
    "(int (reverse_add_pair_reverse ss mod 693) -
        int (reverse_add_pair_term ss mod 693)) mod 693 =
      (int (reverse_add_pair_reverse ss) -
        int (reverse_add_pair_term ss)) mod 693"
    using reverse_residue source_residue by (simp add: mod_diff_eq)
  have defect_exact:
    "int (reverse_add_pair_reverse ss) -
        int (reverse_add_pair_term ss) =
      99 * reverse_laurent_defect ss"
    by (rule reverse_laurent_defect_exact[OF source_mod11])
  have scaled_mod:
    "(99 * reverse_laurent_defect ss) mod 693 =
      99 * (reverse_laurent_defect ss mod 7)"
    using mod_mult_mult1[of "99::int" "reverse_laurent_defect ss" 7]
    by simp
  have residue_exact:
    "(int (reverse_add_pair_reverse ss mod 693) -
        int (reverse_add_pair_term ss mod 693)) mod 693 =
      99 * (reverse_laurent_defect ss mod 7)"
    using residue_difference defect_exact scaled_mod by simp
  show ?thesis using residue_exact by simp
qed

lemma reverse_laurent_decimal_value_mod2_head:
  assumes nonempty: "ds \<noteq> []"
  shows "decimal_list_value ds mod 2 = hd ds mod 2"
proof -
  obtain head rest where ds: "ds = head # rest"
    using nonempty by (cases ds) auto
  have even_tail: "(10 * decimal_list_value rest) mod 2 = 0"
  proof -
    have factor:
      "10 * decimal_list_value rest =
        2 * (5 * decimal_list_value rest)"
      by (simp add: mult.assoc)
    show ?thesis using factor by simp
  qed
  show ?thesis using even_tail
    by (simp add: ds decimal_list_value.simps mod_add_eq[symmetric])
qed

lemma reverse_laurent_defect_parity_from_normalized_ends:
  assumes valid: "valid_pair ss"
      and source_mod11: "reverse_add_pair_term ss mod 11 = 0"
  shows "reverse_laurent_defect ss mod 2 =
      (int (last (digits ss)) - int (hd (digits ss))) mod 2"
proof -
  have normalized_nonempty: "digits ss \<noteq> []"
    using valid by (auto simp: valid_pair_def digits_def)
  have forward_mod2:
    "int (reverse_add_pair_term ss) mod 2 =
      int (hd (digits ss)) mod 2"
  proof -
    have natural:
      "reverse_add_pair_term ss mod 2 = hd (digits ss) mod 2"
      using reverse_laurent_decimal_value_mod2_head[OF normalized_nonempty]
      by (simp add: reverse_add_pair_term_def)
    have cast:
      "int (reverse_add_pair_term ss mod 2) =
        int (hd (digits ss) mod 2)"
      by (rule arg_cong[where f="\<lambda>value::nat. int value", OF natural])
    show ?thesis using cast
      by (simp only: of_nat_mod of_nat_numeral)
  qed
  have reverse_mod2:
    "int (reverse_add_pair_reverse ss) mod 2 =
      int (last (digits ss)) mod 2"
  proof -
    have natural:
      "reverse_add_pair_reverse ss mod 2 = last (digits ss) mod 2"
    proof -
      have reversed_nonempty: "rev (digits ss) \<noteq> []"
        using normalized_nonempty by simp
      have head:
        "decimal_list_value (rev (digits ss)) mod 2 =
          hd (rev (digits ss)) mod 2"
        by (rule reverse_laurent_decimal_value_mod2_head[OF reversed_nonempty])
      show ?thesis using head normalized_nonempty
        by (simp add: reverse_add_pair_reverse_def hd_rev)
    qed
    have cast:
      "int (reverse_add_pair_reverse ss mod 2) =
        int (last (digits ss) mod 2)"
      by (rule arg_cong[where f="\<lambda>value::nat. int value", OF natural])
    show ?thesis using cast
      by (simp only: of_nat_mod of_nat_numeral)
  qed
  have difference_mod2:
    "(int (reverse_add_pair_reverse ss) -
        int (reverse_add_pair_term ss)) mod 2 =
      (int (last (digits ss)) - int (hd (digits ss))) mod 2"
    by (rule mod_diff_cong[OF reverse_mod2 forward_mod2])
  have defect_mod2:
    "reverse_laurent_defect ss mod 2 =
      (int (reverse_add_pair_reverse ss) -
        int (reverse_add_pair_term ss)) mod 2"
    using reverse_laurent_defect_exact[OF source_mod11]
    by (simp add: mod_mult_left_eq[symmetric])
  show ?thesis using defect_mod2 difference_mod2 by simp
qed

definition reverse_laurent_even_update ::
    "int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int \<times> int" where
  "reverse_laurent_even_update a b x y reverse_y =
    (a + int y, b + int reverse_y - int x)"

lemma reverse_laurent_even_update_sum:
  "fst (reverse_laurent_even_update a b x y reverse_y) +
      snd (reverse_laurent_even_update a b x y reverse_y) =
    a + b + int y + int reverse_y - int x"
  by (simp add: reverse_laurent_even_update_def algebra_simps)

lemma reverse_laurent_sum_transport_mod:
  fixes a b x y z modulus :: int
  assumes source_sum: "(a + b) mod modulus = x mod modulus"
  shows "(a + b + y + z - x) mod modulus =
    (y + z) mod modulus"
proof -
  have cancelled_source:
    "(a + b - x) mod modulus = (x - x) mod modulus"
    by (rule mod_diff_cong[OF source_sum]) simp
  have regroup:
    "a + b + y + z - x = (a + b - x) + (y + z)"
    by (simp add: algebra_simps)
  have grouped:
    "(a + b + y + z - x) mod modulus =
      ((a + b - x) + (y + z)) mod modulus"
    by (simp only: regroup)
  have cancelled:
    "((a + b - x) + (y + z)) mod modulus =
      (y + z) mod modulus"
  proof -
    have "((a + b - x) + (y + z)) mod modulus =
        (((a + b - x) mod modulus) +
          ((y + z) mod modulus)) mod modulus"
      by (rule mod_add_eq[symmetric])
    also have "... = (((x - x) mod modulus) +
          ((y + z) mod modulus)) mod modulus"
      by (simp only: cancelled_source)
    also have "... = (y + z) mod modulus"
      by simp
    finally show ?thesis .
  qed
  show ?thesis by (rule trans[OF grouped cancelled])
qed

lemma reverse_laurent_mul_99_mod7:
  fixes t :: int
  shows "(99 * t) mod 7 = t mod 7"
proof -
  have coefficient: "(99::int) mod 7 = (1::int) mod 7" by simp
  have "(99 * t) mod 7 = (1 * t) mod 7"
    by (rule mod_mult_cong[OF coefficient refl])
  then show ?thesis by simp
qed

theorem reverse_laurent_two_tick_source_forcing:
  assumes valid: "valid_pair ss"
      and source_mod11: "reverse_add_pair_term ss mod 11 = 0"
  shows "int (reverse_add_pair_term (step (step ss))) =
      4 * int (reverse_add_pair_term ss) +
        99 * (2 * reverse_laurent_defect ss +
          reverse_laurent_defect (step ss))"
    and "fst (reverse_laurent_even_update a b
          (reverse_add_pair_term ss) (reverse_add_pair_term (step ss))
          (reverse_add_pair_reverse (step ss))) -
        snd (reverse_laurent_even_update a b
          (reverse_add_pair_term ss) (reverse_add_pair_term (step ss))
          (reverse_add_pair_reverse (step ss))) =
      (a - b) + int (reverse_add_pair_term ss) -
        99 * reverse_laurent_defect (step ss)"
proof -
  have successor_valid: "valid_pair (step ss)"
    by (rule valid_pair_successor[OF valid])
  have successor_mod11: "reverse_add_pair_term (step ss) mod 11 = 0"
    by (rule reverse_mod99_step_preserves_mod11_zero[OF valid source_mod11])
  have source_defect:
    "int (reverse_add_pair_reverse ss) -
        int (reverse_add_pair_term ss) =
      99 * reverse_laurent_defect ss"
    by (rule reverse_laurent_defect_exact[OF source_mod11])
  have source_reverse:
    "int (reverse_add_pair_reverse ss) =
      int (reverse_add_pair_term ss) +
        99 * reverse_laurent_defect ss"
    using source_defect by arith
  have successor_defect:
    "int (reverse_add_pair_reverse (step ss)) -
        int (reverse_add_pair_term (step ss)) =
      99 * reverse_laurent_defect (step ss)"
    by (rule reverse_laurent_defect_exact[OF successor_mod11])
  have successor_reverse:
    "int (reverse_add_pair_reverse (step ss)) =
      int (reverse_add_pair_term (step ss)) +
        99 * reverse_laurent_defect (step ss)"
    using successor_defect by arith
  have first_successor:
    "reverse_add_pair_term (step ss) = reverse_add_pair_term ss +
        reverse_add_pair_reverse ss"
    by (rule reverse_add_completed_pair_successor[OF valid])
  have second_successor:
    "reverse_add_pair_term (step (step ss)) =
        reverse_add_pair_term (step ss) + reverse_add_pair_reverse (step ss)"
    by (rule reverse_add_completed_pair_successor[OF successor_valid])
  have successor_value:
    "int (reverse_add_pair_term (step ss)) =
      2 * int (reverse_add_pair_term ss) +
        99 * reverse_laurent_defect ss"
    using first_successor source_reverse by (simp add: algebra_simps)
  have source_two_tick:
    "int (reverse_add_pair_term (step (step ss))) =
      4 * int (reverse_add_pair_term ss) +
        99 * (2 * reverse_laurent_defect ss +
          reverse_laurent_defect (step ss))"
    using second_successor successor_value successor_reverse
    by (simp add: algebra_simps)
  show first:
    "int (reverse_add_pair_term (step (step ss))) =
      4 * int (reverse_add_pair_term ss) +
        99 * (2 * reverse_laurent_defect ss +
          reverse_laurent_defect (step ss))"
    by (rule source_two_tick)
  show second:
    "fst (reverse_laurent_even_update a b
          (reverse_add_pair_term ss) (reverse_add_pair_term (step ss))
          (reverse_add_pair_reverse (step ss))) -
        snd (reverse_laurent_even_update a b
          (reverse_add_pair_term ss) (reverse_add_pair_term (step ss))
          (reverse_add_pair_reverse (step ss))) =
      (a - b) + int (reverse_add_pair_term ss) -
        99 * reverse_laurent_defect (step ss)"
    using successor_reverse
    by (simp add: reverse_laurent_even_update_def algebra_simps)
qed

corollary reverse_laurent_two_tick_mod7:
  assumes valid: "valid_pair ss"
      and source_mod11: "reverse_add_pair_term ss mod 11 = 0"
      and accumulator_sum_mod7:
        "(a + b) mod 7 = int (reverse_add_pair_term ss) mod 7"
  shows "int (reverse_add_pair_term (step (step ss))) mod 7 =
      (4 * int (reverse_add_pair_term ss) +
        2 * reverse_laurent_defect ss +
        reverse_laurent_defect (step ss)) mod 7"
    and "(fst (reverse_laurent_even_update a b
          (reverse_add_pair_term ss) (reverse_add_pair_term (step ss))
          (reverse_add_pair_reverse (step ss))) +
        snd (reverse_laurent_even_update a b
          (reverse_add_pair_term ss) (reverse_add_pair_term (step ss))
          (reverse_add_pair_reverse (step ss)))) mod 7 =
      (4 * int (reverse_add_pair_term ss) +
        2 * reverse_laurent_defect ss +
        reverse_laurent_defect (step ss)) mod 7"
    and "(fst (reverse_laurent_even_update a b
          (reverse_add_pair_term ss) (reverse_add_pair_term (step ss))
          (reverse_add_pair_reverse (step ss))) -
        snd (reverse_laurent_even_update a b
          (reverse_add_pair_term ss) (reverse_add_pair_term (step ss))
          (reverse_add_pair_reverse (step ss)))) mod 7 =
      ((a - b) + int (reverse_add_pair_term ss) -
        reverse_laurent_defect (step ss)) mod 7"
proof -
  note source_forcing =
    reverse_laurent_two_tick_source_forcing[OF valid source_mod11]
  have second_successor:
    "reverse_add_pair_term (step (step ss)) =
      reverse_add_pair_term (step ss) + reverse_add_pair_reverse (step ss)"
    by (rule reverse_add_completed_pair_successor
        [OF valid_pair_successor[OF valid]])
  have update_sum:
    "fst (reverse_laurent_even_update a b
          (reverse_add_pair_term ss) (reverse_add_pair_term (step ss))
          (reverse_add_pair_reverse (step ss))) +
        snd (reverse_laurent_even_update a b
          (reverse_add_pair_term ss) (reverse_add_pair_term (step ss))
          (reverse_add_pair_reverse (step ss))) =
      a + b + int (reverse_add_pair_term (step ss)) +
        int (reverse_add_pair_reverse (step ss)) -
        int (reverse_add_pair_term ss)"
    by (rule reverse_laurent_even_update_sum)
  have update_sum_transport:
    "(a + b + int (reverse_add_pair_term (step ss)) +
        int (reverse_add_pair_reverse (step ss)) -
        int (reverse_add_pair_term ss)) mod 7 =
      (int (reverse_add_pair_term (step ss)) +
        int (reverse_add_pair_reverse (step ss))) mod 7"
    by (rule reverse_laurent_sum_transport_mod[OF accumulator_sum_mod7])
  have update_sum_matches:
    "(fst (reverse_laurent_even_update a b
          (reverse_add_pair_term ss) (reverse_add_pair_term (step ss))
          (reverse_add_pair_reverse (step ss))) +
        snd (reverse_laurent_even_update a b
          (reverse_add_pair_term ss) (reverse_add_pair_term (step ss))
          (reverse_add_pair_reverse (step ss)))) mod 7 =
      int (reverse_add_pair_term (step (step ss))) mod 7"
    using update_sum second_successor update_sum_transport by simp
  have next_mod7: "int (reverse_add_pair_term (step (step ss))) mod 7 =
      (4 * int (reverse_add_pair_term ss) +
        2 * reverse_laurent_defect ss +
        reverse_laurent_defect (step ss)) mod 7"
  proof -
    let ?c = "2 * reverse_laurent_defect ss +
        reverse_laurent_defect (step ss)"
    have joined:
      "(4 * int (reverse_add_pair_term ss) + 99 * ?c) mod 7 =
        (4 * int (reverse_add_pair_term ss) + ?c) mod 7"
      by (rule mod_add_cong[OF refl reverse_laurent_mul_99_mod7])
    show ?thesis using source_forcing(1) joined
      by (simp add: algebra_simps)
  qed
  show "int (reverse_add_pair_term (step (step ss))) mod 7 =
      (4 * int (reverse_add_pair_term ss) +
        2 * reverse_laurent_defect ss +
        reverse_laurent_defect (step ss)) mod 7"
    by (rule next_mod7)
  show "(fst (reverse_laurent_even_update a b
          (reverse_add_pair_term ss) (reverse_add_pair_term (step ss))
          (reverse_add_pair_reverse (step ss))) +
        snd (reverse_laurent_even_update a b
          (reverse_add_pair_term ss) (reverse_add_pair_term (step ss))
          (reverse_add_pair_reverse (step ss)))) mod 7 =
      (4 * int (reverse_add_pair_term ss) +
        2 * reverse_laurent_defect ss +
        reverse_laurent_defect (step ss)) mod 7"
    using update_sum_matches next_mod7 by simp
  show "(fst (reverse_laurent_even_update a b
          (reverse_add_pair_term ss) (reverse_add_pair_term (step ss))
          (reverse_add_pair_reverse (step ss))) -
        snd (reverse_laurent_even_update a b
          (reverse_add_pair_term ss) (reverse_add_pair_term (step ss))
          (reverse_add_pair_reverse (step ss)))) mod 7 =
      ((a - b) + int (reverse_add_pair_term ss) -
        reverse_laurent_defect (step ss)) mod 7"
  proof -
    have difference_transport:
      "((a - b) + int (reverse_add_pair_term ss) -
          99 * reverse_laurent_defect (step ss)) mod 7 =
        ((a - b) + int (reverse_add_pair_term ss) -
          reverse_laurent_defect (step ss)) mod 7"
      by (rule mod_diff_cong[OF refl reverse_laurent_mul_99_mod7])
    show ?thesis using source_forcing(2) difference_transport by simp
  qed
qed

lemma reverse_laurent_scale_division_99:
  fixes a q r :: int
  assumes "q * 2 + r = a"
  shows "99 * a = 198 * q + 99 * r"
  using assms by linarith

lemma reverse_laurent_quotient_split_99:
  fixes head tail :: int
  shows "99 * (2 * head + tail) =
    198 * (head + tail div 2) + 99 * (tail mod 2)"
proof -
  have division: "(tail div 2) * 2 + tail mod 2 = tail"
    by (rule div_mult_mod_eq)
  have tail_split:
    "99 * tail = 198 * (tail div 2) + 99 * (tail mod 2)"
    by (rule reverse_laurent_scale_division_99[OF division])
  have head_expand:
    "99 * (2 * head + tail) = 198 * head + 99 * tail"
    by (simp add: algebra_simps)
  have combine:
    "198 * head +
        (198 * (tail div 2) + 99 * (tail mod 2)) =
      198 * (head + tail div 2) + 99 * (tail mod 2)"
    by (simp add: algebra_simps)
  show ?thesis
  proof -
    have "99 * (2 * head + tail) = 198 * head + 99 * tail"
      by (rule head_expand)
    also have "... = 198 * head +
        (198 * (tail div 2) + 99 * (tail mod 2))"
      by (simp only: tail_split)
    also have "... = 198 * (head + tail div 2) +
        99 * (tail mod 2)"
      by (rule combine)
    finally show ?thesis .
  qed
qed

corollary reverse_laurent_two_tick_mod198:
  assumes valid: "valid_pair ss"
      and source_mod11: "reverse_add_pair_term ss mod 11 = 0"
      and accumulator_sum_mod198:
        "(a + b) mod 198 = int (reverse_add_pair_term ss) mod 198"
  shows "int (reverse_add_pair_term (step (step ss))) mod 198 =
      (4 * int (reverse_add_pair_term ss) +
        99 * (reverse_laurent_defect (step ss) mod 2)) mod 198"
    and "(fst (reverse_laurent_even_update a b
          (reverse_add_pair_term ss) (reverse_add_pair_term (step ss))
          (reverse_add_pair_reverse (step ss))) +
        snd (reverse_laurent_even_update a b
          (reverse_add_pair_term ss) (reverse_add_pair_term (step ss))
          (reverse_add_pair_reverse (step ss)))) mod 198 =
      (4 * int (reverse_add_pair_term ss) +
        99 * (reverse_laurent_defect (step ss) mod 2)) mod 198"
    and "(fst (reverse_laurent_even_update a b
          (reverse_add_pair_term ss) (reverse_add_pair_term (step ss))
          (reverse_add_pair_reverse (step ss))) -
        snd (reverse_laurent_even_update a b
          (reverse_add_pair_term ss) (reverse_add_pair_term (step ss))
          (reverse_add_pair_reverse (step ss)))) mod 198 =
      ((a - b) + int (reverse_add_pair_term ss) -
        99 * (reverse_laurent_defect (step ss) mod 2)) mod 198"
proof -
  note source_forcing =
    reverse_laurent_two_tick_source_forcing[OF valid source_mod11]
  have quotient_split:
    "99 * (2 * reverse_laurent_defect ss +
        reverse_laurent_defect (step ss)) =
      198 * (reverse_laurent_defect ss +
        reverse_laurent_defect (step ss) div 2) +
        99 * (reverse_laurent_defect (step ss) mod 2)"
    by (rule reverse_laurent_quotient_split_99)
  have successor_split:
    "99 * reverse_laurent_defect (step ss) =
      198 * (reverse_laurent_defect (step ss) div 2) +
        99 * (reverse_laurent_defect (step ss) mod 2)"
  proof -
    have division:
      "(reverse_laurent_defect (step ss) div 2) * 2 +
          reverse_laurent_defect (step ss) mod 2 =
        reverse_laurent_defect (step ss)"
      by (rule div_mult_mod_eq)
    show ?thesis by (rule reverse_laurent_scale_division_99[OF division])
  qed
  have update_sum:
    "fst (reverse_laurent_even_update a b
          (reverse_add_pair_term ss) (reverse_add_pair_term (step ss))
          (reverse_add_pair_reverse (step ss))) +
        snd (reverse_laurent_even_update a b
          (reverse_add_pair_term ss) (reverse_add_pair_term (step ss))
          (reverse_add_pair_reverse (step ss))) =
      a + b + int (reverse_add_pair_term (step ss)) +
        int (reverse_add_pair_reverse (step ss)) -
        int (reverse_add_pair_term ss)"
    by (rule reverse_laurent_even_update_sum)
  have update_sum_transport:
    "(a + b + int (reverse_add_pair_term (step ss)) +
        int (reverse_add_pair_reverse (step ss)) -
        int (reverse_add_pair_term ss)) mod 198 =
      (int (reverse_add_pair_term (step ss)) +
        int (reverse_add_pair_reverse (step ss))) mod 198"
    by (rule reverse_laurent_sum_transport_mod[OF accumulator_sum_mod198])
  have second_successor:
    "reverse_add_pair_term (step (step ss)) =
      reverse_add_pair_term (step ss) + reverse_add_pair_reverse (step ss)"
    by (rule reverse_add_completed_pair_successor
        [OF valid_pair_successor[OF valid]])
  have update_sum_matches:
    "(fst (reverse_laurent_even_update a b
          (reverse_add_pair_term ss) (reverse_add_pair_term (step ss))
          (reverse_add_pair_reverse (step ss))) +
        snd (reverse_laurent_even_update a b
          (reverse_add_pair_term ss) (reverse_add_pair_term (step ss))
          (reverse_add_pair_reverse (step ss)))) mod 198 =
      int (reverse_add_pair_term (step (step ss))) mod 198"
    using update_sum second_successor update_sum_transport by simp
  have next_mod198: "int (reverse_add_pair_term (step (step ss))) mod 198 =
      (4 * int (reverse_add_pair_term ss) +
        99 * (reverse_laurent_defect (step ss) mod 2)) mod 198"
  proof -
    let ?x = "int (reverse_add_pair_term ss)"
    let ?k = "reverse_laurent_defect ss +
        reverse_laurent_defect (step ss) div 2"
    let ?r = "reverse_laurent_defect (step ss) mod 2"
    have forced:
      "int (reverse_add_pair_term (step (step ss))) =
        4 * ?x + (198 * ?k + 99 * ?r)"
      using source_forcing(1) quotient_split by simp
    have regroup:
      "4 * ?x + (198 * ?k + 99 * ?r) =
        (4 * ?x + 99 * ?r) + 198 * ?k"
      by (simp add: algebra_simps)
    have add_residue:
      "((4 * ?x + 99 * ?r) + 198 * ?k) mod 198 =
        ((4 * ?x + 99 * ?r) + (198 * ?k mod 198)) mod 198"
      by (rule mod_add_right_eq[symmetric])
    have multiple_residue: "(198 * ?k) mod 198 = 0"
      by (simp add: mod_mult_left_eq)
    have remove_multiple:
      "(4 * ?x + (198 * ?k + 99 * ?r)) mod 198 =
        (4 * ?x + 99 * ?r) mod 198"
      by (simp only: regroup add_residue multiple_residue add_0_right)
    show ?thesis by (simp only: forced remove_multiple)
  qed
  show "int (reverse_add_pair_term (step (step ss))) mod 198 =
      (4 * int (reverse_add_pair_term ss) +
        99 * (reverse_laurent_defect (step ss) mod 2)) mod 198"
    by (rule next_mod198)
  show "(fst (reverse_laurent_even_update a b
          (reverse_add_pair_term ss) (reverse_add_pair_term (step ss))
          (reverse_add_pair_reverse (step ss))) +
        snd (reverse_laurent_even_update a b
          (reverse_add_pair_term ss) (reverse_add_pair_term (step ss))
          (reverse_add_pair_reverse (step ss)))) mod 198 =
      (4 * int (reverse_add_pair_term ss) +
        99 * (reverse_laurent_defect (step ss) mod 2)) mod 198"
    using update_sum_matches next_mod198 by simp
  show "(fst (reverse_laurent_even_update a b
          (reverse_add_pair_term ss) (reverse_add_pair_term (step ss))
          (reverse_add_pair_reverse (step ss))) -
        snd (reverse_laurent_even_update a b
          (reverse_add_pair_term ss) (reverse_add_pair_term (step ss))
          (reverse_add_pair_reverse (step ss)))) mod 198 =
      ((a - b) + int (reverse_add_pair_term ss) -
        99 * (reverse_laurent_defect (step ss) mod 2)) mod 198"
  proof -
    let ?e = "reverse_laurent_defect (step ss)"
    let ?r = "?e mod 2"
    let ?prefix = "(a - b) + int (reverse_add_pair_term ss)"
    have split: "99 * ?e = 198 * (?e div 2) + 99 * ?r"
      by (rule successor_split)
    have multiple: "(198 * (?e div 2)) mod 198 = (0::int) mod 198"
      by (simp add: mod_mult_left_eq)
    have reduced:
      "(198 * (?e div 2) + 99 * ?r) mod 198 =
        (0 + 99 * ?r) mod 198"
      by (rule mod_add_cong[OF multiple refl])
    have defect_residue: "(99 * ?e) mod 198 = (99 * ?r) mod 198"
      by (simp only: split reduced add_0_left)
    have difference_residue:
      "(?prefix - 99 * ?e) mod 198 = (?prefix - 99 * ?r) mod 198"
      by (rule mod_diff_cong[OF refl defect_residue])
    show ?thesis
      by (simp only: source_forcing(2) difference_residue)
  qed
qed

corollary reverse_laurent_two_tick_mod198_endpoint_phase:
  assumes valid: "valid_pair ss"
      and source_mod11: "reverse_add_pair_term ss mod 11 = 0"
      and accumulator_sum_mod198:
        "(a + b) mod 198 = int (reverse_add_pair_term ss) mod 198"
  shows "int (reverse_add_pair_term (step (step ss))) mod 198 =
      (4 * int (reverse_add_pair_term ss) +
        99 * ((int (last (digits (step ss))) -
          int (hd (digits (step ss)))) mod 2)) mod 198"
    and "(fst (reverse_laurent_even_update a b
          (reverse_add_pair_term ss) (reverse_add_pair_term (step ss))
          (reverse_add_pair_reverse (step ss))) +
        snd (reverse_laurent_even_update a b
          (reverse_add_pair_term ss) (reverse_add_pair_term (step ss))
          (reverse_add_pair_reverse (step ss)))) mod 198 =
      (4 * int (reverse_add_pair_term ss) +
        99 * ((int (last (digits (step ss))) -
          int (hd (digits (step ss)))) mod 2)) mod 198"
    and "(fst (reverse_laurent_even_update a b
          (reverse_add_pair_term ss) (reverse_add_pair_term (step ss))
          (reverse_add_pair_reverse (step ss))) -
        snd (reverse_laurent_even_update a b
          (reverse_add_pair_term ss) (reverse_add_pair_term (step ss))
          (reverse_add_pair_reverse (step ss)))) mod 198 =
      ((a - b) + int (reverse_add_pair_term ss) -
        99 * ((int (last (digits (step ss))) -
          int (hd (digits (step ss)))) mod 2)) mod 198"
proof -
  have successor_valid: "valid_pair (step ss)"
    by (rule valid_pair_successor[OF valid])
  have successor_mod11: "reverse_add_pair_term (step ss) mod 11 = 0"
    by (rule reverse_mod99_step_preserves_mod11_zero[OF valid source_mod11])
  have endpoint_phase:
    "reverse_laurent_defect (step ss) mod 2 =
      (int (last (digits (step ss))) -
        int (hd (digits (step ss)))) mod 2"
    by (rule reverse_laurent_defect_parity_from_normalized_ends
        [OF successor_valid successor_mod11])
  note base = reverse_laurent_two_tick_mod198
    [OF valid source_mod11 accumulator_sum_mod198]
  show "int (reverse_add_pair_term (step (step ss))) mod 198 =
      (4 * int (reverse_add_pair_term ss) +
        99 * ((int (last (digits (step ss))) -
          int (hd (digits (step ss)))) mod 2)) mod 198"
    using base(1) endpoint_phase by (simp only: endpoint_phase)
  show "(fst (reverse_laurent_even_update a b
          (reverse_add_pair_term ss) (reverse_add_pair_term (step ss))
          (reverse_add_pair_reverse (step ss))) +
        snd (reverse_laurent_even_update a b
          (reverse_add_pair_term ss) (reverse_add_pair_term (step ss))
          (reverse_add_pair_reverse (step ss)))) mod 198 =
      (4 * int (reverse_add_pair_term ss) +
        99 * ((int (last (digits (step ss))) -
          int (hd (digits (step ss)))) mod 2)) mod 198"
    using base(2) endpoint_phase by (simp only: endpoint_phase)
  show "(fst (reverse_laurent_even_update a b
          (reverse_add_pair_term ss) (reverse_add_pair_term (step ss))
          (reverse_add_pair_reverse (step ss))) -
        snd (reverse_laurent_even_update a b
          (reverse_add_pair_term ss) (reverse_add_pair_term (step ss))
          (reverse_add_pair_reverse (step ss)))) mod 198 =
      ((a - b) + int (reverse_add_pair_term ss) -
        99 * ((int (last (digits (step ss))) -
          int (hd (digits (step ss)))) mod 2)) mod 198"
    using base(3) endpoint_phase by (simp only: endpoint_phase)
qed

ML \<open>
  val checked = @{thms reverse_laurent_half_reconstructs_symmetric_source
    reverse_laurent_q19_publisher_refines_source
    reverse_laurent_q19_carry_normalization_refines_source
    reverse_laurent_defect_exact
    reverse_laurent_defect_mod7_from_mod693_residues
    reverse_laurent_defect_parity_from_normalized_ends
    reverse_mod99_step_preserves_mod11_zero
    reverse_laurent_two_tick_source_forcing reverse_laurent_two_tick_mod7
    reverse_laurent_two_tick_mod198
    reverse_laurent_two_tick_mod198_endpoint_phase};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Reverse Laurent source refinement depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked
    then error "Skipped Reverse Laurent source refinement proof" else ();
\<close>

end
