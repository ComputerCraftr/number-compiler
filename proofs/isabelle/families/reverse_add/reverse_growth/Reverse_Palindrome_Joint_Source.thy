theory Reverse_Palindrome_Joint_Source
  imports Reverse_Joint_Output_Inverse Reverse_Palindrome_Growth_Iff
    Shared_Carry_Dynamics.Decimal_Word_Reversal "HOL.Bit_Operations"
begin

unbundle bit_operations_syntax

text \<open>The source word is the actual decimal digit word.  Its reflected
partner is formed here, so neither the pair field nor the bit-plane inputs
are supplied as an endpoint hypothesis.  The two binary carries remain
distinct from each other and from the decimal carry in the Q19 guard.\<close>

definition reverse_physical_pair_field :: "nat list \<Rightarrow> nat list" where
  "reverse_physical_pair_field source =
    map (\<lambda>(a,b). a + b) (zip source (rev source))"

definition reverse_physical_bit_pairs :: "nat \<Rightarrow> nat list \<Rightarrow> (bool \<times> bool) list" where
  "reverse_physical_bit_pairs precision source =
    map (\<lambda>bit. (odd (decimal_lsd_value source div 2 ^ bit),
      odd (decimal_lsd_value (rev source) div 2 ^ bit))) [0..<precision]"

definition reverse_physical_q19_guard :: "nat list \<Rightarrow> bool" where
  "reverse_physical_q19_guard source =
    (let field = reverse_physical_pair_field source in
      if carry_out False field then
        hd field = 11 \<and> (\<forall>s \<in> set field. s = 0 \<or> s = 11)
      else \<forall>s \<in> set field. s < 10)"

lemma reverse_joint_source_binary_step_arithmetic:
  "((if fst (reverse_joint_output_bits source reflected plus_carry xor_carry) then 1 else 0)::nat) +
      2 * (if fst (reverse_joint_carries source reflected plus_carry xor_carry) then 1 else 0) =
    (if source then 1 else 0) + (if reflected then 1 else 0) +
      (if plus_carry then 1 else 0) \<and>
   ((if snd (reverse_joint_output_bits source reflected plus_carry xor_carry) then 1 else 0)::nat) +
      2 * (if snd (reverse_joint_carries source reflected plus_carry xor_carry) then 1 else 0) =
    (if source then 1 else 0) + (if source \<noteq> reflected then 1 else 0) +
      (if xor_carry then 1 else 0)"
  by (cases source; cases reflected; cases plus_carry; cases xor_carry;
      simp_all add: reverse_joint_output_bits_def reverse_joint_carries_def)

theorem reverse_joint_output_numeric_words:
  "horner_sum of_bool (2::nat) (map fst (fst (reverse_joint_encode_word inputs carries))) +
      2 ^ length inputs * (if fst (snd (reverse_joint_encode_word inputs carries)) then 1 else 0) =
    horner_sum of_bool (2::nat) (map fst inputs) + horner_sum of_bool (2::nat) (map snd inputs) +
      (if fst carries then 1 else 0) \<and>
   horner_sum of_bool (2::nat) (map snd (fst (reverse_joint_encode_word inputs carries))) +
      2 ^ length inputs * (if snd (snd (reverse_joint_encode_word inputs carries)) then 1 else 0) =
    horner_sum of_bool (2::nat) (map fst inputs) +
      horner_sum of_bool (2::nat) (map (\<lambda>(a,b). a \<noteq> b) inputs) +
      (if snd carries then 1 else 0)"
proof (induction inputs arbitrary: carries)
  case Nil
  then show ?case by (cases carries) simp_all
next
  case (Cons input inputs)
  obtain a b where input: "input = (a,b)" by (cases input) auto
  obtain c d where carries: "carries = (c,d)" by (cases carries) auto
  note tail = Cons.IH[of "reverse_joint_carries a b c d"]
  note head = reverse_joint_source_binary_step_arithmetic[of a b c d]
  show ?case unfolding input carries
    using tail[THEN conjunct1] tail[THEN conjunct2]
      head[THEN conjunct1] head[THEN conjunct2]
    by (simp only: reverse_joint_encode_word.simps Let_def fst_conv snd_conv
        list.map case_prod_conv horner_sum_simps of_bool_def length_Cons power_Suc algebra_simps;
        intro conjI; linarith)
qed

corollary reverse_joint_physical_numeric_prefix:
  fixes precision :: nat and source :: "nat list"
  defines "pairs \<equiv> reverse_physical_bit_pairs precision source"
  shows "horner_sum of_bool (2::nat) (map fst (fst (reverse_joint_encode_word pairs (False, False)))) +
      2 ^ precision * (if fst (snd (reverse_joint_encode_word pairs (False, False))) then 1 else 0) =
    horner_sum of_bool (2::nat) (map fst pairs) + horner_sum of_bool (2::nat) (map snd pairs) \<and>
    horner_sum of_bool (2::nat) (map snd (fst (reverse_joint_encode_word pairs (False, False)))) +
      2 ^ precision * (if snd (snd (reverse_joint_encode_word pairs (False, False))) then 1 else 0) =
    horner_sum of_bool (2::nat) (map fst pairs) +
      horner_sum of_bool (2::nat) (map (\<lambda>(a,b). a \<noteq> b) pairs)"
  using reverse_joint_output_numeric_words[of pairs "(False, False)"]
  by (simp add: pairs_def reverse_physical_bit_pairs_def)

theorem reverse_joint_physical_integer_prefix:
  fixes source :: "nat list" and precision :: nat
  defines "pairs \<equiv> reverse_physical_bit_pairs precision source"
    and "x \<equiv> decimal_lsd_value source"
    and "y \<equiv> decimal_lsd_value (rev source)"
  shows "horner_sum of_bool (2::nat) (map fst (fst (reverse_joint_encode_word pairs (False, False)))) +
      2 ^ precision * (if fst (snd (reverse_joint_encode_word pairs (False, False))) then 1 else 0) =
      x mod 2 ^ precision + y mod 2 ^ precision \<and>
    horner_sum of_bool (2::nat) (map snd (fst (reverse_joint_encode_word pairs (False, False)))) +
      2 ^ precision * (if snd (snd (reverse_joint_encode_word pairs (False, False))) then 1 else 0) =
      x mod 2 ^ precision + (x XOR y) mod 2 ^ precision"
proof -
  have first: "horner_sum of_bool (2::nat) (map fst pairs) = x mod 2 ^ precision"
    unfolding pairs_def reverse_physical_bit_pairs_def x_def
    by (simp add: map_map o_def bit_iff_odd[symmetric] horner_sum_bit_eq_take_bit take_bit_eq_mod)
  have second: "horner_sum of_bool (2::nat) (map snd pairs) = y mod 2 ^ precision"
    unfolding pairs_def reverse_physical_bit_pairs_def y_def
    by (simp add: map_map o_def bit_iff_odd[symmetric] horner_sum_bit_eq_take_bit take_bit_eq_mod)
  have difference: "horner_sum of_bool (2::nat) (map (\<lambda>(a,b). a \<noteq> b) pairs) =
      (x XOR y) mod 2 ^ precision"
  proof -
    have bits: "map (\<lambda>(a,b). a \<noteq> b) pairs = map (bit (x XOR y)) [0..<precision]"
      unfolding pairs_def reverse_physical_bit_pairs_def x_def y_def
      apply (simp only: map_map o_def case_prod_conv)
      apply (rule map_cong[OF refl])
      subgoal for i
        using bit_xor_iff[of "decimal_lsd_value source" "decimal_lsd_value (rev source)" i]
        by (simp only: bit_iff_odd)
      done
    show ?thesis by (simp only: bits horner_sum_bit_eq_take_bit take_bit_eq_mod)
  qed
  show ?thesis using reverse_joint_physical_numeric_prefix[of precision source]
    by (simp only: pairs_def[symmetric] first second difference)
qed

lemma reverse_physical_pair_field_valid:
  assumes nonempty: "source \<noteq> []" and decimal: "\<forall>d \<in> set source. d < 10"
  shows "valid_pair (reverse_physical_pair_field source)"
proof -
  let ?f = "\<lambda>(a,b). a+b"
  have nonempty_field: "reverse_physical_pair_field source \<noteq> []"
    using nonempty by (simp add: reverse_physical_pair_field_def zip_eq_Nil_iff)
  have symmetric: "rev (reverse_physical_pair_field source) = reverse_physical_pair_field source"
  proof -
    have "rev (reverse_physical_pair_field source) = map ?f (zip (rev source) source)"
      by (simp add: reverse_physical_pair_field_def rev_map zip_rev[symmetric])
    also have "... = map ?f (zip source (rev source))"
      by (subst zip_commute) (simp add: comp_def case_prod_unfold add.commute)
    finally show ?thesis by (simp add: reverse_physical_pair_field_def)
  qed
  have bound: "\<forall>s \<in> set (reverse_physical_pair_field source). s \<le> 18"
  proof
    fix s assume "s \<in> set (reverse_physical_pair_field source)"
    then obtain a b where pair: "(a,b) \<in> set (zip source (rev source))" and s: "s = a+b"
      by (auto simp: reverse_physical_pair_field_def)
    have "a < 10" using pair decimal by (meson set_zip_leftD)
    moreover have "b < 10" using pair decimal by (auto dest: set_zip_rightD)
    ultimately show "s \<le> 18" using s by arith
  qed
  show ?thesis using nonempty_field symmetric bound by (simp add: valid_pair_def)
qed

theorem reverse_physical_joint_q19_preimage:
  assumes "source \<noteq> []" "\<forall>d \<in> set source. d < 10"
  shows "reverse_joint_decode_word
      (fst (reverse_joint_encode_word (reverse_physical_bit_pairs precision source) binary_carries))
      binary_carries =
        (reverse_physical_bit_pairs precision source,
         snd (reverse_joint_encode_word (reverse_physical_bit_pairs precision source) binary_carries))
    \<and> ((rev (digits (reverse_physical_pair_field source)) =
      digits (reverse_physical_pair_field source)) = reverse_physical_q19_guard source)"
proof -
  have valid: "valid_pair (reverse_physical_pair_field source)"
    by (rule reverse_physical_pair_field_valid[OF assms])
  have exact: "(rev (digits (reverse_physical_pair_field source)) =
      digits (reverse_physical_pair_field source)) = reverse_physical_q19_guard source"
    unfolding reverse_physical_q19_guard_def Let_def
    using reverse_no_growth_palindrome_preimage_exact[OF valid]
      reverse_growth_palindrome_preimage_exact[OF valid]
    by (cases "carry_out False (reverse_physical_pair_field source)") auto
  show ?thesis using reverse_joint_word_same_source[of "reverse_physical_bit_pairs precision source" binary_carries]
    exact by simp
qed

theorem reverse_physical_integer_joint_q19:
  fixes source :: "nat list" and precision :: nat
  assumes "source \<noteq> []" "\<forall>d \<in> set source. d < 10"
  shows "(reverse_joint_decode_word
      (fst (reverse_joint_encode_word (reverse_physical_bit_pairs precision source) (False, False)))
      (False, False) =
        (reverse_physical_bit_pairs precision source,
         snd (reverse_joint_encode_word (reverse_physical_bit_pairs precision source) (False, False))))
    \<and> ((rev (digits (reverse_physical_pair_field source)) =
      digits (reverse_physical_pair_field source)) = reverse_physical_q19_guard source)
    \<and> (horner_sum of_bool (2::nat)
      (map fst (fst (reverse_joint_encode_word (reverse_physical_bit_pairs precision source) (False, False)))) +
      2 ^ precision * (if fst (snd (reverse_joint_encode_word
        (reverse_physical_bit_pairs precision source) (False, False))) then 1 else 0) =
      decimal_lsd_value source mod 2 ^ precision + decimal_lsd_value (rev source) mod 2 ^ precision)
    \<and> (horner_sum of_bool (2::nat)
      (map snd (fst (reverse_joint_encode_word (reverse_physical_bit_pairs precision source) (False, False)))) +
      2 ^ precision * (if snd (snd (reverse_joint_encode_word
        (reverse_physical_bit_pairs precision source) (False, False))) then 1 else 0) =
      decimal_lsd_value source mod 2 ^ precision +
        (decimal_lsd_value source XOR decimal_lsd_value (rev source)) mod 2 ^ precision)"
  using reverse_physical_joint_q19_preimage[OF assms, of precision "(False, False)"]
    reverse_joint_physical_integer_prefix[of precision source]
  by simp

ML \<open>
  val checked = @{thms reverse_joint_source_binary_step_arithmetic reverse_joint_output_numeric_words
    reverse_joint_physical_numeric_prefix reverse_joint_physical_integer_prefix
    reverse_physical_pair_field_valid reverse_physical_joint_q19_preimage
    reverse_physical_integer_joint_q19};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Reverse physical joint source theorem depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked
    then error "Skipped reverse physical joint source theorem" else ();
\<close>

end
