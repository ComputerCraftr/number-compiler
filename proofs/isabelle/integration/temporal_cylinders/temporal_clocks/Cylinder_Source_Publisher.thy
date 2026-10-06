theory Cylinder_Source_Publisher
  imports Cylinder_Source_Coboundary
begin

text \<open>
  This is the finite source-to-publisher bridge.  The source is the actual
  pair field, its carry is the prefix fold, and the extra coefficient at the
  right is the terminal carry.  Nothing here claims a powered temporal
  normal form.
\<close>

lemma source_coefficient_supported:
  "cylinder_source_supported (length ss) (source_coefficient ss)"
  unfolding cylinder_source_supported_def source_coefficient_def
    cylinder_window_def
  by auto

lemma source_digits_nth_coefficient:
  assumes bound: "j < length ss"
  shows "source_coefficient (digits ss) (int j) =
    int (emit False ss ! j)"
proof -
  have emitted_bound: "j < length (emit False ss)"
    using bound by simp
  show ?thesis
    unfolding source_coefficient_def digits_def
    using bound emitted_bound by (simp add: nth_append)
qed

lemma source_digits_terminal_coefficient:
  "source_coefficient (digits ss) (int (length ss)) =
    int (carry_bit (carry_out False ss))"
proof (cases "carry_out False ss")
  case False
  then show ?thesis
    by (simp add: source_coefficient_def digits_def
        length_digits_exact carry_bit_def nth_append)
next
  case True
  then show ?thesis
    by (simp add: source_coefficient_def digits_def
        length_digits_exact carry_bit_def nth_append)
qed

lemma source_coefficient_zero_at_or_above:
  assumes bound: "int (length xs) \<le> i"
  shows "source_coefficient xs i = 0"
  unfolding source_coefficient_def using bound by simp

lemma source_coefficient_symmetric_of_valid_pair:
  assumes valid: "valid_pair ss"
  shows "cylinder_source_symmetric (length ss) (source_coefficient ss)"
proof (unfold cylinder_source_symmetric_def, intro allI impI)
  fix i
  assume active: "cylinder_window (length ss) i"
  have lower: "0 \<le> i"
    using active unfolding cylinder_window_def by simp
  have upper: "i < int (length ss)"
    using active unfolding cylinder_window_def by simp
  have jbound: "nat i < length ss"
    using lower upper by simp
  have reflected:
      "ss ! (length ss - Suc (nat i)) = ss ! nat i"
    using palindrome_nth_reflect[OF
      source_pair_symmetric_of_valid_pair[OF valid] jbound] .
  have index:
      "nat (int (length ss) - 1 - i) = length ss - Suc (nat i)"
    using lower upper by simp
  have index_bound:
      "nat (int (length ss) - 1 - i) < length ss"
    using lower upper by simp
  have reflected_lower:
      "0 \<le> int (length ss) - 1 - i"
    using upper by arith
  have reflected_upper:
      "int (length ss) - 1 - i < int (length ss)"
    using lower by arith
  show "source_coefficient ss i =
      source_coefficient ss (int (length ss) - 1 - i)"
    unfolding source_coefficient_def
    using reflected reflected_lower reflected_upper index index_bound
      lower upper jbound
    by simp
qed

lemma source_normalized_digits:
  assumes valid: "source_pair_valid ss"
      and positive: "0 < length ss"
  shows "\<forall>i. cylinder_normalized 10 (source_coefficient ss)
      (source_carry_out ss) i =
      source_coefficient (digits ss) i"
proof (intro allI)
  fix i
  have encoding:
      "cylinder_carry_encoding (length ss)
        (source_carry_state ss) (source_carry_out ss)"
    using source_carry_encoding .
  have supported:
      "cylinder_source_supported (length ss) (source_coefficient ss)"
    using source_coefficient_supported .
  show "cylinder_normalized 10 (source_coefficient ss)
      (source_carry_out ss) i = source_coefficient (digits ss) i"
  proof (cases "i < 0")
    case True
    have normalized:
        "cylinder_normalized 10 (source_coefficient ss)
          (source_carry_out ss) i = 0"
      using cylinder_normalized_exterior_zero[OF encoding supported]
        True by blast
    have emitted: "source_coefficient (digits ss) i = 0"
      unfolding source_coefficient_def using True by simp
    show ?thesis using normalized emitted by simp
  next
    case False
    show ?thesis
    proof (cases "i < int (length ss)")
      case True
      have active: "cylinder_window (length ss) i"
        unfolding cylinder_window_def using False True by simp
      have j: "nat i < length ss"
        using False True by simp
      have index: "int (nat i) = i"
        using False by simp
      have normalized:
          "cylinder_normalized 10 (source_coefficient ss)
            (source_carry_out ss) i = int (emit False ss ! nat i)"
        using source_coboundary_emit[OF valid j]
        by (simp only: index)
      have emitted:
          "source_coefficient (digits ss) i = int (emit False ss ! nat i)"
        using source_digits_nth_coefficient[OF j]
        by (simp only: index)
      show ?thesis using normalized emitted by simp
    next
      case False
      have at_or_above: "int (length ss) \<le> i"
        using False by arith
      show ?thesis
      proof (cases "i = int (length ss)")
        case True
        have terminal:
            "source_carry_state ss (int (length ss)) =
              int (carry_bit (carry_out False ss))"
          unfolding source_carry_state_def
          by simp
        have carry_cases:
            "int (carry_bit (carry_out False ss)) = 0 \<or>
             int (carry_bit (carry_out False ss)) = 1"
          by (simp add: carry_bit_def)
        have normalized:
            "cylinder_normalized 10 (source_coefficient ss)
              (source_carry_out ss) i =
              int (carry_bit (carry_out False ss))"
          using cylinder_normalized_leading_carry
            [OF positive encoding supported terminal carry_cases, where b=10]
          using True by simp
        have emitted:
            "source_coefficient (digits ss) i =
              int (carry_bit (carry_out False ss))"
          using source_digits_terminal_coefficient[of ss]
          using True by simp
        show ?thesis using normalized emitted by simp
      next
        case False
        have greater: "int (length ss) < i"
          using at_or_above False by arith
        have normalized:
            "cylinder_normalized 10 (source_coefficient ss)
              (source_carry_out ss) i = 0"
          using cylinder_normalized_exterior_zero[OF encoding supported]
            greater by blast
        have digits_length:
            "int (length (digits ss)) \<le> int (length ss) + 1"
          by (simp add: length_digits_exact)
        have output_bound: "int (length (digits ss)) \<le> i"
          using greater digits_length by arith
        have emitted:
            "source_coefficient (digits ss) i = 0"
          using source_coefficient_zero_at_or_above[OF output_bound] .
        show ?thesis using normalized emitted by simp
      qed
    qed
  qed
qed

text \<open>
  The preceding theorem is the complete finite source normalization,
  including both the terminal carry coefficient and exterior zero support.
  The next statement exposes the remaining finite publisher equality with
  the explicit list-step semantics.  Its proof is intentionally stated on
  the actual source and not on a supplied digit or carry word.
\<close>

lemma source_reflected_pair_sum:
  "source_coefficient (map (\<lambda>(a,b). a+b) (zip ds (rev ds))) i =
    source_coefficient ds i +
    source_coefficient ds (int (length ds) - 1 - i)"
proof (cases "0 \<le> i \<and> i < int (length ds)")
  case True
  then have lower: "0 \<le> i" and upper: "i < int (length ds)" by auto
  have bound: "nat i < length ds" using lower upper by simp
  have mirror_lower: "0 \<le> int (length ds) - 1 - i" using upper by arith
  have mirror_upper: "int (length ds) - 1 - i < int (length ds)"
    using lower by arith
  have mirror_index:
    "nat (int (length ds) - 1 - i) = length ds - Suc (nat i)"
    using lower upper by simp
  have mapped:
    "map (\<lambda>(a,b). a+b) (zip ds (rev ds)) ! nat i =
      ds ! nat i + ds ! (length ds - Suc (nat i))"
    using bound by (simp add: rev_nth)
  show ?thesis
    using True mirror_lower mirror_upper mirror_index mapped
    by (simp add: source_coefficient_def)
next
  case False
  have mirrored:
    "\<not> (0 \<le> int (length ds) - 1 - i \<and>
      int (length ds) - 1 - i < int (length ds))"
    using False by arith
  show ?thesis using False mirrored by (auto simp: source_coefficient_def)
qed

theorem source_cylinder_next_step:
  assumes valid: "valid_pair ss"
  shows "cylinder_next
      (int (length ss) + int (carry_bit (carry_out False ss)) - 1)
      (source_coefficient ss) (source_carry_out ss) =
      source_coefficient (step ss)"
proof (rule ext)
  fix i
  have pair_valid: "source_pair_valid ss"
    using source_pair_valid_of_valid_pair[OF valid] .
  have positive: "0 < length ss"
    using valid by (simp add: valid_pair_def)
  have normalized:
      "cylinder_normalized 10 (source_coefficient ss)
        (source_carry_out ss) = source_coefficient (digits ss)"
    using source_normalized_digits[OF pair_valid positive]
    by (simp add: fun_eq_iff)
  have output_length:
      "length (step ss) = length (digits ss)"
    by simp
  have source_extent:
      "int (length ss) + int (carry_bit (carry_out False ss)) - 1 =
        int (length (digits ss)) - 1"
    by (cases "carry_out False ss") (simp_all add: length_digits_exact carry_bit_def)
  show "cylinder_next
      (int (length ss) + int (carry_bit (carry_out False ss)) - 1)
      (source_coefficient ss) (source_carry_out ss) i =
      source_coefficient (step ss) i"
    unfolding cylinder_next_def innovation_add_def innovation_reflect_def
    using normalized source_extent source_reflected_pair_sum[of "digits ss" i]
    by (simp only: step_def)
qed

ML \<open>
  val checked = @{thms source_coefficient_supported source_digits_nth_coefficient
    source_digits_terminal_coefficient source_coefficient_symmetric_of_valid_pair
    source_normalized_digits source_cylinder_next_step};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Source publisher bridge depends on an oracle";
\<close>

end
