theory Reverse_Punctured_T2_Coefficients
  imports Reverse_196_Publisher_Refinement Reverse_Punctured_Run_Normalization
begin

text \<open>The punctured T2 constructor's first coefficient tape is the exact
pair field @{term "step ss"}.  These equations refine its two pointwise
coefficient branches, before event partitioning, digit normalization, and
opposite-end run pairing.  They do not claim that those later run transforms
are refined or that T2 composes to an all-depth temporal action.\<close>

text \<open>The Q19 producer stores only the first half of a symmetric pair
field and an odd-width tag.  Its run decoder mirrors that half, removing one
copy of the center symbol for odd width.  The following carrier lemmas connect
that input representation to @{const valid_pair}, the precondition used by
the exact coefficient lemmas below.\<close>

definition punctured_q19_decode_half :: "nat list \<Rightarrow> bool \<Rightarrow> nat list" where
  "punctured_q19_decode_half half is_odd =
    (if is_odd then half @ rev (butlast half) else half @ rev half)"

lemma punctured_q19_decode_half_symmetric:
  "rev (punctured_q19_decode_half half is_odd) =
    punctured_q19_decode_half half is_odd"
proof (cases is_odd)
  case False
  then show ?thesis
    by (simp add: punctured_q19_decode_half_def rev_append)
next
  case True
  show ?thesis
  proof (cases half)
    case Nil
    then show ?thesis using True
      by (simp add: punctured_q19_decode_half_def)
  next
    case (Cons head tail)
    have split: "half = butlast half @ [last half]"
      using Cons by simp
    have reverse_half:
      "rev half = [last half] @ rev (butlast half)"
      using split by (simp add: rev_append)
    have reverse_decoded:
      "rev (half @ rev (butlast half)) = butlast half @ rev half"
      by (simp add: rev_append)
    have same_form:
      "half @ rev (butlast half) = butlast half @ rev half"
    proof (rule trans)
      show "half @ rev (butlast half) =
          (butlast half @ [last half]) @ rev (butlast half)"
        using split
        by (rule arg_cong[where f="\<lambda>word. word @ rev (butlast half)"])
      show "(butlast half @ [last half]) @ rev (butlast half) =
          butlast half @ rev half"
      proof (rule trans)
        show "(butlast half @ [last half]) @ rev (butlast half) =
            butlast half @ ([last half] @ rev (butlast half))"
          by (simp only: append_assoc)
        show "butlast half @ ([last half] @ rev (butlast half)) =
            butlast half @ rev half"
          using reverse_half[symmetric]
          by (rule arg_cong[where f="\<lambda>word. butlast half @ word"])
      qed
    qed
    show ?thesis using True reverse_decoded same_form
      by (simp add: punctured_q19_decode_half_def)
  qed
qed

lemma punctured_q19_decode_half_length:
  "length (punctured_q19_decode_half half is_odd) =
    2 * length half - (if is_odd then 1 else 0)"
proof (cases is_odd)
  case False
  then show ?thesis
    by (simp add: punctured_q19_decode_half_def)
next
  case True
  then show ?thesis
    by (simp add: punctured_q19_decode_half_def)
qed

lemma punctured_q19_decode_half_valid:
  assumes nonempty: "half \<noteq> []"
      and bounded: "\<forall>symbol\<in>set half. symbol \<le> 18"
  shows "valid_pair (punctured_q19_decode_half half is_odd)"
proof -
  have mirrored: "rev (punctured_q19_decode_half half is_odd) =
      punctured_q19_decode_half half is_odd"
    by (rule punctured_q19_decode_half_symmetric)
  have butlast_subset: "set (butlast half) \<subseteq> set half"
    by (induction half) auto
  have bounded_reverse: "\<forall>symbol\<in>set (rev half). symbol \<le> 18"
    using bounded by auto
  have bounded_butlast_reverse:
    "\<forall>symbol\<in>set (rev (butlast half)). symbol \<le> 18"
    using bounded butlast_subset by auto
  have decoded_nonempty: "punctured_q19_decode_half half is_odd \<noteq> []"
    using nonempty by (cases half) (simp_all add: punctured_q19_decode_half_def)
  show ?thesis
    using mirrored decoded_nonempty bounded bounded_reverse
      bounded_butlast_reverse
    by (auto simp: valid_pair_def punctured_q19_decode_half_def)
qed

definition punctured_prefix_carry :: "nat list \<Rightarrow> nat \<Rightarrow> bool" where
  "punctured_prefix_carry ss i = carry_out False (take i ss)"

definition punctured_no_growth_coefficient :: "nat list \<Rightarrow> nat \<Rightarrow> nat" where
  "punctured_no_growth_coefficient ss i =
    2 * (ss ! i) + carry_bit (punctured_prefix_carry ss i) +
      carry_bit (punctured_prefix_carry ss (length ss - Suc i)) -
    10 * (carry_bit (punctured_prefix_carry ss (Suc i)) +
      carry_bit (punctured_prefix_carry ss (length ss - i)) )"

definition punctured_growth_interior_coefficient :: "nat list \<Rightarrow> nat \<Rightarrow> nat" where
  "punctured_growth_interior_coefficient ss i =
    (ss ! (i - 1)) + (ss ! i) +
      carry_bit (punctured_prefix_carry ss i) +
      carry_bit (punctured_prefix_carry ss (length ss - i)) -
    10 * (carry_bit (punctured_prefix_carry ss (Suc i)) +
      carry_bit (punctured_prefix_carry ss (Suc (length ss - i))))"

definition punctured_growth_edge_coefficient :: "nat list \<Rightarrow> nat" where
  "punctured_growth_edge_coefficient ss =
    (ss ! 0) + 1 - 10 * carry_bit (punctured_prefix_carry ss 1)"

lemma carry_out_take_successor:
  assumes bound: "i < length ss"
  shows "carry_out False (take (Suc i) ss) =
    carry_apply (domain (ss ! i)) (carry_out False (take i ss))"
proof -
  have take: "take (Suc i) ss = take i ss @ [ss ! i]"
    using take_Suc_conv_app_nth[OF bound] by simp
  show ?thesis using take
    by (simp add: carry_out_append carry_out_def)
qed

lemma punctured_carry_subtrahend_bound:
  "10 * carry_bit (carry_apply (domain symbol) incoming) \<le>
    symbol + carry_bit incoming"
proof -
  have transfer:
    "carry_apply (domain symbol) incoming =
      (10 \<le> symbol + carry_bit incoming)"
    by (simp add: carry_from_domain carry_bit_def)
  show ?thesis
  proof (cases "carry_apply (domain symbol) incoming")
    case True
    then have threshold: "10 \<le> symbol + carry_bit incoming"
      using transfer by simp
    show ?thesis using True threshold by (simp add: carry_bit_def)
  next
    case False
    then show ?thesis by (simp add: carry_bit_def)
  qed
qed

lemma nat_sum_subtracts_exact:
  fixes left right left_sub right_sub :: nat
  assumes left_bound: "left_sub \<le> left"
      and right_bound: "right_sub \<le> right"
  shows "left + right - (left_sub + right_sub) =
    (left - left_sub) + (right - right_sub)"
proof -
  have left_split: "left = (left - left_sub) + left_sub"
    using left_bound by arith
  have right_split: "right = (right - right_sub) + right_sub"
    using right_bound by arith
  have joined:
    "left + right =
      ((left - left_sub) + (right - right_sub)) + (left_sub + right_sub)"
    using left_split right_split by (simp add: algebra_simps)
  have subtract:
    "left + right - (left_sub + right_sub) =
      (((left - left_sub) + (right - right_sub)) +
        (left_sub + right_sub)) - (left_sub + right_sub)"
    using joined by (simp only: joined)
  show ?thesis using subtract
    by (simp only: add_diff_cancel_right')
qed

lemma punctured_two_digit_normalization_sum:
  fixes left right :: nat
    and left_carry right_carry :: bool
  shows "left + right + carry_bit left_carry + carry_bit right_carry -
      10 * (carry_bit (carry_apply (domain left) left_carry) +
        carry_bit (carry_apply (domain right) right_carry)) =
    (left + carry_bit left_carry -
      10 * carry_bit (carry_apply (domain left) left_carry)) +
    (right + carry_bit right_carry -
      10 * carry_bit (carry_apply (domain right) right_carry))"
proof -
  have left_bound: "10 * carry_bit (carry_apply (domain left) left_carry) \<le>
      left + carry_bit left_carry"
    by (rule punctured_carry_subtrahend_bound)
  have right_bound: "10 * carry_bit (carry_apply (domain right) right_carry) \<le>
      right + carry_bit right_carry"
    by (rule punctured_carry_subtrahend_bound)
  show ?thesis
    using nat_sum_subtracts_exact[OF left_bound right_bound]
    by (simp add: algebra_simps)
qed

lemma punctured_digits_cell_exact:
  assumes bound: "i < length ss"
      and symbol: "ss ! i < 19"
  shows "digits ss ! i =
    ss ! i + carry_bit (punctured_prefix_carry ss i) -
      10 * carry_bit (punctured_prefix_carry ss (Suc i))"
proof -
  let ?incoming = "punctured_prefix_carry ss i"
  have digit_mod:
    "digits ss ! i = (ss ! i + carry_bit ?incoming) mod 10"
  proof (cases "carry_out False ss")
    case True
    then show ?thesis
      using digits_nth_growth[OF bound True]
      by (simp add: punctured_prefix_carry_def)
  next
    case False
    then show ?thesis
      using digits_nth_no_growth[OF bound] by (simp add: punctured_prefix_carry_def)
  qed
  have successor_carry:
    "punctured_prefix_carry ss (Suc i) =
      carry_apply (domain (ss ! i)) ?incoming"
    using carry_out_take_successor[OF bound]
    by (simp add: punctured_prefix_carry_def)
  have normalized:
    "ss ! i + carry_bit ?incoming -
        10 * carry_bit (carry_apply (domain (ss ! i)) ?incoming) =
      (ss ! i + carry_bit ?incoming) mod 10"
    using punctured_digit_normal_form[OF symbol, of ?incoming]
    by (simp add: carry_bit_def punctured_carry_value_def)
  show ?thesis using digit_mod normalized successor_carry by simp
qed

lemma punctured_pair_coefficient_refines_digits:
  assumes left_bound: "left_index < length ss"
      and right_bound: "right_index < length ss"
      and left_symbol: "ss ! left_index < 19"
      and right_symbol: "ss ! right_index < 19"
  shows "ss ! left_index + ss ! right_index +
      carry_bit (punctured_prefix_carry ss left_index) +
      carry_bit (punctured_prefix_carry ss right_index) -
    10 * (carry_bit (punctured_prefix_carry ss (Suc left_index)) +
      carry_bit (punctured_prefix_carry ss (Suc right_index))) =
    digits ss ! left_index + digits ss ! right_index"
proof -
  have left_digit:
    "digits ss ! left_index =
      ss ! left_index + carry_bit (punctured_prefix_carry ss left_index) -
        10 * carry_bit (punctured_prefix_carry ss (Suc left_index))"
    by (rule punctured_digits_cell_exact[OF left_bound left_symbol])
  have right_digit:
    "digits ss ! right_index =
      ss ! right_index + carry_bit (punctured_prefix_carry ss right_index) -
        10 * carry_bit (punctured_prefix_carry ss (Suc right_index))"
    by (rule punctured_digits_cell_exact[OF right_bound right_symbol])
  have normalized_sum:
    "ss ! left_index + ss ! right_index +
        carry_bit (punctured_prefix_carry ss left_index) +
        carry_bit (punctured_prefix_carry ss right_index) -
      10 * (carry_bit (punctured_prefix_carry ss (Suc left_index)) +
        carry_bit (punctured_prefix_carry ss (Suc right_index))) =
      (ss ! left_index + carry_bit (punctured_prefix_carry ss left_index) -
        10 * carry_bit (punctured_prefix_carry ss (Suc left_index))) +
      (ss ! right_index + carry_bit (punctured_prefix_carry ss right_index) -
        10 * carry_bit (punctured_prefix_carry ss (Suc right_index)))"
    using punctured_two_digit_normalization_sum
      [where left_carry="punctured_prefix_carry ss left_index"
        and right_carry="punctured_prefix_carry ss right_index"]
      carry_out_take_successor[OF left_bound]
      carry_out_take_successor[OF right_bound]
    by (simp add: punctured_prefix_carry_def)
  show ?thesis using normalized_sum left_digit right_digit by simp
qed

theorem punctured_no_growth_coefficient_refines_step:
  assumes valid: "valid_pair ss"
      and no_growth: "\<not> carry_out False ss"
      and bound: "i < length ss"
  shows "punctured_no_growth_coefficient ss i = step ss ! i"
proof -
  have bounded: "\<forall>s\<in>set ss. s < 19"
    using valid by (auto simp: valid_pair_def)
  have palindrome: "rev ss = ss"
    using valid by (simp add: valid_pair_def)
  let ?j = "length ss - Suc i"
  have jbound: "?j < length ss" using bound by arith
  have j_successor: "Suc ?j = length ss - i" using bound by arith
  have source_reflect: "ss ! ?j = ss ! i"
    using palindrome_nth_reflect[OF palindrome bound] by simp
  have symbol_i: "ss ! i < 19" using bounded bound by auto
  have symbol_j: "ss ! ?j < 19" using bounded jbound by auto
  have pair_digits:
    "ss ! i + ss ! ?j +
        carry_bit (punctured_prefix_carry ss i) +
        carry_bit (punctured_prefix_carry ss ?j) -
      10 * (carry_bit (punctured_prefix_carry ss (Suc i)) +
        carry_bit (punctured_prefix_carry ss (Suc ?j))) =
      digits ss ! i + digits ss ! ?j"
    using punctured_pair_coefficient_refines_digits[OF bound jbound symbol_i symbol_j] .
  have twice: "2 * (ss ! i) = ss ! i + ss ! i"
    by (simp add: mult_2)
  have expanded:
    "punctured_no_growth_coefficient ss i =
      ss ! i + ss ! ?j +
        carry_bit (punctured_prefix_carry ss i) +
        carry_bit (punctured_prefix_carry ss ?j) -
      10 * (carry_bit (punctured_prefix_carry ss (Suc i)) +
        carry_bit (punctured_prefix_carry ss (Suc ?j)))"
    using source_reflect j_successor twice
    by (simp only: punctured_no_growth_coefficient_def
        punctured_prefix_carry_def twice source_reflect j_successor)
  have coefficient:
    "punctured_no_growth_coefficient ss i = digits ss ! i + digits ss ! ?j"
    using expanded pair_digits by simp
  have step_cell: "step ss ! i = digits ss ! i + digits ss ! ?j"
    using bound no_growth
    by (simp add: step_def digits_def rev_nth)
  show ?thesis using coefficient step_cell by simp
qed

theorem punctured_growth_interior_coefficient_refines_step:
  assumes valid: "valid_pair ss"
      and growth: "carry_out False ss"
      and positive: "0 < i"
      and bound: "i < length ss"
  shows "punctured_growth_interior_coefficient ss i = step ss ! i"
proof -
  have bounded: "\<forall>s\<in>set ss. s < 19"
    using valid by (auto simp: valid_pair_def)
  have palindrome: "rev ss = ss"
    using valid by (simp add: valid_pair_def)
  let ?j = "length ss - i"
  have jbound: "?j < length ss" using positive bound by arith
  have previous_bound: "i - 1 < length ss" using bound by arith
  have source_reflect: "ss ! ?j = ss ! (i - 1)"
    using palindrome_nth_reflect[OF palindrome previous_bound] positive
    by simp
  have symbol_i: "ss ! i < 19" using bounded bound by auto
  have symbol_j: "ss ! ?j < 19" using bounded jbound by auto
  have pair_digits:
    "ss ! i + ss ! ?j +
        carry_bit (punctured_prefix_carry ss i) +
        carry_bit (punctured_prefix_carry ss ?j) -
      10 * (carry_bit (punctured_prefix_carry ss (Suc i)) +
        carry_bit (punctured_prefix_carry ss (Suc ?j))) =
      digits ss ! i + digits ss ! ?j"
    using punctured_pair_coefficient_refines_digits[OF bound jbound symbol_i symbol_j] .
  have coefficient:
    "punctured_growth_interior_coefficient ss i = digits ss ! i + digits ss ! ?j"
    using pair_digits source_reflect
    by (simp add: punctured_growth_interior_coefficient_def
        punctured_prefix_carry_def algebra_simps)
  have step_cell: "step ss ! i = digits ss ! i + digits ss ! ?j"
    using bound positive growth jbound
    by (simp add: step_def length_digits_exact rev_nth nth_append)
  show ?thesis using coefficient step_cell by simp
qed

lemma punctured_growth_edge_coefficient_refines_first:
  assumes valid: "valid_pair ss"
      and growth: "carry_out False ss"
  shows "punctured_growth_edge_coefficient ss = step ss ! 0"
proof -
  have nonempty: "ss \<noteq> []" using valid by (simp add: valid_pair_def)
  have bound: "0 < length ss" using nonempty by simp
  have bounded: "\<forall>s\<in>set ss. s < 19"
    using valid by (auto simp: valid_pair_def)
  have symbol: "ss ! 0 < 19" using bounded bound by auto
  have digit: "digits ss ! 0 =
      ss ! 0 + carry_bit (punctured_prefix_carry ss 0) -
        10 * carry_bit (punctured_prefix_carry ss 1)"
    using punctured_digits_cell_exact[OF bound symbol] by simp
  have terminal: "digits ss ! length ss = 1"
    by (rule digits_growth_last[OF growth])
  have step_cell: "step ss ! 0 = digits ss ! 0 + digits ss ! length ss"
    using growth nonempty by (simp add: step_def length_digits_exact rev_nth)
  have carry0: "punctured_prefix_carry ss 0 = False"
    by (simp add: punctured_prefix_carry_def carry_out_def)
  have carry_bound:
    "10 * carry_bit (punctured_prefix_carry ss 1) \<le> ss ! 0"
    using punctured_carry_subtrahend_bound[of "ss ! 0" False]
      carry_out_take_successor[OF bound] symbol
    by (simp add: punctured_prefix_carry_def carry0 carry_bit_def carry_out_def)
  have digit0:
    "digits ss ! 0 = ss ! 0 -
      10 * carry_bit (punctured_prefix_carry ss 1)"
    using digit carry0 by (simp add: carry_bit_def)
  have normalized_edge:
    "ss ! 0 + 1 - 10 * carry_bit (punctured_prefix_carry ss 1) =
      digits ss ! 0 + 1"
    using digit0 carry_bound by arith
  have edge:
    "punctured_growth_edge_coefficient ss = digits ss ! 0 + 1"
    using normalized_edge
    by (simp add: punctured_growth_edge_coefficient_def)
  show ?thesis using step_cell terminal edge by simp
qed

lemma punctured_growth_edge_coefficient_refines_last:
  assumes valid: "valid_pair ss"
      and growth: "carry_out False ss"
  shows "punctured_growth_edge_coefficient ss = step ss ! length ss"
proof -
  have first: "punctured_growth_edge_coefficient ss = step ss ! 0"
    by (rule punctured_growth_edge_coefficient_refines_first[OF valid growth])
  have positive: "0 < length (step ss)"
    using valid by (simp add: valid_pair_def step_def digits_def)
  have last_index: "length (step ss) - Suc 0 = length ss"
    using growth by (simp add: length_step_exact length_digits_exact)
  have symmetry: "step ss ! length ss = step ss ! 0"
  proof -
    have zero_bound: "0 < length (step ss)" using positive .
    have reverse_zero:
      "rev (step ss) ! 0 = step ss ! (length (step ss) - Suc 0)"
      using rev_nth[OF zero_bound] .
    show ?thesis using step_symmetric[of ss] reverse_zero last_index
      by simp
  qed
  show ?thesis using first symmetry by simp
qed

ML \<open>
  val checked = @{thms carry_out_take_successor
    punctured_q19_decode_half_symmetric punctured_q19_decode_half_length
    punctured_q19_decode_half_valid
    punctured_carry_subtrahend_bound punctured_two_digit_normalization_sum
    punctured_digits_cell_exact punctured_no_growth_coefficient_refines_step
    punctured_growth_interior_coefficient_refines_step
    punctured_growth_edge_coefficient_refines_first
    punctured_growth_edge_coefficient_refines_last};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Punctured T2 coefficient refinement depends on an oracle";
\<close>

end
