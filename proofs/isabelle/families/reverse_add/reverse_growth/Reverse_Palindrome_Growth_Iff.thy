theory Reverse_Palindrome_Growth_Iff
  imports Reverse_Palindrome_Physical_Iff
begin

theorem reverse_growth_palindrome_preimage_exact:
  assumes valid: "valid_pair coefficients"
    and growth: "carry_out False coefficients"
  shows "rev (digits coefficients) = digits coefficients \<longleftrightarrow>
    hd coefficients = 11 \<and> (\<forall>s \<in> set coefficients. s = 0 \<or> s = 11)"
proof
  assume palindrome: "rev (digits coefficients) = digits coefficients"
  let ?n = "length coefficients"
  let ?C = "reverse_palindrome_prefix_carry coefficients"
  let ?S = "(\<lambda>i. coefficients ! i)"
  have nonempty: "coefficients \<noteq> []" and symmetric: "rev coefficients = coefficients"
    and coefficient_bound: "\<forall>s \<in> set coefficients. s < 19"
    using valid by (auto simp: valid_pair_def)
  have width: "0 < ?n" using nonempty by simp
  have start: "?C 0 = 0"
    by (simp add: reverse_palindrome_prefix_carry_def carry_bit_def carry_out_def)
  have finish: "?C ?n = 1"
    using growth by (simp add: reverse_palindrome_prefix_carry_def carry_bit_def)
  have bits: "?C i < 2" for i by simp
  have source_symmetry: "?S i = ?S (?n - Suc i)" if "i < ?n" for i
    using palindrome_nth_reflect[OF symmetric that] by simp
  have carry_step: "?C (Suc i) = decimal_carry (?S i) (?C i)" if "i < ?n" for i
    by (rule reverse_palindrome_prefix_carry_step[OF that])
  have length: "length (digits coefficients) = Suc ?n"
    using growth by (simp add: length_digits_exact)
  have digit_nth: "digits coefficients ! i = emit False coefficients ! i" if "i < ?n" for i
    using that growth by (simp add: digits_def nth_append length_emit)
  have interior:
    "normalized_growth_digit ?S ?C i = normalized_growth_digit ?S ?C (?n - i)"
    if positive: "0 < i" and bound: "i < ?n" for i
  proof -
    have other: "?n - i < ?n" using positive bound by arith
    have reflected: "digits coefficients ! i = digits coefficients ! (?n - i)"
      using palindrome_nth_reflect[OF palindrome, of i] positive bound length by simp
    have emitted: "emit False coefficients ! i = emit False coefficients ! (?n - i)"
      using reflected digit_nth[OF bound] digit_nth[OF other] by simp
    show ?thesis
      using reverse_palindrome_physical_digit[OF bound coefficient_bound]
        reverse_palindrome_physical_digit[OF other coefficient_bound] emitted by simp
  qed
  have last_digit: "digits coefficients ! ?n = 1"
    using growth by (simp add: digits_def nth_append length_emit)
  have first_digit: "digits coefficients ! 0 = 1"
    using palindrome_nth_reflect[OF palindrome, of 0] width length last_digit by simp
  have edge: "normalized_growth_digit ?S ?C 0 = 1"
    using reverse_palindrome_physical_digit[OF width coefficient_bound]
      digit_nth[OF width] first_digit by simp
  have outer_symmetry: "?S 0 = ?S (?n - 1)"
    using source_symmetry[OF width] by simp
  have outer: "?C 1 = 1 \<and> ?S 0 = 11"
    by (rule reverse_palindrome_growth_outer
        [OF width start finish bits outer_symmetry edge carry_step])
  have coefficients: "?S i = 11 * ?C (Suc i)" if "i < ?n" for i
    using reverse_palindrome_growth_inward
      [OF width outer[THEN conjunct1] finish outer[THEN conjunct2]
        bits source_symmetry interior carry_step, of "Suc i"] that by simp
  have "coefficients ! i = 0 \<or> coefficients ! i = 11" if "i < ?n" for i
  proof -
    have "?C (Suc i) = 0 \<or> ?C (Suc i) = 1" using bits[of "Suc i"] by arith
    with coefficients[OF that] show ?thesis by auto
  qed
  then show "hd coefficients = 11 \<and> (\<forall>s \<in> set coefficients. s = 0 \<or> s = 11)"
    using outer width by (auto simp: in_set_conv_nth hd_conv_nth; blast)
next
  assume property: "hd coefficients = 11 \<and> (\<forall>s \<in> set coefficients. s = 0 \<or> s = 11)"
  have nonempty: "coefficients \<noteq> []" and symmetric: "rev coefficients = coefficients"
    using valid by (auto simp: valid_pair_def)
  let ?bits = "map (\<lambda>s. s = 11) coefficients"
  have coefficients: "coefficients = map (\<lambda>b. if b then 11 else 0) ?bits"
  proof -
    have "map (\<lambda>s. if s = 11 then 11 else 0) coefficients = coefficients"
      by (rule map_idI) (use property in auto)
    then show ?thesis by (simp add: map_map o_def)
  qed
  have symmetry: "rev ?bits = ?bits" using symmetric by (simp add: rev_map)
  have bits_nonempty: "?bits \<noteq> []" using nonempty by simp
  have last_coefficient: "last coefficients = 11"
  proof -
    have "last coefficients = hd (rev coefficients)" by (rule hd_rev[symmetric])
    also have "... = hd coefficients" by (simp only: symmetric)
    also have "... = 11" using property by (rule conjunct1)
    finally show ?thesis .
  qed
  have last: "last ?bits" by (simp only: last_map[OF nonempty] last_coefficient)
  show "rev (digits coefficients) = digits coefficients"
    using reverse_decimal_palindrome_preimage_growth[OF symmetry bits_nonempty last] coefficients by simp
qed

definition reverse_q19_growth_guard :: "nat list \<Rightarrow> nat option \<Rightarrow> bool" where
  "reverse_q19_growth_guard pairs center \<longleftrightarrow>
    pairs \<noteq> [] \<and> hd pairs = 11 \<and>
    (\<forall>p \<in> set pairs. p = 0 \<or> p = 11) \<and>
    (case center of None \<Rightarrow> True | Some d \<Rightarrow> d = 0)"

theorem reverse_q19_growth_preimage_exact:
  assumes valid: "valid_pair (reverse_q19_coefficients pairs center)"
    and growth: "carry_out False (reverse_q19_coefficients pairs center)"
  shows "(rev (digits (reverse_q19_coefficients pairs center)) =
      digits (reverse_q19_coefficients pairs center)) = reverse_q19_growth_guard pairs center"
proof -
  have midpoint: "(2 * d = 0 \<or> 2 * d = 11) \<longleftrightarrow> (d::nat) = 0" for d by arith
  have odd_midpoint: "2 * (d::nat) \<noteq> 11" for d by arith
  have guard: "(hd (reverse_q19_coefficients pairs center) = 11 \<and>
      (\<forall>s \<in> set (reverse_q19_coefficients pairs center). s = 0 \<or> s = 11)) =
      reverse_q19_growth_guard pairs center"
    using valid by (cases pairs; cases center)
      (auto simp: reverse_q19_growth_guard_def reverse_q19_coefficients_def
        valid_pair_def midpoint odd_midpoint)
  show ?thesis using reverse_growth_palindrome_preimage_exact[OF valid growth] guard by simp
qed

lemma reverse_q19_no_growth_guard_no_carry:
  assumes "reverse_q19_no_growth_guard pairs center"
  shows "\<not> carry_out False (reverse_q19_coefficients pairs center)"
proof (rule reverse_decimal_no_carry_final)
  have middle: "2 * d < 10 \<longleftrightarrow> (d::nat) < 5" for d by arith
  show "\<forall>s\<in>set (reverse_q19_coefficients pairs center). s < 10"
    using assms by (cases center)
      (auto simp: reverse_q19_no_growth_guard_def reverse_q19_coefficients_def middle)
qed

lemma reverse_q19_growth_guard_has_carry:
  assumes "reverse_q19_growth_guard pairs center"
  shows "carry_out False (reverse_q19_coefficients pairs center)"
  using assms by (cases pairs; cases center)
    (auto simp: reverse_q19_growth_guard_def reverse_q19_coefficients_def
      carry_out_append carry_out_def domain_def)

definition reverse_q19_palindrome_guard :: "nat list \<Rightarrow> nat option \<Rightarrow> bool" where
  "reverse_q19_palindrome_guard pairs center \<longleftrightarrow>
    reverse_q19_no_growth_guard pairs center \<or> reverse_q19_growth_guard pairs center"

definition reverse_q19_executable_guard :: "nat list \<Rightarrow> nat option \<Rightarrow> bool" where
  "reverse_q19_executable_guard pairs center =
    (case pairs of [] \<Rightarrow> reverse_q19_no_growth_guard pairs center
    | p # ps \<Rightarrow> if p < 10 then reverse_q19_no_growth_guard pairs center
      else reverse_q19_growth_guard pairs center)"

lemma reverse_q19_executable_guard_exact:
  "reverse_q19_executable_guard pairs center = reverse_q19_palindrome_guard pairs center"
  by (cases pairs)
     (auto simp: reverse_q19_executable_guard_def reverse_q19_palindrome_guard_def
       reverse_q19_no_growth_guard_def reverse_q19_growth_guard_def)

theorem reverse_q19_palindrome_preimage_exact:
  assumes valid: "valid_pair (reverse_q19_coefficients pairs center)"
  shows "(rev (digits (reverse_q19_coefficients pairs center)) =
      digits (reverse_q19_coefficients pairs center)) = reverse_q19_palindrome_guard pairs center"
proof (cases "carry_out False (reverse_q19_coefficients pairs center)")
  case True
  have "\<not> reverse_q19_no_growth_guard pairs center"
    using True reverse_q19_no_growth_guard_no_carry by blast
  with reverse_q19_growth_preimage_exact[OF valid True] show ?thesis
    by (simp add: reverse_q19_palindrome_guard_def)
next
  case False
  have "\<not> reverse_q19_growth_guard pairs center"
    using False reverse_q19_growth_guard_has_carry by blast
  with reverse_q19_no_growth_preimage_exact[OF valid False] show ?thesis
    by (simp add: reverse_q19_palindrome_guard_def)
qed

corollary reverse_q19_executable_preimage_exact:
  assumes "valid_pair (reverse_q19_coefficients pairs center)"
  shows "(rev (digits (reverse_q19_coefficients pairs center)) =
      digits (reverse_q19_coefficients pairs center)) = reverse_q19_executable_guard pairs center"
  using reverse_q19_palindrome_preimage_exact[OF assms]
    reverse_q19_executable_guard_exact by simp

ML \<open>
  val checked = @{thms reverse_no_growth_palindrome_preimage_exact
    reverse_growth_palindrome_preimage_exact reverse_q19_no_growth_preimage_exact
    reverse_q19_growth_preimage_exact reverse_q19_executable_preimage_exact
    reverse_q19_first_arrival_exact};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Reverse palindrome consumer depends on an oracle";
\<close>

end
