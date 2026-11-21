theory Reverse_Q19_Packed_Lanes
  imports Reverse_Palindrome_Growth_Iff "HOL.Bit_Operations"
begin

unbundle bit_operations_syntax

text \<open>Base-64 lane packing used by the decimal pair-field publisher.\<close>

fun reverse_q19_pack :: "nat list \<Rightarrow> nat" where
  "reverse_q19_pack [] = 0"
| "reverse_q19_pack (d # ds) = d + 64 * reverse_q19_pack ds"

lemma reverse_q19_pack_bias:
  "reverse_q19_pack (map (\<lambda>d. d + bias) lanes) =
    reverse_q19_pack lanes + bias * reverse_q19_pack (replicate (length lanes) 1)"
  by (induction lanes) (simp_all add: algebra_simps)

lemma reverse_q19_pack_scale:
  "reverse_q19_pack (map (\<lambda>d. factor * d) lanes) = factor * reverse_q19_pack lanes"
  by (induction lanes) (simp_all add: algebra_simps)

lemma reverse_q19_lane_ones_times:
  "63 * reverse_q19_pack (replicate n 1) + 1 = 64 ^ n"
  by (induction n) (simp_all add: algebra_simps)

lemma reverse_q19_lane_ones:
  "(64 ^ n - 1) div 63 = reverse_q19_pack (replicate n 1)"
proof -
  have "64 ^ n - 1 = 63 * reverse_q19_pack (replicate n 1)"
    using reverse_q19_lane_ones_times[of n] by arith
  then show ?thesis by simp
qed

lemma reverse_q19_biased_lane_bound:
  fixes d :: nat
  assumes "d < 19"
  shows "d + 22 < 64"
  using assms by arith

lemma reverse_q19_native_carry_lane:
  fixes d carry :: nat
  assumes digit: "d < 19" and inlet: "carry < 2"
  shows "(d + 54 + carry) div 64 = (if 10 \<le> d + carry then 1 else 0)"
    and "bit ((d + 54 + carry) mod 64) 5 \<longleftrightarrow> d + carry < 10"
proof -
  have cases: "d = 0 \<or> d = 1 \<or> d = 2 \<or> d = 3 \<or> d = 4 \<or>
      d = 5 \<or> d = 6 \<or> d = 7 \<or> d = 8 \<or> d = 9 \<or>
      d = 10 \<or> d = 11 \<or> d = 12 \<or> d = 13 \<or> d = 14 \<or>
      d = 15 \<or> d = 16 \<or> d = 17 \<or> d = 18"
    using digit by (rule nat_less_nineteen_cases)
  have inlets: "carry = 0 \<or> carry = 1" using inlet by arith
  show "(d + 54 + carry) div 64 = (if 10 \<le> d + carry then 1 else 0)"
    using cases inlets by (elim disjE; simp)
  show "bit ((d + 54 + carry) mod 64) 5 \<longleftrightarrow> d + carry < 10"
    using cases inlets by (elim disjE; simp add: bit_iff_odd)
qed

fun reverse_q19_native_carries :: "nat \<Rightarrow> nat list \<Rightarrow> nat list" where
  "reverse_q19_native_carries carry [] = []"
| "reverse_q19_native_carries carry (d # ds) =
    (if 10 \<le> d + carry then 1 else 0) #
    reverse_q19_native_carries (if 10 \<le> d + carry then 1 else 0) ds"

theorem reverse_q19_native_carry_word:
  assumes valid: "\<forall>d \<in> set lanes. d < 19"
    and inlet: "carry < 2"
    and index: "i < length lanes"
  shows "bit (reverse_q19_pack (map (\<lambda>d. d + 54) lanes) + carry)
        (6 * i + 5) \<longleftrightarrow>
      reverse_q19_native_carries carry lanes ! i = 0"
  using valid inlet index
proof (induction lanes arbitrary: carry i)
  case Nil
  then show ?case by simp
next
  case (Cons d ds)
  define next_carry :: nat where
    "next_carry = (if 10 \<le> d + carry then 1 else 0)"
  define word where
    "word = reverse_q19_pack (map (\<lambda>d. d + 54) (d # ds)) + carry"
  have digit: "d < 19" and tail: "\<forall>d \<in> set ds. d < 19"
    using Cons.prems by auto
  have inlet: "carry < 2" using Cons.prems by simp
  have bounded: "next_carry < 2" by (simp add: next_carry_def)
  have div_lane: "(d + 54 + carry) div 64 = next_carry"
    using reverse_q19_native_carry_lane(1)[OF digit inlet] by (simp add: next_carry_def)
  have word_split:
    "word = (d + 54 + carry) + 64 * reverse_q19_pack (map (\<lambda>d. d + 54) ds)"
    by (simp add: word_def algebra_simps)
  have mod_word: "word mod 64 = (d + 54 + carry) mod 64"
    by (simp add: word_split)
  have div_word:
    "word div 64 = reverse_q19_pack (map (\<lambda>d. d + 54) ds) + next_carry"
    using div_lane by (simp add: word_split add.commute)
  show ?case
  proof (cases i)
    case 0
    have local_bit: "bit word 5 \<longleftrightarrow> bit (word mod 64) 5"
      using bit_take_bit_iff[of 6 word 5] by (simp add: take_bit_eq_mod)
    show ?thesis using local_bit mod_word reverse_q19_native_carry_lane(2)[OF digit inlet]
      by (simp add: 0 word_def next_carry_def)
  next
    case (Suc j)
    have index: "j < length ds" using Cons.prems Suc by simp
    have shifted: "bit word (6 * Suc j + 5) \<longleftrightarrow> bit (word div 64) (6 * j + 5)"
      using fun_cong[OF bit_drop_bit_eq[of 6 word], of "6 * j + 5"]
      by (simp add: drop_bit_eq_div algebra_simps)
    have tail_bit:
      "bit (reverse_q19_pack (map (\<lambda>d. d + 54) ds) + next_carry)
        (6 * j + 5) \<longleftrightarrow> reverse_q19_native_carries next_carry ds ! j = 0"
      by (rule Cons.IH[OF tail bounded index])
    show ?thesis using shifted div_word tail_bit by (simp add: Suc word_def next_carry_def)
  qed
qed

corollary reverse_q19_native_carry_production:
  assumes valid: "\<forall>d \<in> set lanes. d < 19"
    and index: "i < length lanes"
  shows "bit (reverse_q19_pack lanes + 54 * ((64 ^ length lanes - 1) div 63))
        (6 * i + 5) \<longleftrightarrow>
      reverse_q19_native_carries 0 lanes ! i = 0"
proof -
  have inlet: "(0::nat) < 2" by simp
  note exact = reverse_q19_native_carry_word[OF valid inlet index]
  show ?thesis using exact
    by (simp only: reverse_q19_pack_bias add_0_right reverse_q19_lane_ones)
qed

lemma reverse_q19_first_lane:
  assumes "d < 64"
  shows "reverse_q19_pack (d # ds) mod 64 = d"
  using assms by simp

lemma reverse_q19_remaining_lanes:
  assumes "d < 64"
  shows "reverse_q19_pack (d # ds) div 64 = reverse_q19_pack ds"
  using assms by simp

lemma reverse_q19_biased_high_bit:
  fixes d :: nat
  assumes "d < 19"
  shows "(d + 22) AND (2 ^ 5) \<noteq> 0 \<longleftrightarrow> 10 \<le> d"
proof -
  have cases: "d = 0 \<or> d = 1 \<or> d = 2 \<or> d = 3 \<or> d = 4 \<or>
      d = 5 \<or> d = 6 \<or> d = 7 \<or> d = 8 \<or> d = 9 \<or>
      d = 10 \<or> d = 11 \<or> d = 12 \<or> d = 13 \<or> d = 14 \<or>
      d = 15 \<or> d = 16 \<or> d = 17 \<or> d = 18"
    using assms by (rule nat_less_nineteen_cases)
  have high: "bit (d + 22) 5 \<longleftrightarrow> 10 \<le> d"
    using cases by (elim disjE; simp add: bit_iff_odd)
  show ?thesis using high by (simp only: and_exp_eq_0_iff_not_bit not_not)
qed

lemma reverse_q19_low_high_disjoint:
  "take_bit 6 a AND (64 * b) = (0::nat)"
proof (rule bit_eqI)
  fix n
  have scale: "64 * b = push_bit 6 b" by (simp add: push_bit_eq_mult mult.commute)
  show "bit (take_bit 6 a AND (64 * b)) n \<longleftrightarrow> bit (0::nat) n"
    by (auto simp: scale bit_simps)
qed

lemma reverse_q19_and_lane_split:
  fixes a b x y :: nat
  assumes "a < 64" "b < 64"
  shows "(a + 64*x) AND (b + 64*y) = (a AND b) + 64*(x AND y)"
proof -
  have a_low: "take_bit 6 a = a" using assms(1) by (simp add: take_bit_nat_eq_self_iff)
  have b_low: "take_bit 6 b = b" using assms(2) by (simp add: take_bit_nat_eq_self_iff)
  have ab_low: "take_bit 6 (a AND b) = a AND b" using a_low b_low by simp
  have a_or: "a + 64*x = a OR (64*x)"
    by (rule disjunctive_add_eq_or) (use reverse_q19_low_high_disjoint[of a x] a_low in simp)
  have b_or: "b + 64*y = b OR (64*y)"
    by (rule disjunctive_add_eq_or) (use reverse_q19_low_high_disjoint[of b y] b_low in simp)
  have ab_or: "(a AND b) + 64*(x AND y) = (a AND b) OR (64*(x AND y))"
    by (rule disjunctive_add_eq_or) (use reverse_q19_low_high_disjoint[of "a AND b" "x AND y"] ab_low in simp)
  have scale_x: "64*x = push_bit 6 x" by (simp add: push_bit_eq_mult mult.commute)
  have scale_y: "64*y = push_bit 6 y" by (simp add: push_bit_eq_mult mult.commute)
  have scale_xy: "64*(x AND y) = push_bit 6 (x AND y)" by (simp add: push_bit_eq_mult mult.commute)
  have a_bit: "bit a n \<Longrightarrow> n < 6" for n
    using a_low bit_take_bit_iff by metis
  have b_bit: "bit b n \<Longrightarrow> n < 6" for n
    using b_low bit_take_bit_iff by metis
  have split_bits: "(a OR push_bit 6 x) AND (b OR push_bit 6 y) =
      (a AND b) OR push_bit 6 (x AND y)"
  proof (rule bit_eqI)
    fix n
    assume "possible_bit TYPE(nat) n"
    show "bit ((a OR push_bit 6 x) AND (b OR push_bit 6 y)) n \<longleftrightarrow>
        bit ((a AND b) OR push_bit 6 (x AND y)) n"
    proof (cases "n < 6")
      case True
      then show ?thesis
        by (auto simp only: bit_and_iff bit_or_iff bit_push_bit_iff possible_bit_nat)
    next
      case False
      have "\<not> bit a n" "\<not> bit b n" using False a_bit b_bit by blast+
      with False show ?thesis
        by (auto simp only: bit_and_iff bit_or_iff bit_push_bit_iff possible_bit_nat)
    qed
  qed
  show ?thesis using split_bits a_or b_or ab_or scale_x scale_y scale_xy by metis
qed

lemma reverse_q19_masked_lanes:
  assumes "\<forall>d \<in> set lanes. d < 19"
  shows "(reverse_q19_pack (map (\<lambda>d. d + 22) lanes) AND
      reverse_q19_pack (replicate (length lanes) 32) = 0) \<longleftrightarrow>
    (\<forall>d \<in> set lanes. d < 10)"
  using assms
proof (induction lanes)
  case Nil
  then show ?case by simp
next
  case (Cons d ds)
  have bound: "d + 22 < 64" using Cons.prems by auto
  have split: "(d + 22 + 64 * reverse_q19_pack (map (\<lambda>x. x + 22) ds)) AND
      (32 + 64 * reverse_q19_pack (replicate (length ds) 32)) =
      ((d + 22) AND 32) + 64 *
       (reverse_q19_pack (map (\<lambda>x. x + 22) ds) AND
        reverse_q19_pack (replicate (length ds) 32))"
    by (rule reverse_q19_and_lane_split[OF bound]) simp
  have lane_ok: "((d + 22) AND 32 = 0) \<longleftrightarrow> d < 10"
    using reverse_q19_biased_high_bit[of d] Cons.prems by (auto; arith)
  show ?case using Cons split lane_ok by simp
qed

theorem reverse_q19_packed_no_growth_test:
  assumes "\<forall>d \<in> set lanes. d < 19"
  defines "ones \<equiv> (64 ^ length lanes - 1) div 63"
  shows "((reverse_q19_pack lanes + 22 * ones) AND (32 * ones) = 0) \<longleftrightarrow>
    (\<forall>d \<in> set lanes. d < 10)"
proof -
  have ones_eq: "ones = reverse_q19_pack (replicate (length lanes) 1)"
    unfolding ones_def by (rule reverse_q19_lane_ones)
  have scaled_mask: "reverse_q19_pack (replicate (length lanes) 32) =
      32 * reverse_q19_pack (replicate (length lanes) 1)"
    using reverse_q19_pack_scale[of 32 "replicate (length lanes) 1"]
    by simp
  have mask: "reverse_q19_pack (replicate (length lanes) 32) = 32 * ones"
    using scaled_mask ones_eq by simp
  show ?thesis
    using reverse_q19_masked_lanes[OF assms(1)]
      reverse_q19_pack_bias[where lanes=lanes and bias=22] mask
    by (simp only: ones_eq)
qed

lemma reverse_q19_packed_low_bits:
  assumes "\<forall>d \<in> set lanes. d < 64"
  shows "reverse_q19_pack lanes AND reverse_q19_pack (replicate (length lanes) 1) =
    reverse_q19_pack (map (\<lambda>d. d mod 2) lanes)"
  using assms
proof (induction lanes)
  case Nil
  then show ?case by simp
next
  case (Cons d ds)
  have split: "(d + 64 * reverse_q19_pack ds) AND
      (1 + 64 * reverse_q19_pack (replicate (length ds) 1)) =
      (d AND 1) + 64 *
        (reverse_q19_pack ds AND reverse_q19_pack (replicate (length ds) 1))"
    by (rule reverse_q19_and_lane_split) (use Cons.prems in auto)
  show ?case using Cons split by (simp add: one_and_eq ac_simps)
qed

lemma reverse_q19_pack_injective:
  assumes "\<forall>d \<in> set left. d < 64" "\<forall>d \<in> set right. d < 64"
    and "length left = length right"
    and "reverse_q19_pack left = reverse_q19_pack right"
  shows "left = right"
  using assms
proof (induction left arbitrary: right)
  case Nil
  then show ?case by simp
next
  case (Cons d ds)
  then obtain e es where right: "right = e # es" by (cases right) auto
  have bounds: "d < 64" "e < 64" using Cons.prems right by auto
  have heads: "d = e"
    using arg_cong[OF Cons.prems(4), of "\<lambda>x. x mod 64"] bounds right by simp
  have tails: "reverse_q19_pack ds = reverse_q19_pack es"
    using arg_cong[OF Cons.prems(4), of "\<lambda>x. x div 64"] bounds right by simp
  have "ds = es" by (rule Cons.IH) (use Cons.prems right tails in auto)
  with heads right show ?case by simp
qed

theorem reverse_q19_packed_growth_test:
  assumes bound: "\<forall>d \<in> set lanes. d < 19"
  defines "ones \<equiv> (64 ^ length lanes - 1) div 63"
  shows "reverse_q19_pack lanes = 11 * (reverse_q19_pack lanes AND ones) \<longleftrightarrow>
    (\<forall>d \<in> set lanes. d = 0 \<or> d = 11)"
proof -
  have ones_eq: "ones = reverse_q19_pack (replicate (length lanes) 1)"
    unfolding ones_def by (rule reverse_q19_lane_ones)
  have lane_bound: "\<forall>d \<in> set lanes. d < 64" using bound by auto
  have bits: "reverse_q19_pack lanes AND ones =
      reverse_q19_pack (map (\<lambda>d. d mod 2) lanes)"
    using reverse_q19_packed_low_bits[OF lane_bound] by (simp only: ones_eq)
  have scaled: "11 * (reverse_q19_pack lanes AND ones) =
      reverse_q19_pack (map (\<lambda>d. 11 * (d mod 2)) lanes)"
    using bits reverse_q19_pack_scale[of 11 "map (\<lambda>d. d mod 2) lanes"]
    by (simp add: map_map o_def)
  have image_bound: "\<forall>d \<in> set (map (\<lambda>d. 11 * (d mod 2)) lanes). d < 64"
    by auto
  have image_length: "length lanes = length (map (\<lambda>d. 11 * (d mod 2)) lanes)" by simp
  have equal: "reverse_q19_pack lanes = reverse_q19_pack (map (\<lambda>d. 11 * (d mod 2)) lanes) \<longleftrightarrow>
      lanes = map (\<lambda>d. 11 * (d mod 2)) lanes"
  proof
    assume "reverse_q19_pack lanes = reverse_q19_pack (map (\<lambda>d. 11 * (d mod 2)) lanes)"
    then show "lanes = map (\<lambda>d. 11 * (d mod 2)) lanes"
      by (rule reverse_q19_pack_injective[OF lane_bound image_bound image_length])
  next
    assume "lanes = map (\<lambda>d. 11 * (d mod 2)) lanes"
    then show "reverse_q19_pack lanes = reverse_q19_pack (map (\<lambda>d. 11 * (d mod 2)) lanes)"
      by simp
  qed
  have digit_identity: "d = 11 * (d mod 2) \<longleftrightarrow> d = 0 \<or> (d::nat) = 11" for d
  proof (cases "d mod 2 = 0")
    case True
    have "d \<noteq> 11" using True by auto
    with True show ?thesis by simp
  next
    case False
    have "d mod 2 = 1" using mod_less_divisor[of 2 d] False by arith
    moreover have "d \<noteq> 0" using False by auto
    ultimately show ?thesis by simp
  qed
  have "(lanes = map (\<lambda>d. 11 * (d mod 2)) lanes) \<longleftrightarrow>
      (\<forall>d \<in> set lanes. d = 0 \<or> d = 11)"
    by (induction lanes) (auto simp: digit_identity)
  with scaled equal show ?thesis by simp
qed

theorem reverse_q19_packed_palindrome_preimage_exact:
  assumes valid: "valid_pair (reverse_q19_coefficients pairs center)"
  defines "ones \<equiv> (64 ^ length pairs - 1) div 63"
  shows "(rev (digits (reverse_q19_coefficients pairs center)) =
      digits (reverse_q19_coefficients pairs center)) \<longleftrightarrow>
    (((reverse_q19_pack pairs + 22 * ones) AND (32 * ones) = 0 \<and>
        (case center of None \<Rightarrow> True | Some d \<Rightarrow> d < 5)) \<or>
     (pairs \<noteq> [] \<and> hd pairs = 11 \<and>
        reverse_q19_pack pairs = 11 * (reverse_q19_pack pairs AND ones) \<and>
        (case center of None \<Rightarrow> True | Some d \<Rightarrow> d = 0)))"
proof -
  have bound: "\<forall>d \<in> set pairs. d < 19"
    using valid by (cases center) (auto simp: valid_pair_def reverse_q19_coefficients_def)
  have no_growth: "((reverse_q19_pack pairs + 22 * ones) AND (32 * ones) = 0) \<longleftrightarrow>
      (\<forall>d \<in> set pairs. d < 10)"
    using reverse_q19_packed_no_growth_test[OF bound, folded ones_def] .
  have growth: "reverse_q19_pack pairs = 11 * (reverse_q19_pack pairs AND ones) \<longleftrightarrow>
      (\<forall>d \<in> set pairs. d = 0 \<or> d = 11)"
    using reverse_q19_packed_growth_test[OF bound, folded ones_def] .
  show ?thesis
    using reverse_q19_palindrome_preimage_exact[OF valid] no_growth growth
    by (auto simp: reverse_q19_palindrome_guard_def reverse_q19_no_growth_guard_def
      reverse_q19_growth_guard_def)
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles @{thms reverse_q19_pack_bias
    reverse_q19_native_carry_lane reverse_q19_native_carry_word
    reverse_q19_native_carry_production
    reverse_q19_biased_lane_bound reverse_q19_first_lane reverse_q19_remaining_lanes
    reverse_q19_biased_high_bit reverse_q19_packed_no_growth_test
    reverse_q19_packed_growth_test reverse_q19_packed_palindrome_preimage_exact}) then ()
    else error "Reverse Q19 packed-lane proof depends on an oracle";
\<close>

end
