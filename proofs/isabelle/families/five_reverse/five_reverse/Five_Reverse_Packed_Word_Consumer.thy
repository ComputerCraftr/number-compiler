theory Five_Reverse_Packed_Word_Consumer
  imports Five_Reverse_Packed_Consumer
begin

unbundle bit_operations_syntax

definition five_bcd_upper_mask :: "nat \<Rightarrow> nat" where
  "five_bcd_upper_mask n = 14 * five_bcd_low_mask n"

lemma five_bcd_upper_mask_successor:
  "five_bcd_upper_mask (Suc n) = 14 + 16 * five_bcd_upper_mask n"
  by (simp add: five_bcd_upper_mask_def algebra_simps)

lemma five_bcd_upper_mask_bound:
  "five_bcd_upper_mask n < 16^n"
  using five_bcd_low_mask_geometric[of n]
  unfolding five_bcd_upper_mask_def by arith

lemma five_bcd_upper_mask_lane:
  assumes "i < n"
  shows "(five_bcd_upper_mask n div 16^i) mod 16 = 14"
  using assms
proof (induction n arbitrary: i)
  case 0
  then show ?case by simp
next
  case (Suc n)
  note smaller_lane = Suc.IH
  note index_bound = Suc.prems
  show ?case
  proof (cases i)
    case 0
    then show ?thesis
      by (simp add: five_bcd_upper_mask_successor)
  next
    case (Suc j)
    have "j < n" using index_bound Suc by simp
    then have digit: "(five_bcd_upper_mask n div 16^j) mod 16 = 14"
      by (rule smaller_lane)
    have quotient:
      "(14 + 16 * five_bcd_upper_mask n) div 16 = five_bcd_upper_mask n"
      by (subst div_mult_self2) simp_all
    have exponent: "(16::nat)^Suc j = 16 * 16^j"
      by (simp only: power_Suc)
    have shift: "five_bcd_upper_mask (Suc n) div 16^(Suc j) =
        five_bcd_upper_mask n div 16^j"
      by (simp only: five_bcd_upper_mask_successor exponent div_mult2_eq quotient)
    show ?thesis using Suc shift digit by simp
  qed
qed

lemma five_bcd_upper_mask_bit_lane:
  assumes "i < n"
  shows "take_bit 4 (drop_bit (4 * i) (five_bcd_upper_mask n)) = 14"
  using five_bcd_upper_mask_lane[OF assms]
  by (simp add: take_bit_eq_mod drop_bit_eq_div power_mult)

lemma five_bcd_upper_lane_from_word:
  assumes "i < n"
  shows "take_bit 4 (drop_bit (4 * i) (packed AND five_bcd_upper_mask n)) =
    take_bit 4 (drop_bit (4 * i) packed) AND 14"
  using five_bcd_masked_lane[of i packed "five_bcd_upper_mask n"]
    five_bcd_upper_mask_bit_lane[OF assms] by simp

lemma five_bcd_upper_masked_word_bounded:
  fixes packed :: nat
  assumes "packed < 16^n"
  shows "(packed AND five_bcd_upper_mask n) < 16^n"
proof -
  have power: "(2::nat)^(4*n) = 16^n"
    by (simp add: power_mult)
  have upper: "five_bcd_upper_mask n < 2^(4*n)"
    using five_bcd_upper_mask_bound[of n] by (simp only: power)
  have source: "packed < 2^(4*n)" using assms by (simp only: power)
  have source_take: "take_bit (4*n) packed = packed"
    using source by (simp only: take_bit_eq_mod mod_less)
  have upper_take: "take_bit (4*n) (five_bcd_upper_mask n) = five_bcd_upper_mask n"
    using upper by (simp only: take_bit_eq_mod mod_less)
  have truncated: "take_bit (4*n) (packed AND five_bcd_upper_mask n) =
      packed AND five_bcd_upper_mask n"
    by (simp only: take_bit_and source_take upper_take)
  have "take_bit (4*n) (packed AND five_bcd_upper_mask n) < 2^(4*n)"
    by (simp add: take_bit_eq_mod)
  then show ?thesis using truncated by (simp only: power)
qed

text \<open>The following candidate is a direct recursive materialization of the
upper-nibble view. It is an arithmetic comparison object, not another
production scheduler or source certificate.\<close>

fun five_bcd_upper_lanes :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "five_bcd_upper_lanes 0 packed = 0"
| "five_bcd_upper_lanes (Suc n) packed =
     ((packed mod 16) AND 14) + 16 * five_bcd_upper_lanes n (packed div 16)"

lemma five_bcd_upper_digit_bound:
  fixes packed :: nat
  shows "((packed mod 16) AND 14) < 16"
proof -
  have decomposition: "take_bit 4 (packed AND 14) =
      take_bit 4 packed AND take_bit 4 (14::nat)"
    by (rule take_bit_and)
  have p: "take_bit 4 packed = packed mod 16"
    by (simp add: take_bit_eq_mod)
  have c: "take_bit 4 (14::nat) = 14" by (simp add: take_bit_eq_mod)
  have projection: "take_bit 4 (packed AND 14) = (packed mod 16) AND 14"
    unfolding decomposition by (simp only: p c)
  have "take_bit 4 (packed AND 14) < 16"
    by (simp add: take_bit_eq_mod)
  then show ?thesis using projection by simp
qed

lemma five_bcd_upper_lanes_bound:
  "five_bcd_upper_lanes n packed < 16^n"
proof (induction n arbitrary: packed)
  case 0
  then show ?case by simp
next
  case (Suc n)
  note digit = five_bcd_upper_digit_bound[of packed]
  note tail = Suc.IH[of "packed div 16"]
  show ?case using digit tail by (simp add: power_Suc; arith)
qed

lemma five_bcd_upper_lanes_at:
  assumes "i < n"
  shows "(five_bcd_upper_lanes n packed div 16^i) mod 16 =
    ((packed div 16^i) mod 16) AND 14"
  using assms
proof (induction n arbitrary: i packed)
  case 0
  then show ?case by simp
next
  case (Suc n)
  note induct = Suc.IH
  note bound = Suc.prems
  show ?case
  proof (cases i)
    case 0
    note digit = five_bcd_upper_digit_bound[of packed]
    show ?thesis using 0 digit by simp
  next
    case (Suc j)
    have "j < n" using bound Suc by simp
    then have smaller:
      "(five_bcd_upper_lanes n (packed div 16) div 16^j) mod 16 =
       ((packed div 16 div 16^j) mod 16) AND 14"
      by (rule induct)
    note digit_bound = five_bcd_upper_digit_bound[of packed]
    have digit_zero: "((packed mod 16) AND 14) div 16 = 0"
      by (rule div_less[OF digit_bound])
    have quotient:
      "(((packed mod 16) AND 14) + 16 * five_bcd_upper_lanes n (packed div 16)) div 16 =
        five_bcd_upper_lanes n (packed div 16)"
      by (subst div_mult_self2) (simp_all add: digit_zero)
    have exponent: "(16::nat)^Suc j = 16 * 16^j"
      by (simp only: power_Suc)
    show ?thesis using Suc smaller
      by (simp only: Suc five_bcd_upper_lanes.simps exponent div_mult2_eq quotient)
  qed
qed

theorem five_bcd_upper_word_and:
  assumes "packed < 16^n"
  shows "packed AND five_bcd_upper_mask n = five_bcd_upper_lanes n packed"
proof (rule five_bcd_word_extensionality)
  show "(packed AND five_bcd_upper_mask n) < 16^n"
    by (rule five_bcd_upper_masked_word_bounded[OF assms])
  show "five_bcd_upper_lanes n packed < 16^n"
    by (rule five_bcd_upper_lanes_bound)
  show "\<forall>i<n. ((packed AND five_bcd_upper_mask n) div 16^i) mod 16 =
      (five_bcd_upper_lanes n packed div 16^i) mod 16"
  proof (intro allI impI)
    fix i
    assume bound: "i < n"
    note masked = five_bcd_upper_lane_from_word[OF bound, of packed]
    note lanes = five_bcd_upper_lanes_at[OF bound, of packed]
    show "((packed AND five_bcd_upper_mask n) div 16^i) mod 16 =
        (five_bcd_upper_lanes n packed div 16^i) mod 16"
      using masked lanes by (simp add: take_bit_eq_mod drop_bit_eq_div power_mult)
  qed
qed

text \<open>A separate decimal decoder bridge. This does not assert that the
integer mask/shift implementation has produced the encoded E digits.\<close>

fun five_bcd_valid :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "five_bcd_valid 0 packed = (packed = 0)"
| "five_bcd_valid (Suc n) packed =
    (packed mod 16 < 10 \<and> five_bcd_valid n (packed div 16))"

fun five_bcd_decimal :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "five_bcd_decimal 0 packed = 0"
| "five_bcd_decimal (Suc n) packed =
    packed mod 16 + 10 * five_bcd_decimal n (packed div 16)"

fun five_bcd_E_decimal :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "five_bcd_E_decimal 0 packed = 0"
| "five_bcd_E_decimal (Suc n) packed =
    10 * five_bcd_E_decimal n (packed div 16) +
      ((packed mod 16) + 99 * ((packed mod 16) mod 2)) div 2"

theorem five_bcd_decimal_reflected_E:
  assumes "five_bcd_valid n packed"
  shows "five_bcd_E_decimal n packed = five_reflected_E (five_bcd_decimal n packed)"
  using assms
proof (induction n arbitrary: packed)
  case 0
  then show ?case by (simp add: five_reflected_E_def five_parity_mask.simps)
next
  case (Suc n)
  have digit: "packed mod 16 < 10" using Suc.prems by simp
  have tail: "five_bcd_valid n (packed div 16)" using Suc.prems by simp
  have induction: "five_bcd_E_decimal n (packed div 16) =
      five_reflected_E (five_bcd_decimal n (packed div 16))"
    by (rule Suc.IH[OF tail])
  have quotient: "five_bcd_decimal (Suc n) packed div 10 =
      five_bcd_decimal n (packed div 16)"
    using digit by simp
  have remainder: "five_bcd_decimal (Suc n) packed mod 10 = packed mod 16"
    using digit by simp
  note equation = five_reflected_E_digit_equation[of "five_bcd_decimal (Suc n) packed"]
  show ?case using equation quotient remainder induction by simp
qed

fun five_bcd_drop_low_zero :: "nat \<Rightarrow> nat \<Rightarrow> nat \<times> nat" where
  "five_bcd_drop_low_zero 0 packed = (0, 0)"
| "five_bcd_drop_low_zero (Suc n) packed =
    (if packed mod 16 = 0 then five_bcd_drop_low_zero n (packed div 16)
     else (Suc n, packed))"

theorem five_bcd_zero_normalization:
  assumes "five_bcd_valid n packed"
  shows "five_reflected_normalize (five_bcd_decimal n packed) =
    five_bcd_decimal (fst (five_bcd_drop_low_zero n packed))
      (snd (five_bcd_drop_low_zero n packed))"
  using assms
proof (induction n arbitrary: packed)
  case 0
  then show ?case by (simp add: five_reflected_normalize.simps)
next
  case (Suc n)
  have digit: "packed mod 16 < 10" using Suc.prems by simp
  have tail: "five_bcd_valid n (packed div 16)" using Suc.prems by simp
  show ?case
  proof (cases "packed mod 16 = 0")
    case True
    note induction = Suc.IH[OF tail]
    show ?thesis using True induction
      by (simp add: five_reflected_normalize_times_ten)
  next
    case False
    have residue: "five_bcd_decimal (Suc n) packed mod 10 = packed mod 16"
      using digit by simp
    have nonzero: "five_bcd_decimal (Suc n) packed \<noteq> 0"
      using residue False by auto
    have normalized: "five_reflected_normalize (five_bcd_decimal (Suc n) packed) =
        five_bcd_decimal (Suc n) packed"
      using nonzero residue False by (subst five_reflected_normalize.simps) simp
    show ?thesis using False normalized by simp
  qed
qed

text \<open>Carry-free addition at the lowest encoded lane is shared by the
M and E inductions.  The caller must prove the lane bound for its specific
masked tail before using this lemma.\<close>

lemma five_bcd_decimal_low_add:
  fixes packed delta n :: nat
  assumes lane: "packed mod 16 + delta < 10"
  shows "five_bcd_decimal (Suc n) (packed + delta) =
    five_bcd_decimal (Suc n) packed + delta"
proof -
  have bound: "packed mod 16 + delta < 16" using lane by arith
  have split: "packed + delta = (packed mod 16 + delta) + 16 * (packed div 16)"
    using div_mult_mod_eq[of packed 16] by arith
  have low_expanded:
    "((packed mod 16 + delta) + 16 * (packed div 16)) mod 16 =
      packed mod 16 + delta"
    by (subst mod_mult_self2) (rule mod_less[OF bound])
  have low: "(packed + delta) mod 16 = packed mod 16 + delta"
    unfolding split by (rule low_expanded)
  have high: "(packed + delta) div 16 = packed div 16"
    unfolding split
    by (subst div_mult_self2) (simp_all add: div_less[OF bound])
  show ?thesis by (simp only: five_bcd_decimal.simps low high; arith)
qed

lemma five_bcd_and_concatenation:
  fixes packed mask :: nat
  shows "packed AND mask = ((packed mod 16) AND (mask mod 16)) +
    16 * ((packed div 16) AND (mask div 16))"
proof -
  have four: "(2::nat)^4 = 16" by simp
  have low: "(packed AND mask) mod 16 = (packed mod 16) AND (mask mod 16)"
    using take_bit_and[of 4 packed mask]
    unfolding take_bit_eq_mod four .
  have high: "(packed AND mask) div 16 = (packed div 16) AND (mask div 16)"
    using drop_bit_and[of 4 packed mask]
    unfolding drop_bit_eq_div four .
  have decomposition: "packed AND mask =
      16 * ((packed AND mask) div 16) + (packed AND mask) mod 16"
    using div_mult_mod_eq[of "packed AND mask" 16] by (simp only: mult.commute)
  have "packed AND mask =
      16 * ((packed AND mask) div 16) + (packed AND mask) mod 16"
    by (rule decomposition)
  also have "... = ((packed mod 16) AND (mask mod 16)) +
      16 * ((packed div 16) AND (mask div 16))"
    by (simp only: high low add.commute)
  finally show ?thesis .
qed

definition five_bcd_M :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "five_bcd_M n packed =
    5 * (packed AND five_bcd_low_mask n) +
      8 * (packed AND five_bcd_upper_mask n)"

definition five_bcd_E :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "five_bcd_E n packed =
    (packed AND five_bcd_upper_mask n) div 2 +
      80 * (packed AND five_bcd_low_mask n)"

lemma five_bcd_low_word_split:
  "packed AND five_bcd_low_mask (Suc n) =
    ((packed mod 16) AND 1) +
      16 * ((packed div 16) AND five_bcd_low_mask n)"
proof -
  have low: "five_bcd_low_mask (Suc n) mod 16 = 1" by simp
  have high: "five_bcd_low_mask (Suc n) div 16 = five_bcd_low_mask n"
    unfolding five_bcd_low_mask.simps
    by (subst div_mult_self2) simp_all
  show ?thesis using five_bcd_and_concatenation[of packed "five_bcd_low_mask (Suc n)"]
    unfolding low high .
qed

lemma five_bcd_upper_word_split:
  "packed AND five_bcd_upper_mask (Suc n) =
    ((packed mod 16) AND 14) +
      16 * ((packed div 16) AND five_bcd_upper_mask n)"
proof -
  have low: "five_bcd_upper_mask (Suc n) mod 16 = 14"
    by (simp add: five_bcd_upper_mask_successor)
  have high: "five_bcd_upper_mask (Suc n) div 16 = five_bcd_upper_mask n"
    unfolding five_bcd_upper_mask_successor
    by (subst div_mult_self2) simp_all
  show ?thesis using five_bcd_and_concatenation[of packed "five_bcd_upper_mask (Suc n)"]
    unfolding low high .
qed

lemma five_bcd_M_word_recursion:
  assumes "packed mod 16 < 10"
  shows "five_bcd_M (Suc n) packed =
    5 * ((packed mod 16) mod 2) +
      16 * (five_bcd_M n (packed div 16) + (packed mod 16) div 2)"
  using five_bcd_digit_masks[OF assms]
  unfolding five_bcd_M_def five_bcd_low_word_split five_bcd_upper_word_split
  by (simp add: algebra_simps)

lemma five_bcd_upper_word_even:
  "even (packed AND five_bcd_upper_mask n)"
  by (simp add: even_and_iff five_bcd_upper_mask_def)

lemma five_bcd_E_word_recursion:
  assumes "packed mod 16 < 10"
  shows "five_bcd_E (Suc n) packed =
    (packed mod 16) div 2 +
      16 * (five_bcd_E n (packed div 16) + 5 * ((packed mod 16) mod 2))"
proof -
  let ?tail = "(packed div 16) AND five_bcd_upper_mask n"
  have even: "even ?tail" by (rule five_bcd_upper_word_even)
  have mask: "(packed mod 16) AND 14 = 2 * ((packed mod 16) div 2)"
    by (rule five_bcd_digit_masks(2)[OF assms])
  have parity: "(packed mod 16) AND 1 = (packed mod 16) mod 2"
    by (rule five_bcd_digit_masks(1)[OF assms])
  show ?thesis using even mask parity
    unfolding five_bcd_E_def five_bcd_low_word_split five_bcd_upper_word_split
    by (simp add: algebra_simps)
qed

lemma five_bcd_M_low_kind:
  assumes "five_bcd_valid n packed"
  shows "five_bcd_M n packed mod 16 = 0 \<or> five_bcd_M n packed mod 16 = 5"
proof (cases n)
  case 0
  then show ?thesis by (simp add: five_bcd_M_def five_bcd_upper_mask_def)
next
  case (Suc k)
  have digit: "packed mod 16 < 10" using assms Suc by simp
  have parity_bound: "(packed mod 16) mod 2 < 2" by simp
  have parity: "(packed mod 16) mod 2 = 0 \<or> (packed mod 16) mod 2 = 1"
    using parity_bound by arith
  note recurrence = five_bcd_M_word_recursion[OF digit, of k]
  have bound: "5 * ((packed mod 16) mod 2) < 16" using parity_bound by arith
  have projected:
    "(5 * ((packed mod 16) mod 2) +
        16 * (five_bcd_M k (packed div 16) + (packed mod 16) div 2)) mod 16 =
      5 * ((packed mod 16) mod 2)"
    by (subst mod_mult_self2) (rule mod_less[OF bound])
  have head: "five_bcd_M (Suc k) packed mod 16 = 5 * ((packed mod 16) mod 2)"
    unfolding recurrence by (rule projected)
  show ?thesis using head parity Suc by auto
qed

lemma five_bcd_E_low_bound:
  assumes "five_bcd_valid n packed"
  shows "five_bcd_E n packed mod 16 < 5"
proof (cases n)
  case 0
  then show ?thesis by (simp add: five_bcd_E_def five_bcd_upper_mask_def)
next
  case (Suc k)
  have digit: "packed mod 16 < 10" using assms Suc by simp
  have half: "(packed mod 16) div 2 < 5"
    using digit by (simp add: div_less_iff_less_mult)
  note recurrence = five_bcd_E_word_recursion[OF digit, of k]
  have bound: "(packed mod 16) div 2 < 16" using half by arith
  have projected:
    "((packed mod 16) div 2 +
        16 * (five_bcd_E k (packed div 16) + 5 * ((packed mod 16) mod 2))) mod 16 =
      (packed mod 16) div 2"
    by (subst mod_mult_self2) (rule mod_less[OF bound])
  have head: "five_bcd_E (Suc k) packed mod 16 = (packed mod 16) div 2"
    unfolding recurrence by (rule projected)
  show ?thesis using head half Suc by simp
qed

lemma five_bcd_decimal_cons:
  assumes "digit < 10"
  shows "five_bcd_decimal (Suc n) (digit + 16 * tail) =
    digit + 10 * five_bcd_decimal n tail"
proof -
  have bound: "digit < 16" using assms by arith
  have low: "(digit + 16 * tail) mod 16 = digit"
    by (subst mod_mult_self2) (rule mod_less[OF bound])
  have high: "(digit + 16 * tail) div 16 = tail"
    by (subst div_mult_self2) (simp_all add: div_less[OF bound])
  show ?thesis by (simp only: five_bcd_decimal.simps low high)
qed

theorem five_bcd_M_decodes:
  assumes "five_bcd_valid n packed"
  shows "five_bcd_decimal (Suc n) (five_bcd_M n packed) =
    5 * five_bcd_decimal n packed"
  using assms
proof (induction n arbitrary: packed)
  case 0
  then show ?case by (simp add: five_bcd_M_def five_bcd_upper_mask_def)
next
  case (Suc n)
  let ?d = "packed mod 16"
  let ?b = "?d mod 2"
  let ?q = "?d div 2"
  let ?tail = "packed div 16"
  let ?word = "five_bcd_M n ?tail"
  have digit: "?d < 10" using Suc.prems by simp
  have valid: "five_bcd_valid n ?tail" using Suc.prems by simp
  have half: "?q < 5" using digit by (simp add: div_less_iff_less_mult)
  have parity_bound: "?b < 2" by simp
  have parity: "?b = 0 \<or> ?b = 1" using parity_bound by arith
  have low: "?word mod 16 = 0 \<or> ?word mod 16 = 5"
    by (rule five_bcd_M_low_kind[OF valid])
  have no_spill: "?word mod 16 + ?q < 10" using low half by arith
  have add: "five_bcd_decimal (Suc n) (?word + ?q) =
      five_bcd_decimal (Suc n) ?word + ?q"
    by (rule five_bcd_decimal_low_add[OF no_spill])
  have output_digit: "5 * ?b < 10" using parity_bound by arith
  have rec: "five_bcd_M (Suc n) packed = 5 * ?b + 16 * (?word + ?q)"
    by (rule five_bcd_M_word_recursion[OF digit])
  have decoded_output: "five_bcd_decimal (Suc (Suc n)) (five_bcd_M (Suc n) packed) =
      5 * ?b + 10 * five_bcd_decimal (Suc n) (?word + ?q)"
    unfolding rec by (rule five_bcd_decimal_cons[OF output_digit])
  have induction: "five_bcd_decimal (Suc n) ?word = 5 * five_bcd_decimal n ?tail"
    by (rule Suc.IH[OF valid])
  have decomposed: "?d = 2 * ?q + ?b"
    using div_mult_mod_eq[of ?d 2] by (simp add: mult.commute)
  have linear: "\<And>d q b z :: nat. d = 2*q + b \<Longrightarrow>
      5*b + 10*(5*z + q) = 5*(d + 10*z)"
    by (simp add: algebra_simps)
  have arithmetic: "5 * ?b + 10 * (5 * five_bcd_decimal n ?tail + ?q) =
      5 * (?d + 10 * five_bcd_decimal n ?tail)"
    by (rule linear[OF decomposed])
  have "five_bcd_decimal (Suc (Suc n)) (five_bcd_M (Suc n) packed) =
      5 * ?b + 10 * five_bcd_decimal (Suc n) (?word + ?q)"
    by (rule decoded_output)
  also have "... = 5 * ?b + 10 * (5 * five_bcd_decimal n ?tail + ?q)"
    by (simp only: add induction)
  also have "... = 5 * (?d + 10 * five_bcd_decimal n ?tail)"
    by (rule arithmetic)
  also have "... = 5 * five_bcd_decimal (Suc n) packed"
    by (simp only: five_bcd_decimal.simps)
  finally show ?case .
qed

theorem five_bcd_E_decodes:
  assumes "five_bcd_valid n packed"
  shows "five_bcd_decimal (Suc n) (five_bcd_E n packed) =
    five_bcd_E_decimal n packed"
  using assms
proof (induction n arbitrary: packed)
  case 0
  then show ?case by (simp add: five_bcd_E_def five_bcd_upper_mask_def)
next
  case (Suc n)
  let ?d = "packed mod 16"
  let ?b = "?d mod 2"
  let ?q = "?d div 2"
  let ?tail = "packed div 16"
  let ?word = "five_bcd_E n ?tail"
  have digit: "?d < 10" using Suc.prems by simp
  have valid: "five_bcd_valid n ?tail" using Suc.prems by simp
  have half: "?q < 5" using digit by (simp add: div_less_iff_less_mult)
  have parity_bound: "?b < 2" by simp
  have parity: "?b = 0 \<or> ?b = 1" using parity_bound by arith
  have low: "?word mod 16 < 5" by (rule five_bcd_E_low_bound[OF valid])
  have no_spill: "?word mod 16 + 5 * ?b < 10"
    using low parity by auto
  have add: "five_bcd_decimal (Suc n) (?word + 5 * ?b) =
      five_bcd_decimal (Suc n) ?word + 5 * ?b"
    by (rule five_bcd_decimal_low_add[OF no_spill])
  have rec: "five_bcd_E (Suc n) packed = ?q + 16 * (?word + 5 * ?b)"
    by (rule five_bcd_E_word_recursion[OF digit])
  have decoded_output: "five_bcd_decimal (Suc (Suc n)) (five_bcd_E (Suc n) packed) =
      ?q + 10 * five_bcd_decimal (Suc n) (?word + 5 * ?b)"
    unfolding rec by (rule five_bcd_decimal_cons) (use half in arith)
  have induction: "five_bcd_decimal (Suc n) ?word = five_bcd_E_decimal n ?tail"
    by (rule Suc.IH[OF valid])
  have cases: "?d=0 \<or> ?d=1 \<or> ?d=2 \<or> ?d=3 \<or> ?d=4 \<or>
      ?d=5 \<or> ?d=6 \<or> ?d=7 \<or> ?d=8 \<or> ?d=9"
    using digit by arith
  have digit_identity: "?q + 50 * ?b = (?d + 99 * ?b) div 2"
    using cases by (elim disjE; simp)
  have linear: "\<And>q b z x :: nat. q + 50*b = x \<Longrightarrow>
      q + 10*(z + 5*b) = 10*z + x"
    by (simp add: algebra_simps)
  have arithmetic: "?q + 10 * (five_bcd_E_decimal n ?tail + 5 * ?b) =
      10 * five_bcd_E_decimal n ?tail + (?d + 99 * ?b) div 2"
    by (rule linear[OF digit_identity])
  have "five_bcd_decimal (Suc (Suc n)) (five_bcd_E (Suc n) packed) =
      ?q + 10 * five_bcd_decimal (Suc n) (?word + 5 * ?b)"
    by (rule decoded_output)
  also have "... = ?q + 10 * (five_bcd_E_decimal n ?tail + 5 * ?b)"
    by (simp only: add induction)
  also have "... = 10 * five_bcd_E_decimal n ?tail + (?d + 99 * ?b) div 2"
    by (rule arithmetic)
  also have "... = five_bcd_E_decimal (Suc n) packed"
    by (simp only: five_bcd_E_decimal.simps)
  finally show ?case .
qed

theorem five_bcd_E_decodes_physical:
  assumes "five_bcd_valid n packed"
  shows "five_bcd_decimal (Suc n) (five_bcd_E n packed) =
    five_reflected_E (five_bcd_decimal n packed)"
  using five_bcd_E_decodes[OF assms] five_bcd_decimal_reflected_E[OF assms] by simp

lemma five_bcd_drop_low_zero_valid:
  assumes "five_bcd_valid n packed"
  shows "five_bcd_valid (fst (five_bcd_drop_low_zero n packed))
    (snd (five_bcd_drop_low_zero n packed))"
  using assms
  by (induction n arbitrary: packed) (auto split: if_splits)

theorem five_bcd_pair_physical_conditional:
  assumes source: "five_bcd_valid n packed"
      and reflected: "five_bcd_valid (Suc n) (five_bcd_E n packed)"
  defines "cut \<equiv> five_bcd_drop_low_zero (Suc n) (five_bcd_E n packed)"
  shows "five_bcd_decimal (Suc (fst cut)) (five_bcd_M (fst cut) (snd cut)) =
    five_reverse_step (five_reverse_step (five_bcd_decimal n packed))"
proof -
  have valid_cut: "five_bcd_valid (fst cut) (snd cut)"
    unfolding cut_def by (rule five_bcd_drop_low_zero_valid[OF reflected])
  have decoded: "five_bcd_decimal (Suc (fst cut)) (five_bcd_M (fst cut) (snd cut)) =
      5 * five_bcd_decimal (fst cut) (snd cut)"
    by (rule five_bcd_M_decodes[OF valid_cut])
  have normalized: "five_bcd_decimal (fst cut) (snd cut) =
      five_reflected_normalize (five_reflected_E (five_bcd_decimal n packed))"
    using five_bcd_zero_normalization[OF reflected]
      five_bcd_E_decodes_physical[OF source]
    unfolding cut_def by simp
  show ?thesis using decoded normalized five_reflected_physical_two_step by simp
qed

lemma five_bcd_valid_low_add:
  assumes valid: "five_bcd_valid (Suc n) packed"
      and lane: "packed mod 16 + delta < 10"
  shows "five_bcd_valid (Suc n) (packed + delta)"
proof -
  have bound: "packed mod 16 + delta < 16" using lane by arith
  have split: "packed + delta = (packed mod 16 + delta) + 16 * (packed div 16)"
    using div_mult_mod_eq[of packed 16] by arith
  have low_expanded:
    "((packed mod 16 + delta) + 16 * (packed div 16)) mod 16 =
      packed mod 16 + delta"
    by (subst mod_mult_self2) (rule mod_less[OF bound])
  have low: "(packed + delta) mod 16 = packed mod 16 + delta"
    unfolding split by (rule low_expanded)
  have high: "(packed + delta) div 16 = packed div 16"
    unfolding split
    by (subst div_mult_self2) (simp_all add: div_less[OF bound])
  show ?thesis using valid lane by (simp only: five_bcd_valid.simps low high)
qed

lemma five_bcd_valid_cons:
  assumes "digit < 10" "five_bcd_valid n tail"
  shows "five_bcd_valid (Suc n) (digit + 16 * tail)"
proof -
  have bound: "digit < 16" using assms by arith
  have low: "(digit + 16 * tail) mod 16 = digit"
    by (subst mod_mult_self2) (rule mod_less[OF bound])
  have high: "(digit + 16 * tail) div 16 = tail"
    by (subst div_mult_self2) (simp_all add: div_less[OF bound])
  show ?thesis using assms by (simp only: five_bcd_valid.simps low high)
qed

theorem five_bcd_E_valid:
  assumes "five_bcd_valid n packed"
  shows "five_bcd_valid (Suc n) (five_bcd_E n packed)"
  using assms
proof (induction n arbitrary: packed)
  case 0
  then show ?case by (simp add: five_bcd_E_def five_bcd_upper_mask_def)
next
  case (Suc n)
  let ?d = "packed mod 16"
  let ?b = "?d mod 2"
  let ?q = "?d div 2"
  let ?tail = "packed div 16"
  let ?word = "five_bcd_E n ?tail"
  have digit: "?d < 10" using Suc.prems by simp
  have valid: "five_bcd_valid n ?tail" using Suc.prems by simp
  have half: "?q < 5" using digit by (simp add: div_less_iff_less_mult)
  have parity_bound: "?b < 2" by simp
  have parity: "?b = 0 \<or> ?b = 1" using parity_bound by arith
  have low: "?word mod 16 < 5" by (rule five_bcd_E_low_bound[OF valid])
  have no_spill: "?word mod 16 + 5 * ?b < 10" using low parity by auto
  have valid_word: "five_bcd_valid (Suc n) ?word" by (rule Suc.IH[OF valid])
  have valid_tail: "five_bcd_valid (Suc n) (?word + 5 * ?b)"
    by (rule five_bcd_valid_low_add[OF valid_word no_spill])
  have rec: "five_bcd_E (Suc n) packed = ?q + 16 * (?word + 5 * ?b)"
    by (rule five_bcd_E_word_recursion[OF digit])
  show ?case unfolding rec by (rule five_bcd_valid_cons) (use half valid_tail in auto)
qed

corollary five_bcd_pair_physical:
  assumes "five_bcd_valid n packed"
  defines "cut \<equiv> five_bcd_drop_low_zero (Suc n) (five_bcd_E n packed)"
  shows "five_bcd_decimal (Suc (fst cut)) (five_bcd_M (fst cut) (snd cut)) =
    five_reverse_step (five_reverse_step (five_bcd_decimal n packed))"
  using five_bcd_pair_physical_conditional[OF assms(1) five_bcd_E_valid[OF assms(1)]]
    unfolding cut_def .

definition five_bcd_bounded_pair :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat option" where
  "five_bcd_bounded_pair bits n packed =
    (let source = five_bcd_decimal n packed;
         cut = five_bcd_drop_low_zero (Suc n) (five_bcd_E n packed);
         endpoint = five_bcd_decimal (Suc (fst cut)) (five_bcd_M (fst cut) (snd cut))
     in if five_reverse_step source < 2^bits \<and> endpoint < 2^bits
        then Some endpoint else None)"

theorem five_bcd_bounded_pair_exact:
  assumes "five_bcd_valid n packed"
  shows "five_bcd_bounded_pair bits n packed =
    five_physical_bounded_pair bits (five_bcd_decimal n packed)"
  unfolding five_bcd_bounded_pair_def five_physical_bounded_pair_def Let_def
  using five_bcd_pair_physical[OF assms] by simp

corollary five_bcd_bounded_pair_first_refusal:
  assumes "five_bcd_valid n packed"
      "2^bits \<le> five_reverse_step (five_bcd_decimal n packed)"
  shows "five_bcd_bounded_pair bits n packed = None"
  using five_bcd_bounded_pair_exact[OF assms(1)]
    five_physical_bounded_pair_first_refusal[OF assms(2)] by simp


ML \<open>
  val checked = @{thms five_bcd_upper_word_and five_bcd_and_concatenation
    five_bcd_M_word_recursion five_bcd_E_word_recursion
    five_bcd_M_decodes five_bcd_E_decodes five_bcd_E_valid
    five_bcd_zero_normalization five_bcd_pair_physical
    five_bcd_bounded_pair_exact five_bcd_bounded_pair_first_refusal};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Packed five-reverse word consumer depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked then
    error "Skipped packed five-reverse word consumer proof" else ();
\<close>

end
