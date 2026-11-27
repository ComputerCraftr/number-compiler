theory Mahler_CF_Ordered_Row_Blocks
  imports Mahler_CF_Multitick_Tiles Mahler_CF_Minimal_Prefix Mahler_Exact_Even_Event_Threshold
    "Shared_Carry_Dynamics.Decimal_Word_Reversal"
begin

text \<open>A block begins at the authenticated exponent before its first row.
Every leaf denotes one physical successor and its complete significant
MSD-first word. Internal nodes retain chronological order and the source
exponent of the adjoining seam.\<close>

definition mahler_cf_physical_row :: "nat \<Rightarrow> nat list" where
  "mahler_cf_physical_row n =
    rev (reflected_trim_high (mahler_cf_pow5_word (Suc n)))"

fun mahler_cf_ordered_row_block :: "nat \<Rightarrow> nat \<Rightarrow> nat list list" where
  "mahler_cf_ordered_row_block n 0 = [mahler_cf_physical_row n]"
| "mahler_cf_ordered_row_block n (Suc k) =
    mahler_cf_ordered_row_block n k @
      mahler_cf_ordered_row_block (n + 2^k) k"

lemma mahler_cf_ordered_row_block_exact:
  "mahler_cf_ordered_row_block n k =
    map (\<lambda>i. mahler_cf_physical_row (n+i)) [0..<2^k]"
proof (induction k arbitrary: n)
  case 0
  then show ?case by simp
next
  case (Suc k)
  have range: "[0..<2^(Suc k)] = [0..<2^k] @ [2^k..<2^k+2^k]"
    using upt_add_eq_append[of 0 "2^k" "2^k"] by (simp add: power_Suc mult_2)
  have mapped: "map ((+) (2^k)) [0..<2^k] =
      map (\<lambda>i::nat. i + 2^k) [0..<2^k]"
    by (rule map_cong[OF refl]) (simp add: add.commute)
  have shifted: "[2^k..<2^k+2^k] = map ((+) (2^k)) [0..<2^k]"
    using map_add_upt[of "2^k" "2^k"] mapped by metis
  have split:
    "map (\<lambda>i. mahler_cf_physical_row (n+i)) [0..<2^(Suc k)] =
      map (\<lambda>i. mahler_cf_physical_row (n+i)) [0..<2^k] @
      map (\<lambda>i. mahler_cf_physical_row ((n+2^k)+i)) [0..<2^k]"
    by (subst range) (simp only: map_append shifted map_map comp_def add.assoc)
  show ?case
    by (simp only: mahler_cf_ordered_row_block.simps Suc.IH split)
qed

definition mahler_cf_row_block_word :: "nat \<Rightarrow> nat \<Rightarrow> nat list" where
  "mahler_cf_row_block_word n k = concat (mahler_cf_ordered_row_block n k)"

theorem mahler_cf_ordered_block_word_split:
  "mahler_cf_row_block_word n (Suc k) =
    mahler_cf_row_block_word n k @ mahler_cf_row_block_word (n+2^k) k"
  by (simp add: mahler_cf_row_block_word_def)

theorem mahler_cf_ordered_block_action_split:
  "mahler_cf_word (mahler_cf_row_block_word n (Suc k)) =
    ordered_matrix2_multiply (mahler_cf_word (mahler_cf_row_block_word n k))
      (mahler_cf_word (mahler_cf_row_block_word (n+2^k) k))"
  by (simp only: mahler_cf_ordered_block_word_split mahler_cf_word_append)

theorem mahler_cf_ordered_block_inside_prefix:
  "take count (mahler_cf_row_block_word n (Suc k)) =
    (let left = mahler_cf_row_block_word n k;
         right = mahler_cf_row_block_word (n+2^k) k
     in if count \<le> length left then take count left
        else left @ take (count - length left) right)"
  by (simp add: mahler_cf_ordered_block_word_split take_append Let_def)

theorem mahler_cf_ordered_block_inside_prefix_action:
  "mahler_cf_word (take count (mahler_cf_row_block_word n (Suc k))) =
    (let left = mahler_cf_row_block_word n k;
         right = mahler_cf_row_block_word (n+2^k) k
     in if count \<le> length left then mahler_cf_word (take count left)
        else ordered_matrix2_multiply (mahler_cf_word left)
          (mahler_cf_word (take (count - length left) right)))"
  by (simp add: mahler_cf_ordered_block_inside_prefix mahler_cf_word_append Let_def)

theorem mahler_cf_retained_lower_prefix_action:
  fixes digits :: "nat list" and lower middle :: nat
  assumes ordered: "lower \<le> middle"
  shows "mahler_cf_word (take middle digits) =
    ordered_matrix2_multiply (mahler_cf_word (take lower digits))
      (mahler_cf_word (take (middle - lower) (drop lower digits)))"
proof -
  have "take middle digits =
      take lower digits @ take (middle - lower) (drop lower digits)"
    using take_add[of lower "middle - lower" digits] ordered by simp
  then show ?thesis by (simp only: mahler_cf_word_append)
qed
text \<open>Each block leaf is the selected physical tile output with its full
low and high halo. The theorem names both exponent and chronological
continued-fraction action, so a matching numeric endpoint alone cannot
supply the ordered word.\<close>

theorem mahler_cf_ordered_block_leaf_tile:
  fixes n :: nat and input :: "nat list"
  defines "input \<equiv> [0] @ mahler_cf_pow5_word n @ [0]"
  shows "mahler_cf_word (mahler_cf_row_block_word n 0) =
    mahler_cf_word (dropWhile ((=) 0)
      (map (overlap_recursive 0 mahler_cf_mul5_cell ((!) (rev input)))
        [0..<length input - 1]))"
proof -
  have selected:
    "rev (mahler_cf_full_steps 1 (mahler_cf_pow5_word n)) =
      map (overlap_run mahler_cf_mul5_cell 1 ((!) (rev input)))
        [0..<length input - 1]"
    using mahler_cf_temporal_tile_selected_output[where ticks=1 and n=n]
    by (simp add: input_def)
  have cells:
    "overlap_recursive 0 mahler_cf_mul5_cell ((!) (rev input)) =
      overlap_run mahler_cf_mul5_cell 1 ((!) (rev input))"
    by (rule ext) (simp only: mahler_cf_cell_tile power_0)
  have whole:
    "map (overlap_recursive 0 mahler_cf_mul5_cell ((!) (rev input)))
        [0..<length input - 1] =
      rev (mahler_cf_full_steps 1 (mahler_cf_pow5_word n))"
    using selected by (simp only: cells)
  have trimmed:
    "dropWhile ((=) 0)
      (map (overlap_recursive 0 mahler_cf_mul5_cell ((!) (rev input)))
        [0..<length input - 1]) =
      rev (reflected_trim_high (mahler_cf_full_steps 1 (mahler_cf_pow5_word n)))"
    by (simp only: whole reflected_reverse_trim_high)
  have physical:
    "dropWhile ((=) 0)
      (map (overlap_recursive 0 mahler_cf_mul5_cell ((!) (rev input)))
        [0..<length input - 1]) = mahler_cf_physical_row n"
    using trimmed mahler_cf_full_steps_pow5_exact_word[of 1 n]
    by (simp add: mahler_cf_physical_row_def)
  show ?thesis
    using physical by (simp add: mahler_cf_row_block_word_def)

qed

text \<open>The receiving guard is an admitted half-open source interval.
Containment of a physical CF prefix persists under every later source digit.
The first contained prefix is selected over the full ordered block, including
the boundary between its children.\<close>

definition mahler_cf_guard_contains_prefix ::
  "real \<Rightarrow> real \<Rightarrow> nat list \<Rightarrow> bool" where
  "mahler_cf_guard_contains_prefix low_bound high_bound digits \<longleftrightarrow>
    (case mahler_cf_prefix digits of (q,r,p,s) \<Rightarrow>
      low_bound \<le> mahler_cf_low q r p s \<and>
      mahler_cf_high q r p s \<le> high_bound)"

lemma mahler_cf_guard_contains_narrows:
  assumes "mahler_cf_guard_contains_prefix low_bound high_bound prefix"
  shows "mahler_cf_guard_contains_prefix low_bound high_bound (prefix @ suffix)"
proof -
  obtain q r p s where before: "mahler_cf_prefix prefix = (q,r,p,s)"
    by (cases "mahler_cf_prefix prefix") auto
  obtain q' r' p' s' where after: "mahler_cf_prefix (prefix @ suffix) = (q',r',p',s')"
    by (cases "mahler_cf_prefix (prefix @ suffix)") auto
  show ?thesis
    using mahler_cf_source_prefix_nested[OF before after] assms
    by (auto simp: mahler_cf_guard_contains_prefix_def before after)
qed

lemma mahler_cf_guard_take_monotone:
  assumes "i \<le> j"
      and "mahler_cf_guard_contains_prefix low_bound high_bound (prefix @ take i source)"
  shows "mahler_cf_guard_contains_prefix low_bound high_bound (prefix @ take j source)"
proof -
  have "take j source = take i source @ take (j-i) (drop i source)"
    using assms(1) by (metis add_diff_inverse_nat not_less take_add)
  then show ?thesis
    using mahler_cf_guard_contains_narrows[OF assms(2),
      of "take (j-i) (drop i source)"]
    by (simp add: append.assoc)
qed

text \<open>A finite continued-fraction consumer needs the current affine
fractional action and its complete source guard. It can compose these
quantities before reconstructing the source residue.\<close>

definition mahler_cf_lean_fraction ::
  "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "mahler_cf_lean_fraction gain modulus innovation x =
    (gain * x - innovation) / modulus"

theorem mahler_cf_lean_action_composition:
  fixes gain modulus innovation scale next_modulus offset x :: real
  assumes "modulus \<noteq> 0" "next_modulus \<noteq> 0"
  shows "mahler_cf_lean_fraction scale next_modulus offset
      (mahler_cf_lean_fraction gain modulus innovation x) =
    mahler_cf_lean_fraction (scale * gain) (modulus * next_modulus)
      (scale * innovation + modulus * offset) x"
  using assms by (simp add: mahler_cf_lean_fraction_def field_simps algebra_simps)

theorem mahler_cf_lean_zero_run_complete_guard:
  fixes x :: real
  assumes inlet: "0 \<le> x" "x < 1/2"
      and final: "(3/2)^ticks * x < 1/2"
  shows "cylinder_guard (2^ticks * source) ticks x"
  using mahler_even_run_guard_exact[OF inlet, of ticks source] final by simp

theorem mahler_cf_lean_odd_pair_bounds:
  fixes x :: real
  assumes "1/3 \<le> x" "x < 1/2"
  shows "0 \<le> (3*x-1)/2" "(3*x-1)/2 < 1/4"
    "0 \<le> 3*((3*x-1)/2)/2" "3*((3*x-1)/2)/2 < 1/2"
proof -
  show "0 \<le> (3*x-1)/2" using assms by (simp add: field_simps; linarith)
  show "(3*x-1)/2 < 1/4" using assms by (simp add: field_simps; linarith)
  show "0 \<le> 3*((3*x-1)/2)/2" using assms by (simp add: field_simps; linarith)
  show "3*((3*x-1)/2)/2 < 1/2" using assms by (simp add: field_simps; linarith)
qed

theorem mahler_cf_lean_odd_pair_composition:
  fixes gain modulus innovation x :: real
  assumes "modulus \<noteq> 0"
  shows "3 * ((3 * mahler_cf_lean_fraction gain modulus innovation x - 1) / 2) / 2 =
    mahler_cf_lean_fraction (9 * gain) (4 * modulus)
      (9 * innovation + 3 * modulus) x"
  using assms by (simp add: mahler_cf_lean_fraction_def field_simps algebra_simps)


theorem mahler_cf_lean_scaled_guard_refinement:
  fixes gain scale low_bound high_bound innovation modulus :: real
  assumes gain: "0 < gain" and scale: "0 < scale"
  shows
    "max (low_bound / gain) (innovation / (scale * gain)) =
      max (scale * low_bound) innovation / (scale * gain)"
    "min (high_bound / (2*gain)) ((2*innovation+modulus) / (2*(scale*gain))) =
      min (scale * high_bound) (2*innovation+modulus) / (2*(scale*gain))"
proof -
  have g: "0 < scale*gain" using assms by simp
  have low_bound: "low_bound/gain = (scale*low_bound)/(scale*gain)"
    using scale by simp
  have high_bound: "high_bound/(2*gain) = (scale*high_bound)/(2*(scale*gain))"
    using scale by (simp add: mult.assoc mult.commute mult.left_commute)
  show "max (low_bound / gain) (innovation / (scale * gain)) =
      max (scale * low_bound) innovation / (scale * gain)"
    using low_bound g by (simp only: max_divide_distrib_right if_P less_imp_le)
  show "min (high_bound / (2*gain)) ((2*innovation+modulus) / (2*(scale*gain))) =
      min (scale * high_bound) (2*innovation+modulus) / (2*(scale*gain))"
    using high_bound g by (simp only: min_divide_distrib_right if_P less_imp_le mult_pos_pos zero_less_numeral)
qed


text \<open>The packed temporal lane represents all intervening physical
powers, in ascending chronological order. Each lane has a common decimal
base larger than every selected source row. The common base and finite
bound belong to the issued block, while each selected digit is an exact
projection from that block.\<close>

fun mahler_cf_pack_rows :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "mahler_cf_pack_rows source base 0 = 0"
| "mahler_cf_pack_rows source base (Suc rows) =
    5*source + base * mahler_cf_pack_rows (5*source) base rows"

lemma mahler_cf_pack_head:
  fixes source base rows :: nat
  assumes "0 < base" "5*source < base"
  shows "mahler_cf_pack_rows source base (Suc rows) mod base = 5*source"
    "mahler_cf_pack_rows source base (Suc rows) div base =
      mahler_cf_pack_rows (5*source) base rows"
  using assms by simp_all

theorem mahler_cf_packed_lane_exact:
  fixes source base rows index :: nat
  assumes bound: "5^rows * source < base" and index: "index < rows"
  shows "(mahler_cf_pack_rows source base rows div base^index) mod base =
    5^(Suc index) * source"
  using bound index
proof (induction rows arbitrary: source index)
  case 0
  then show ?case by simp
next
  case (Suc rows)
  have power_bound: "(5::nat) \<le> 5^(Suc rows)"
    using power_increasing[of 1 "Suc rows" "5::nat"] by simp
  have first: "5*source < base"
    by (rule le_less_trans[OF mult_right_mono[OF power_bound] Suc.prems(1)]; simp)
  have positive: "0 < base" using first by arith
  show ?case
  proof (cases index)
    case 0
    then show ?thesis using mahler_cf_pack_head(1)[OF positive first] by simp
  next
    case (Suc digit)
    have next_bound: "5^rows * (5*source) < base"
      using Suc.prems(1) by (simp add: power_Suc mult.assoc mult.commute mult.left_commute)
    have next_index: "digit < rows" using Suc.prems(2) Suc by simp
    have next_lane: "(mahler_cf_pack_rows (5*source) base rows div base^digit) mod base =
        5^(Suc digit) * (5*source)"
      by (rule Suc.IH[OF next_bound next_index])
    have quotient: "mahler_cf_pack_rows source base (Suc rows) div base =
        mahler_cf_pack_rows (5*source) base rows"
      by (rule mahler_cf_pack_head(2)[OF positive first])
    show ?thesis using next_lane quotient Suc
      by (simp add: power_Suc div_mult2_eq mult.assoc mult.commute mult.left_commute)
  qed
qed

lemma mahler_cf_packed_runtime_width:
  fixes source width rows :: nat
  assumes source_width: "source < 10^width"
  shows "5^rows * source < 10^(width+rows)"
proof -
  have pow: "(5::nat)^rows \<le> 10^rows" by (rule power_mono) simp_all
  have first: "5^rows * source \<le> 10^rows * source"
    by (rule mult_right_mono[OF pow]; simp)
  have second: "10^rows * source < 10^rows * 10^width"
    by (rule mult_strict_left_mono[OF source_width]) simp
  show ?thesis using le_less_trans[OF first second]
    by (simp add: power_add mult.commute)
qed

theorem mahler_cf_packed_geometric:
  "mahler_cf_pack_rows source base rows =
    5*source * (\<Sum>i<rows. (5*base)^i)"
proof (induction rows arbitrary: source)
  case 0
  then show ?case by simp
next
  case (Suc rows)
  have sums: "(\<Sum>i<Suc rows. (5*base)^i) =
      1 + (5*base) * (\<Sum>i<rows. (5*base)^i)"
    by (simp only: sum.lessThan_Suc_shift power_0 power_Suc sum_distrib_left)
  show ?case using Suc.IH[of "5*source"]
    by (simp only: mahler_cf_pack_rows.simps sums; simp add: algebra_simps)
qed

theorem mahler_cf_packed_closed_form:
  assumes "1 < 5*base"
  shows "mahler_cf_pack_rows source base rows =
    5*source * (((5*base)^rows - 1) div (5*base - 1))"
  by (simp only: mahler_cf_packed_geometric geometric_sum_nat[OF assms])


definition mahler_cf_packed_stream ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list" where
  "mahler_cf_packed_stream source base width rows =
    concat (map (\<lambda>i. dropWhile ((=) 0)
      (mahler_cf_decimal_digits width
        ((mahler_cf_pack_rows source base rows div base^i) mod base))) [0..<rows])"

definition mahler_cf_literal_rows ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list" where
  "mahler_cf_literal_rows source width rows =
    concat (map (\<lambda>i. dropWhile ((=) 0)
      (mahler_cf_decimal_digits width (5^(Suc i)*source))) [0..<rows])"

theorem mahler_cf_packed_stream_exact:
  assumes bound: "5^rows * source < base"
  shows "mahler_cf_packed_stream source base width rows =
    mahler_cf_literal_rows source width rows"
proof -
  have rows: "map (\<lambda>i. dropWhile ((=) 0)
       (mahler_cf_decimal_digits width
         ((mahler_cf_pack_rows source base rows div base^i) mod base))) [0..<rows] =
     map (\<lambda>i. dropWhile ((=) 0)
       (mahler_cf_decimal_digits width (5^(Suc i)*source))) [0..<rows]"
    by (rule map_cong[OF refl]) (simp add: mahler_cf_packed_lane_exact[OF bound])
  show ?thesis
    by (simp only: mahler_cf_packed_stream_def mahler_cf_literal_rows_def rows)
qed

lemma mahler_cf_decimal_lsd_digit:
  assumes "list_all (\<lambda>d. d < 10) digits"
  shows "(decimal_lsd_value digits div 10^j) mod 10 =
    (if j < length digits then digits!j else 0)"
  using assms
proof (induction j arbitrary: digits)
  case 0
  then show ?case
    by (cases digits) (auto simp: decimal_word_split mult.commute)
next
  case (Suc j)
  show ?case
  proof (cases digits)
    case Nil
    then show ?thesis by simp
  next
    case (Cons d ds)
    have small: "d < 10" and tail: "list_all (\<lambda>d. d < 10) ds"
      using Suc.prems Cons by auto
    have quotient: "decimal_lsd_value digits div 10 = decimal_lsd_value ds"
      using decimal_word_split(1)[OF small, of "decimal_lsd_value ds"] Cons
      by (simp add: mult.commute)
    show ?thesis using Suc.IH[OF tail] quotient Cons
      by (simp add: power_Suc div_mult2_eq mult.commute)
  qed
qed

lemma mahler_cf_padded_digits_lsd:
  assumes decimal: "list_all (\<lambda>d. d < 10) digits"
  shows "rev (mahler_cf_decimal_digits width (decimal_lsd_value digits)) =
    map (\<lambda>j. if j < length digits then digits!j else 0) [0..<width]"
proof (rule nth_equalityI)
  show "length (rev (mahler_cf_decimal_digits width (decimal_lsd_value digits))) =
      length (map (\<lambda>j. if j < length digits then digits!j else 0) [0..<width])"
    by (simp add: mahler_cf_decimal_digits_def)
  fix i
  assume "i < length (rev (mahler_cf_decimal_digits width (decimal_lsd_value digits)))"
  then have i: "i < width" by (simp add: mahler_cf_decimal_digits_def)
  have offset: "width - 1 - (width - Suc i) = i" using i by arith
  show "rev (mahler_cf_decimal_digits width (decimal_lsd_value digits)) ! i =
      map (\<lambda>j. if j < length digits then digits!j else 0) [0..<width] ! i"
    using mahler_cf_decimal_lsd_digit[OF decimal, of i] i
    by (simp add: mahler_cf_decimal_digits_def rev_nth offset)
qed

lemma mahler_cf_padded_lsd_list:
  "map (\<lambda>j. if j < length digits then digits!j else 0) [0..<width] =
    take width digits @ replicate (width - length digits) 0"
proof (rule nth_equalityI)
  show "length (map (\<lambda>j. if j < length digits then digits!j else 0) [0..<width]) =
      length (take width digits @ replicate (width - length digits) 0)"
    by simp
  fix i
  assume i: "i < length (map (\<lambda>j. if j < length digits then digits!j else 0) [0..<width])"
  then show "map (\<lambda>j. if j < length digits then digits!j else 0) [0..<width] ! i =
      (take width digits @ replicate (width - length digits) 0) ! i"
    by (auto simp: nth_append nth_take)
qed

lemma mahler_cf_digits_above_width_zero:
  assumes decimal: "list_all (\<lambda>d. d < 10) digits"
    and fits: "decimal_lsd_value digits < 10^width"
    and i: "width \<le> i" "i < length digits"
  shows "digits!i = 0"
proof -
  have powers: "(10::nat)^width \<le> 10^i"
    by (rule power_increasing[OF i(1)]) simp
  have small: "decimal_lsd_value digits < 10^i" using fits powers by arith
  show ?thesis using mahler_cf_decimal_lsd_digit[OF decimal, of i] small i
    by simp
qed

lemma mahler_cf_trim_fits:
  assumes decimal: "list_all (\<lambda>d. d < 10) digits"
    and fits: "decimal_lsd_value digits < 10^width"
  shows "reflected_trim_high (take width digits) = reflected_trim_high digits"
proof -
  have zeros: "drop width digits = replicate (length digits - width) 0"
  proof (rule nth_equalityI)
    show "length (drop width digits) = length (replicate (length digits - width) 0)" by simp
    fix i
    assume i: "i < length (drop width digits)"
    have bounds: "width \<le> width+i" "width+i < length digits" using i by auto
    show "drop width digits ! i = replicate (length digits - width) 0 ! i"
      using mahler_cf_digits_above_width_zero[OF decimal fits bounds] i
      by (simp add: nth_drop)
  qed
  have "reflected_trim_high digits =
      reflected_trim_high (take width digits @ drop width digits)" by simp
  also have "... = reflected_trim_high (take width digits)"
    by (simp only: zeros mahler_cf_trim_high_zeros)
  finally show ?thesis by simp
qed

theorem mahler_cf_decimal_padded_physical:
  assumes decimal: "list_all (\<lambda>d. d < 10) digits"
    and fits: "decimal_lsd_value digits < 10^width"
  shows "dropWhile ((=) 0) (mahler_cf_decimal_digits width (decimal_lsd_value digits)) =
    rev (reflected_trim_high digits)"
proof -
  have "reflected_trim_high (rev (mahler_cf_decimal_digits width (decimal_lsd_value digits))) =
      reflected_trim_high digits"
    using mahler_cf_padded_digits_lsd[OF decimal, of width]
      mahler_cf_trim_fits[OF decimal fits]
    by (simp only: mahler_cf_padded_lsd_list mahler_cf_trim_high_zeros)
  then show ?thesis by (simp add: reflected_trim_high_def)
qed

theorem mahler_cf_packed_physical_source:
  fixes n width rows :: nat
  assumes source_width: "(5::nat)^n < 10^width"
  shows "mahler_cf_packed_stream (5^n) (10^(width+rows)) (width+rows) rows =
    concat (map (\<lambda>i. rev (reflected_trim_high (mahler_cf_pow5_word (n+Suc i)))) [0..<rows])"
proof -
  have bound: "(5::nat)^rows * 5^n < 10^(width+rows)"
    by (rule mahler_cf_packed_runtime_width[OF source_width])
  have row: "\<And>i. i < rows \<Longrightarrow>
      dropWhile ((=) 0) (mahler_cf_decimal_digits (width+rows) (5^(Suc i)*5^n)) =
      rev (reflected_trim_high (mahler_cf_pow5_word (n+Suc i)))"
  proof -
    fix i assume i: "i < rows"
    have pow: "(5::nat)^(Suc i) \<le> 5^rows"
      by (rule power_increasing) (use i in auto)
    have mono: "(5::nat)^(Suc i)*5^n \<le> 5^rows*5^n"
      by (rule mult_right_mono[OF pow]; simp)
    have fits: "(5::nat)^(Suc i)*5^n < 10^(width+rows)"
      by (rule le_less_trans[OF mono bound])
    show "dropWhile ((=) 0) (mahler_cf_decimal_digits (width+rows) (5^(Suc i)*5^n)) =
      rev (reflected_trim_high (mahler_cf_pow5_word (n+Suc i)))"
      using mahler_cf_decimal_padded_physical[OF mahler_cf_pow5_word_consumer(2),
          of "n+Suc i" "width+rows"] fits
      by (simp only: mahler_cf_pow5_word_consumer power_add mult.commute)
  qed
  have map_rows: "map (\<lambda>i. dropWhile ((=) 0)
        (mahler_cf_decimal_digits (width+rows) (5^(Suc i)*5^n))) [0..<rows] =
      map (\<lambda>i. rev (reflected_trim_high (mahler_cf_pow5_word (n+Suc i)))) [0..<rows]"
  proof (rule map_cong[OF refl])
    fix i assume "i \<in> set [0..<rows]"
    then have "i < rows" by simp
    then show "dropWhile ((=) 0) (mahler_cf_decimal_digits (width+rows) (5^(Suc i)*5^n)) =
      rev (reflected_trim_high (mahler_cf_pow5_word (n+Suc i)))" by (rule row)
  qed
  show ?thesis using mahler_cf_packed_stream_exact[OF bound, of "width+rows"]
    by (simp only: mahler_cf_literal_rows_def map_rows)
qed

theorem mahler_cf_packed_capped_source_action:
  assumes bound: "5^rows * source < base"
  shows "mahler_cf_word (take cap (mahler_cf_packed_stream source base width rows)) =
    mahler_cf_word (take cap (mahler_cf_literal_rows source width rows))"
  using mahler_cf_packed_stream_exact[OF bound] by simp

theorem mahler_cf_packed_capped_first_guard_prefix:
  fixes source base width rows cap index :: nat and low_bound high_bound :: real
    and prefix emitted :: "nat list" and decision :: "nat \<Rightarrow> bool"
  defines "emitted \<equiv> take cap (mahler_cf_packed_stream source base width rows)"
    and "decision \<equiv> (\<lambda>i. mahler_cf_guard_contains_prefix low_bound high_bound
      (prefix @ take i emitted))"
    and "index \<equiv> mahler_cf_binary_decisive decision 1 (length emitted)"
  assumes bound: "5^rows * source < base"
    and nonempty: "emitted \<noteq> []"
    and first: "\<not> decision 0" and last: "decision (length emitted)"
  shows "1 \<le> index" "index \<le> length emitted" "decision index"
    "\<forall>i<index. \<not> decision i"
    "mahler_cf_word (take index emitted) =
      mahler_cf_word (take index (take cap (mahler_cf_literal_rows source width rows)))"
proof -
  have nonempty_length: "1 \<le> length emitted"
    using nonempty by (cases emitted) simp_all
  have previous: "\<And>i. i < 1 \<Longrightarrow> \<not> decision i"
    using first by simp
  have mono: "\<And>i j. i \<le> j \<Longrightarrow> decision i \<Longrightarrow> decision j"
    unfolding decision_def by (rule mahler_cf_guard_take_monotone)
  have selected: "1 \<le> index" "index \<le> length emitted" "decision index"
    "\<forall>i<index. \<not> decision i"
    using mahler_cf_binary_decisive_exact[
      where P=decision and l=1 and h="length emitted",
      OF nonempty_length last previous mono]
    by (simp_all add: index_def)
  show "1 \<le> index" "index \<le> length emitted" "decision index"
    "\<forall>i<index. \<not> decision i"
    using selected by auto
  show "mahler_cf_word (take index emitted) =
      mahler_cf_word (take index (take cap (mahler_cf_literal_rows source width rows)))"
    using mahler_cf_packed_stream_exact[OF bound] by (simp only: emitted_def)
qed

theorem mahler_cf_block_prefix_global_earliest:
  fixes prefix emitted :: "nat list" and low_bound high_bound :: real and index :: nat
  assumes old: "\<not> mahler_cf_guard_contains_prefix low_bound high_bound prefix"
    and new: "\<And>j. j < index \<Longrightarrow>
      \<not> mahler_cf_guard_contains_prefix low_bound high_bound (prefix @ take j emitted)"
    and found: "mahler_cf_guard_contains_prefix low_bound high_bound
      (prefix @ take index emitted)"
    and available: "index \<le> length emitted"
  shows "mahler_cf_guard_contains_prefix low_bound high_bound
      (take (length prefix + index) (prefix @ emitted))"
    "\<And>j. j < length prefix + index \<Longrightarrow>
      \<not> mahler_cf_guard_contains_prefix low_bound high_bound
        (take j (prefix @ emitted))"
proof -
  show "mahler_cf_guard_contains_prefix low_bound high_bound
      (take (length prefix + index) (prefix @ emitted))"
    using found by (simp add: take_append)
  fix j assume before: "j < length prefix + index"
  show "\<not> mahler_cf_guard_contains_prefix low_bound high_bound
      (take j (prefix @ emitted))"
  proof (cases "j < length prefix")
    case True
    have "\<not> mahler_cf_guard_contains_prefix low_bound high_bound (take j prefix)"
    proof
      assume "mahler_cf_guard_contains_prefix low_bound high_bound (take j prefix)"
      then have "mahler_cf_guard_contains_prefix low_bound high_bound
          (take j prefix @ drop j prefix)"
        by (rule mahler_cf_guard_contains_narrows)
      then show False using old by simp
    qed
    then show ?thesis using True by (simp add: take_append)
  next
    case False
    then have "j - length prefix < index" using before by arith
    then show ?thesis using new[of "j - length prefix"] False
      by (simp add: take_append)
  qed
qed

theorem mahler_cf_runtime_physical_first_prefix:
  fixes n width rows cap index :: nat and prefix emitted :: "nat list"
    and decision :: "nat \<Rightarrow> bool" and low_bound high_bound :: real
  defines "emitted \<equiv> take cap (mahler_cf_packed_stream (5^n)
      (10^(width+rows)) (width+rows) rows)"
    and "decision \<equiv> (\<lambda>i. mahler_cf_guard_contains_prefix low_bound high_bound
      (prefix @ take i emitted))"
    and "index \<equiv> mahler_cf_binary_decisive decision 1 (length emitted)"
  assumes source_width: "(5::nat)^n < 10^width"
    and old: "\<not> mahler_cf_guard_contains_prefix low_bound high_bound prefix"
    and nonempty: "emitted \<noteq> []" and last: "decision (length emitted)"
  shows "mahler_cf_guard_contains_prefix low_bound high_bound
      (take (length prefix + index) (prefix @ emitted))"
    "\<And>j. j < length prefix + index \<Longrightarrow>
      \<not> mahler_cf_guard_contains_prefix low_bound high_bound
        (take j (prefix @ emitted))"
    "mahler_cf_word (take index emitted) = mahler_cf_word
      (take index (take cap (concat (map (\<lambda>i.
        rev (reflected_trim_high (mahler_cf_pow5_word (n+Suc i)))) [0..<rows]))))"
proof -
  have nonempty_length: "1 \<le> length emitted" using nonempty by (cases emitted) simp_all
  have previous: "\<And>i. i < 1 \<Longrightarrow> \<not> decision i"
    using old by (simp add: decision_def)
  have mono: "\<And>i j. i \<le> j \<Longrightarrow> decision i \<Longrightarrow> decision j"
    unfolding decision_def by (rule mahler_cf_guard_take_monotone)
  have selected: "index \<le> length emitted" "decision index" "\<forall>i<index. \<not> decision i"
    using mahler_cf_binary_decisive_exact[
      where P=decision and l=1 and h="length emitted", OF nonempty_length last previous mono]
    by (simp_all add: index_def)
  have before: "\<And>j. j < index \<Longrightarrow>
      \<not> mahler_cf_guard_contains_prefix low_bound high_bound (prefix @ take j emitted)"
    using selected(3) by (simp add: decision_def)
  have found: "mahler_cf_guard_contains_prefix low_bound high_bound (prefix @ take index emitted)"
    using selected(2) by (simp add: decision_def)
  show "mahler_cf_guard_contains_prefix low_bound high_bound
      (take (length prefix + index) (prefix @ emitted))"
    by (rule mahler_cf_block_prefix_global_earliest(1)[OF old before found selected(1)])
  show "mahler_cf_word (take index emitted) = mahler_cf_word
      (take index (take cap (concat (map (\<lambda>i.
        rev (reflected_trim_high (mahler_cf_pow5_word (n+Suc i)))) [0..<rows]))))"
    using mahler_cf_packed_physical_source[OF source_width] by (simp only: emitted_def)
  fix j assume j: "j < length prefix + index"
  show "\<not> mahler_cf_guard_contains_prefix low_bound high_bound
        (take j (prefix @ emitted))"
    by (rule mahler_cf_block_prefix_global_earliest(2)[OF old before found selected(1) j])
qed

text \<open>An exact source interval admits a common next bit exactly when
one branch carries every point of its half-open cylinder to the safe cell.\<close>

lemma mahler_cf_interval_strict_upper:
  fixes lo hi bound :: real
  assumes nonempty: "lo < hi"
    and below: "\<And>x. lo \<le> x \<Longrightarrow> x < hi \<Longrightarrow> x < bound"
  shows "hi \<le> bound"
proof (rule ccontr)
  assume "\<not> hi \<le> bound"
  then have high: "bound < hi" by simp
  have left: "lo \<le> max lo bound" by simp
  have inside: "max lo bound < hi"
    using nonempty high by (simp add: max_less_iff_conj)
  have "max lo bound < bound" by (rule below[OF left inside])
  then show False by simp
qed

theorem mahler_cf_common_safe_bit_exact:
  fixes lo hi :: real
  assumes nonempty: "lo < hi"
  shows
    "(\<exists>b::nat. b \<le> 1 \<and>
       (\<forall>x. lo \<le> x \<and> x < hi \<longrightarrow>
         0 \<le> x \<and> x < 1/2 \<and>
         0 \<le> (3*x - of_nat b)/2 \<and>
         (3*x - of_nat b)/2 < 1/2)) \<longleftrightarrow>
     (0 \<le> lo \<and> hi \<le> 1/2 \<and> (hi \<le> 1/3 \<or> 1/3 \<le> lo))"
proof
  assume "\<exists>b::nat. b \<le> 1 \<and>
       (\<forall>x. lo \<le> x \<and> x < hi \<longrightarrow>
         0 \<le> x \<and> x < 1/2 \<and>
         0 \<le> (3*x - of_nat b)/2 \<and>
         (3*x - of_nat b)/2 < 1/2)"
  then obtain b :: nat where bit: "b \<le> 1"
    and all: "\<And>x. lo \<le> x \<Longrightarrow> x < hi \<Longrightarrow>
      0 \<le> x \<and> x < 1/2 \<and>
      0 \<le> (3*x - of_nat b)/2 \<and>
      (3*x - of_nat b)/2 < 1/2" by blast
  have lower: "0 \<le> lo" using all[of lo] nonempty by simp
  have upper: "hi \<le> 1/2"
  proof (rule mahler_cf_interval_strict_upper[OF nonempty])
    fix x assume "lo \<le> x" "x < hi"
    then show "x < 1/2" using all[of x] by blast
  qed
  have bits: "b = 0 \<or> b = 1" using bit by arith
  have branch: "hi \<le> 1/3 \<or> 1/3 \<le> lo"
  proof (cases "b = 0")
    case True
    have "hi \<le> 1/3"
    proof (rule mahler_cf_interval_strict_upper[OF nonempty])
      fix x assume inlet: "lo \<le> x" "x < hi"
      have "(3*x - of_nat b)/2 < 1/2" using all[OF inlet] by blast
      then show "x < 1/3" using True by simp
    qed
    then show ?thesis by blast
  next
    case False
    then have "b = 1" using bits by blast
    moreover have "0 \<le> (3*lo - of_nat b)/2"
      using all[of lo] nonempty by simp
    ultimately have "1/3 \<le> lo" by simp
    then show ?thesis by blast
  qed
  show "0 \<le> lo \<and> hi \<le> 1/2 \<and> (hi \<le> 1/3 \<or> 1/3 \<le> lo)"
    using lower upper branch by blast
next
  assume bounds: "0 \<le> lo \<and> hi \<le> 1/2 \<and> (hi \<le> 1/3 \<or> 1/3 \<le> lo)"
  show "\<exists>b::nat. b \<le> 1 \<and>
       (\<forall>x. lo \<le> x \<and> x < hi \<longrightarrow>
         0 \<le> x \<and> x < 1/2 \<and>
         0 \<le> (3*x - of_nat b)/2 \<and>
         (3*x - of_nat b)/2 < 1/2)"
  proof (cases "hi \<le> 1/3")
    case True
    show ?thesis
      by (rule exI[of _ 0]) (use bounds True in \<open>auto; linarith\<close>)
  next
    case False
    have odd: "1/3 \<le> lo" using False bounds by blast
    show ?thesis
      by (rule exI[of _ 1]) (use bounds odd in \<open>auto; linarith\<close>)
  qed
qed

lemma mahler_cf_stalled_affine_excludes_continuation:
  fixes lo hi gain scale innovation :: real and bit :: nat
  defines "F \<equiv> (\<lambda>x. (gain*x - innovation)/scale)"
  assumes gain: "0 < gain" and scale: "0 < scale" and nonempty: "lo < hi"
    and stalled: "\<not> (0 \<le> F lo \<and> F hi \<le> 1/2 \<and>
      (F hi \<le> 1/3 \<or> 1/3 \<le> F lo))"
    and bit: "bit \<le> 1"
    and safe: "\<And>x. lo \<le> x \<Longrightarrow> x < hi \<Longrightarrow>
      0 \<le> F x \<and> F x < 1/2 \<and>
      0 \<le> (3 * F x - of_nat bit)/2 \<and> (3 * F x - of_nat bit)/2 < 1/2"
  shows False
proof -
  have image_order: "F lo < F hi"
    unfolding F_def using mult_strict_left_mono[OF nonempty gain] scale
    by (simp add: divide_less_eq)
  have all: "\<And>y. F lo \<le> y \<Longrightarrow> y < F hi \<Longrightarrow>
      0 \<le> y \<and> y < 1/2 \<and>
      0 \<le> (3*y - of_nat bit)/2 \<and> (3*y - of_nat bit)/2 < 1/2"
  proof -
    fix y assume yl: "F lo \<le> y" and yh: "y < F hi"
    define x where "x = (scale*y + innovation)/gain"
    have yl': "gain*lo - innovation \<le> scale*y"
      using yl scale by (simp add: F_def divide_le_eq mult.commute)
    have yh': "scale*y < gain*hi - innovation"
      using yh scale by (simp add: F_def less_divide_eq mult.commute)
    have lower_bound: "lo*gain \<le> scale*y + innovation" using yl' by (simp add: mult.commute; linarith)
    have upper_bound: "scale*y + innovation < hi*gain" using yh' by (simp add: mult.commute; linarith)
    have lower: "lo \<le> x" using lower_bound gain by (simp add: x_def le_divide_eq)
    have upper: "x < hi" using upper_bound gain by (simp add: x_def divide_less_eq)
    have image: "F x = y"
      using gain scale unfolding F_def x_def
      by simp
    show "0 \<le> y \<and> y < 1/2 \<and>
      0 \<le> (3*y - of_nat bit)/2 \<and> (3*y - of_nat bit)/2 < 1/2"
      using safe[OF lower upper] image by simp
  qed
  have "\<exists>b::nat. b \<le> 1 \<and>
      (\<forall>y. F lo \<le> y \<and> y < F hi \<longrightarrow>
        0 \<le> y \<and> y < 1/2 \<and>
        0 \<le> (3*y - of_nat b)/2 \<and> (3*y - of_nat b)/2 < 1/2)"
    using all bit by blast
  then show False using mahler_cf_common_safe_bit_exact[OF image_order] stalled by blast
qed

theorem mahler_cf_stalled_prefix_not_complete_guard:
  fixes gain scale innovation low_bound high_bound :: real and bit :: nat
  defines "F \<equiv> (\<lambda>x. (gain*x - innovation)/scale)"
  assumes gain: "0 < gain" and scale: "0 < scale"
    and prefix: "mahler_cf_prefix digits = (q,r,p,s)"
    and stalled: "\<not> (0 \<le> F (mahler_cf_low q r p s) \<and>
      F (mahler_cf_high q r p s) \<le> 1/2 \<and>
      (F (mahler_cf_high q r p s) \<le> 1/3 \<or>
       1/3 \<le> F (mahler_cf_low q r p s)))"
    and bit: "bit \<le> 1"
    and continuation: "\<And>x. low_bound \<le> x \<Longrightarrow> x < high_bound \<Longrightarrow>
      0 \<le> F x \<and> F x < 1/2 \<and>
      0 \<le> (3 * F x - of_nat bit)/2 \<and> (3 * F x - of_nat bit)/2 < 1/2"
  shows "\<not> mahler_cf_guard_contains_prefix low_bound high_bound digits"
proof
  assume covered: "mahler_cf_guard_contains_prefix low_bound high_bound digits"
  have bounds: "low_bound \<le> mahler_cf_low q r p s"
    "mahler_cf_high q r p s \<le> high_bound"
    using covered by (simp_all add: mahler_cf_guard_contains_prefix_def prefix)
  have safe: "\<And>x. mahler_cf_low q r p s \<le> x \<Longrightarrow>
      x < mahler_cf_high q r p s \<Longrightarrow>
      0 \<le> F x \<and> F x < 1/2 \<and>
      0 \<le> (3 * F x - of_nat bit)/2 \<and> (3 * F x - of_nat bit)/2 < 1/2"
  proof -
    fix x assume lo: "mahler_cf_low q r p s \<le> x"
      and hi: "x < mahler_cf_high q r p s"
    have lb: "low_bound \<le> x" using lo bounds by linarith
    have ub: "x < high_bound" using hi bounds by linarith
    show "0 \<le> F x \<and> F x < 1/2 \<and>
      0 \<le> (3 * F x - of_nat bit)/2 \<and> (3 * F x - of_nat bit)/2 < 1/2"
      by (rule continuation[OF lb ub])
  qed
  show False
    using mahler_cf_stalled_affine_excludes_continuation[
      where lo="mahler_cf_low q r p s" and hi="mahler_cf_high q r p s"
        and gain=gain and scale=scale and innovation=innovation and bit=bit,
      OF gain scale mahler_cf_prefix_strict[OF prefix]] stalled bit safe
    by (simp add: F_def)
qed

fun mahler_cf_physical_apply :: "nat list \<Rightarrow> real \<Rightarrow> real" where
  "mahler_cf_physical_apply [] x = x"
| "mahler_cf_physical_apply (b#bs) x =
    mahler_cf_physical_apply bs ((3*x-of_nat b)/2)"

definition mahler_cf_safe_fraction :: "real \<Rightarrow> bool" where
  "mahler_cf_safe_fraction x \<longleftrightarrow> 0 \<le> x \<and> x < 1/2"

fun mahler_cf_physical_safe :: "nat list \<Rightarrow> real \<Rightarrow> bool" where
  "mahler_cf_physical_safe [] x = mahler_cf_safe_fraction x"
| "mahler_cf_physical_safe (b#bs) x =
    (b \<le> 1 \<and> mahler_cf_safe_fraction x \<and>
      mahler_cf_physical_safe bs ((3*x-of_nat b)/2))"

lemma mahler_cf_physical_apply_append:
  "mahler_cf_physical_apply (pre @ post) x =
    mahler_cf_physical_apply post (mahler_cf_physical_apply pre x)"
  by (induction pre arbitrary: x) simp_all

lemma mahler_cf_physical_safe_inlet:
  "mahler_cf_physical_safe bs x \<Longrightarrow> mahler_cf_safe_fraction x"
  by (cases bs) simp_all

lemma mahler_cf_physical_safe_append:
  "mahler_cf_physical_safe (pre @ post) x \<longleftrightarrow>
    mahler_cf_physical_safe pre x \<and>
    mahler_cf_physical_safe post (mahler_cf_physical_apply pre x)"
  by (induction pre arbitrary: x) (auto dest: mahler_cf_physical_safe_inlet)

lemma mahler_cf_apply_zero_row:
  "mahler_cf_physical_apply (replicate t 0) x = (3/2)^t*x"
  by (induction t arbitrary: x) (simp_all add: power_Suc algebra_simps)

lemma mahler_cf_safe_zero_row:
  "mahler_cf_physical_safe (replicate t 0) x \<longleftrightarrow>
    mahler_cf_safe_fraction x \<and> mahler_cf_safe_fraction ((3/2)^t*x)"
proof (induction t arbitrary: x)
  case 0
  then show ?case by simp
next
  case (Suc t)
  have factor: "1 \<le> (3/2::real)^t"
    by (rule one_le_power) simp
  have positive: "0 < (3/2::real)^t" by simp
  have power_eq: "(3/2::real)^t * (3*x/2) = (3/2)^(Suc t)*x"
    by (simp add: power_Suc field_simps)
  show ?case
  proof
    assume "mahler_cf_physical_safe (replicate (Suc t) 0) x"
    then show "mahler_cf_safe_fraction x \<and>
      mahler_cf_safe_fraction ((3/2)^Suc t*x)"
      by (simp only: replicate.simps mahler_cf_physical_safe.simps of_nat_0 diff_zero
          zero_le_one Suc.IH power_eq simp_thms)
  next
    assume bounds: "mahler_cf_safe_fraction x \<and>
      mahler_cf_safe_fraction ((3/2)^Suc t*x)"
    have middle_ge: "0 \<le> 3*x/2"
      using bounds by (auto simp: mahler_cf_safe_fraction_def)
    have middle_le: "3*x/2 \<le> (3/2)^Suc t*x"
      unfolding power_eq[symmetric]
      using mult_right_mono[OF factor middle_ge] by simp
    have final_lt: "(3/2)^Suc t*x < 1/2"
      using bounds by (auto simp only: mahler_cf_safe_fraction_def)
    have middle_lt: "3*x/2 < 1/2" by (rule order_le_less_trans[OF middle_le final_lt])
    have middle: "mahler_cf_safe_fraction (3*x/2)"
      using middle_ge middle_lt by (simp only: mahler_cf_safe_fraction_def)
    show "mahler_cf_physical_safe (replicate (Suc t) 0) x"
      using bounds middle by (simp only: replicate.simps mahler_cf_physical_safe.simps of_nat_0 diff_zero
          zero_le_one Suc.IH power_eq simp_thms)
  qed
qed

lemma mahler_cf_safe_odd_even_batch:
  "mahler_cf_physical_safe [1,0] x \<longleftrightarrow>
    mahler_cf_safe_fraction x \<and> mahler_cf_safe_fraction ((9*x-3)/4)"
proof -
  have equation: "3*((3*x-1)/2)/2 = (9*x-3)/4" by (simp add: field_simps)
  have middle:
    "mahler_cf_safe_fraction x \<Longrightarrow> mahler_cf_safe_fraction ((9*x-3)/4)
     \<Longrightarrow> mahler_cf_safe_fraction ((3*x-1)/2)"
    using mahler_cf_lean_odd_pair_bounds[of x]
    by (simp add: mahler_cf_safe_fraction_def; linarith)
  show ?thesis using equation middle by auto
qed

lemma mahler_cf_physical_guard_extend:
  assumes prior: "\<And>x. lo \<le> x \<Longrightarrow> x < hi
      \<Longrightarrow> mahler_cf_physical_safe pre x"
    and terminal: "\<And>x. new_lo \<le> x \<Longrightarrow> x < new_hi
      \<Longrightarrow> mahler_cf_safe_fraction
        (mahler_cf_physical_apply batch (mahler_cf_physical_apply pre x))"
    and nested: "lo \<le> new_lo" "new_hi \<le> hi"
    and batch:
      "\<And>y. mahler_cf_safe_fraction y
      \<Longrightarrow> mahler_cf_safe_fraction (mahler_cf_physical_apply batch y)
      \<Longrightarrow> mahler_cf_physical_safe batch y"
    and x: "new_lo \<le> x" "x < new_hi"
  shows "mahler_cf_physical_safe (pre @ batch) x"
proof -
  have l: "lo \<le> x" using nested x by simp
  have u: "x < hi" using nested x by simp
  have safe: "mahler_cf_physical_safe pre x" by (rule prior[OF l u])
  have final: "mahler_cf_safe_fraction (mahler_cf_physical_apply pre x)"
    using safe
    by (induction pre arbitrary: x) auto
  have "mahler_cf_physical_safe batch (mahler_cf_physical_apply pre x)"
    by (rule batch[OF final terminal[OF x]])
  then show ?thesis using safe by (simp add: mahler_cf_physical_safe_append)
qed

theorem mahler_cf_compiled_guard_has_next_bit:
  assumes later: "suffix \<noteq> []"
    and safe: "\<And>x. low \<le> x \<Longrightarrow> x < high
      \<Longrightarrow> mahler_cf_physical_safe (prefix @ suffix) x"
    and action: "\<And>x. mahler_cf_physical_apply prefix x =
      mahler_cf_lean_fraction gain modulus innovation x"
  shows "\<exists>b::nat. b \<le> 1 \<and>
    (\<forall>x. low \<le> x \<and> x < high \<longrightarrow>
      mahler_cf_safe_fraction (mahler_cf_lean_fraction gain modulus innovation x) \<and>
      mahler_cf_safe_fraction
        ((3*mahler_cf_lean_fraction gain modulus innovation x-of_nat b)/2))"
proof -
  obtain b bs where suffix: "suffix = b # bs"
    using later by (cases suffix) auto
  text \<open>The admissible batch words supply the next bit independently of
  whether the final source guard has any receiving points.\<close>
  show ?thesis
  proof (cases "low < high")
    case True
    have bit: "b \<le> 1"
      using safe[OF order_refl True]
      by (simp add: suffix mahler_cf_physical_safe_append)
    have bounds: "\<And>x. low \<le> x \<Longrightarrow> x < high \<Longrightarrow>
        mahler_cf_safe_fraction (mahler_cf_lean_fraction gain modulus innovation x) \<and>
        mahler_cf_safe_fraction
          ((3*mahler_cf_lean_fraction gain modulus innovation x-of_nat b)/2)"
      using safe
      by (auto simp: suffix mahler_cf_physical_safe_append action
          dest: mahler_cf_physical_safe_inlet)
    show ?thesis using bit bounds by blast
  next
    case False
    show ?thesis by (rule exI[where x=0]) (use False in auto)
  qed
qed

theorem mahler_cf_stalled_prefix_from_safe_continuation:
  fixes gain modulus innovation low high :: real
  defines "F \<equiv> (\<lambda>x. (gain*x - innovation)/modulus)"
  assumes gain: "0 < gain" and modulus: "0 < modulus"
    and prefix: "mahler_cf_prefix digits = (q,r,p,s)"
    and stalled: "\<not> (0 \<le> F (mahler_cf_low q r p s) \<and>
      F (mahler_cf_high q r p s) \<le> 1/2 \<and>
      (F (mahler_cf_high q r p s) \<le> 1/3 \<or>
       1/3 \<le> F (mahler_cf_low q r p s)))"
    and later: "suffix \<noteq> []"
    and safe: "\<And>x. low \<le> x \<Longrightarrow> x < high \<Longrightarrow>
      mahler_cf_physical_safe (pre @ suffix) x"
    and action: "\<And>x. mahler_cf_physical_apply pre x =
      mahler_cf_lean_fraction gain modulus innovation x"
  shows "\<not> mahler_cf_guard_contains_prefix low high digits"
proof -
  obtain b where bit: "b \<le> 1" and safe_bit:
      "\<And>x. low \<le> x \<Longrightarrow> x < high \<Longrightarrow>
        mahler_cf_safe_fraction (mahler_cf_lean_fraction gain modulus innovation x) \<and>
        mahler_cf_safe_fraction
          ((3*mahler_cf_lean_fraction gain modulus innovation x-of_nat b)/2)"
    using mahler_cf_compiled_guard_has_next_bit[OF later safe action] by blast
  have continuation: "\<And>x. low \<le> x \<Longrightarrow> x < high \<Longrightarrow>
      0 \<le> F x \<and> F x < 1/2 \<and>
      0 \<le> (3 * F x - of_nat b)/2 \<and> (3 * F x - of_nat b)/2 < 1/2"
    using safe_bit by (simp add: F_def mahler_cf_lean_fraction_def mahler_cf_safe_fraction_def)
  show ?thesis
    using mahler_cf_stalled_prefix_not_complete_guard[
      where gain=gain and scale=modulus and innovation=innovation and bit=b,
      OF gain modulus prefix] stalled bit continuation
    by (simp add: F_def)
qed
ML \<open>
  val checked = @{thms mahler_cf_ordered_row_block_exact
    mahler_cf_ordered_block_word_split mahler_cf_ordered_block_action_split
    mahler_cf_ordered_block_inside_prefix mahler_cf_ordered_block_inside_prefix_action
    mahler_cf_retained_lower_prefix_action
    mahler_cf_ordered_block_leaf_tile
    mahler_cf_lean_action_composition mahler_cf_lean_zero_run_complete_guard
    mahler_cf_lean_odd_pair_bounds mahler_cf_lean_odd_pair_composition
    mahler_cf_lean_scaled_guard_refinement mahler_cf_packed_lane_exact
    mahler_cf_packed_closed_form mahler_cf_packed_stream_exact
    mahler_cf_packed_capped_source_action mahler_cf_packed_capped_first_guard_prefix
    mahler_cf_block_prefix_global_earliest mahler_cf_packed_physical_source
    mahler_cf_runtime_physical_first_prefix mahler_cf_common_safe_bit_exact
    mahler_cf_physical_guard_extend mahler_cf_stalled_prefix_from_safe_continuation};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Mahler ordered row block depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked
    then error "Skipped Mahler ordered row block proof" else ();
\<close>

end
