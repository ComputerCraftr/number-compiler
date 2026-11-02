theory Double_Reverse_Nibble_Lane_Refinement
  imports Double_Reverse_Packed_Request_Refinement
    Double_Reverse_Spacetime_Carry_Square
begin

unbundle bit_operations_syntax

text \<open>The bounded packed diagonal kernel stores decimal cells in
little-endian nibbles.  Its four bit-sliced outputs are the predicates used
by the existing scalar packed-cell theorem.  This theory verifies those
finite nibble selectors and the shifts which orient center and neighbor
lanes.  It does not issue source authority or replace the causal-window
admission proved by the preceding theories.\<close>

definition double_reverse_nibble_plane_mod_ge_three :: "nat \<Rightarrow> bool" where
  "double_reverse_nibble_plane_mod_ge_three d =
    ((\<not> bit d 3 \<and> \<not> bit d 2 \<and> bit d 1 \<and> bit d 0) \<or>
     (\<not> bit d 3 \<and> bit d 2 \<and> \<not> bit d 1 \<and> \<not> bit d 0) \<or>
     (bit d 3 \<and> \<not> bit d 2 \<and> \<not> bit d 1 \<and> \<not> bit d 0) \<or>
     (bit d 3 \<and> \<not> bit d 2 \<and> \<not> bit d 1 \<and> bit d 0))"

definition double_reverse_nibble_plane_times_four_bit_two :: "nat \<Rightarrow> bool" where
  "double_reverse_nibble_plane_times_four_bit_two d =
    ((\<not> bit d 3 \<and> \<not> bit d 2 \<and> \<not> bit d 1 \<and> bit d 0) \<or>
     (\<not> bit d 3 \<and> bit d 2 \<and> \<not> bit d 1 \<and> \<not> bit d 0) \<or>
     (\<not> bit d 3 \<and> bit d 2 \<and> bit d 1 \<and> \<not> bit d 0) \<or>
     (bit d 3 \<and> \<not> bit d 2 \<and> \<not> bit d 1 \<and> bit d 0))"

definition double_reverse_nibble_plane_mod_equals_two :: "nat \<Rightarrow> bool" where
  "double_reverse_nibble_plane_mod_equals_two d =
    ((\<not> bit d 3 \<and> \<not> bit d 2 \<and> bit d 1 \<and> \<not> bit d 0) \<or>
     (\<not> bit d 3 \<and> bit d 2 \<and> bit d 1 \<and> bit d 0))"

definition double_reverse_nibble_plane_high :: "nat \<Rightarrow> bool" where
  "double_reverse_nibble_plane_high d =
    (bit d 3 \<or> (bit d 2 \<and> (bit d 1 \<or> bit d 0)))"

definition double_reverse_packed_nibble_planes ::
    "int \<Rightarrow> int \<Rightarrow> int \<times> int \<times> int \<times> int" where
  "double_reverse_packed_nibble_planes packed_word lane_mask =
    (let a = packed_word AND lane_mask;
         b = drop_bit 1 packed_word AND lane_mask;
         c = drop_bit 2 packed_word AND lane_mask;
         h = drop_bit 3 packed_word AND lane_mask;
         no_a = NOT a AND lane_mask;
         no_b = NOT b AND lane_mask;
         no_c = NOT c AND lane_mask;
         no_h = NOT h AND lane_mask;
         eq1 = no_h AND no_c AND no_b AND a;
         eq2 = no_h AND no_c AND b AND no_a;
         eq3 = no_h AND no_c AND b AND a;
         eq4 = no_h AND c AND no_b AND no_a;
         eq6 = no_h AND c AND b AND no_a;
         eq7 = no_h AND c AND b AND a;
         eq8 = h AND no_c AND no_b AND no_a;
         eq9 = h AND no_c AND no_b AND a
     in (eq3 OR eq4 OR eq8 OR eq9,
         eq1 OR eq4 OR eq6 OR eq9,
         eq2 OR eq7,
         h OR (c AND (b OR a))))"

definition double_reverse_packed_nibble_value :: "int \<Rightarrow> nat \<Rightarrow> int" where
  "double_reverse_packed_nibble_value packed_word lane_index =
    take_bit 4 (drop_bit (4*lane_index) packed_word)"

fun double_reverse_pack16 :: "nat list \<Rightarrow> nat" where
  "double_reverse_pack16 [] = 0"
| "double_reverse_pack16 (digit # digits) =
    digit + 16 * double_reverse_pack16 digits"

fun double_reverse_pack16_bits :: "bool list \<Rightarrow> int" where
  "double_reverse_pack16_bits [] = 0"
| "double_reverse_pack16_bits (bit_value # bit_values) =
    of_bool bit_value OR push_bit 4 (double_reverse_pack16_bits bit_values)"

lemma double_reverse_pack16_bits_bit:
  "bit (double_reverse_pack16_bits bits) index \<longleftrightarrow>
    index mod 4 = 0 \<and> index div 4 < length bits \<and>
      bits ! (index div 4)"
proof (induction bits arbitrary: index)
  case Nil
  then show ?case by simp
next
  case (Cons bit_value bit_values)
  show ?case
  proof (cases "index < 4")
    case True
    have cases: "index = 0 \<or> index = 1 \<or> index = 2 \<or> index = 3"
      using True by arith
    then show ?thesis
      by (elim disjE; simp add: bit_or_iff bit_push_bit_iff)
  next
    case False
    have tail_exists: "\<exists>tail_index. index = 4 + tail_index"
    proof (rule exI[of _ "index - 4"])
      show "index = 4 + (index - 4)" using False by arith
    qed
    then obtain tail_index where index_eq: "index = 4 + tail_index"
      by auto
    show ?thesis
      unfolding index_eq
      using Cons.IH[of tail_index]
      by (simp add: bit_or_iff bit_push_bit_iff bit_1_iff div_add_self1)
  qed
qed

lemma double_reverse_pack16_bits_eq_pack16:
  "double_reverse_pack16_bits bits =
    int (double_reverse_pack16 (map (\<lambda>b. if b then 1 else 0) bits))"
proof (induction bits)
  case Nil
  then show ?case by simp
next
  case (Cons bit_value bit_values)
  have disjoint:
    "of_bool bit_value AND
       push_bit 4 (double_reverse_pack16_bits bit_values) = 0"
    by (rule bit_eqI) (simp add: bit_simps)
  have head:
    "of_bool bit_value + push_bit 4 (double_reverse_pack16_bits bit_values) =
       of_bool bit_value OR
         push_bit 4 (double_reverse_pack16_bits bit_values)"
    by (rule disjunctive_add_eq_or[OF disjoint])
  have head_rewrite:
    "of_bool bit_value OR push_bit 4 (double_reverse_pack16_bits bit_values) =
       of_bool bit_value + push_bit 4 (double_reverse_pack16_bits bit_values)"
    by (rule sym[OF head])
  show ?case
    using Cons.IH head_rewrite
    by (simp add: push_bit_eq_mult)
qed

lemma double_reverse_pack16_append:
  "double_reverse_pack16 (left @ right) =
    double_reverse_pack16 left +
      16 ^ length left * double_reverse_pack16 right"
  by (induction left) (simp_all add: algebra_simps power_Suc)

lemma double_reverse_pack16_add_no_lane_carry:
  assumes length: "length left = length right"
      and lane_bound:
        "\<forall>i<length left. left ! i + right ! i < 16"
  shows "double_reverse_pack16 (map2 (+) left right) =
      double_reverse_pack16 left + double_reverse_pack16 right"
  using length lane_bound
proof (induction left arbitrary: right)
  case Nil
  then show ?case by simp
next
  case (Cons left_head left_tail)
  then obtain right_head right_tail where
    right: "right = right_head # right_tail"
    by (cases right) auto
  have tail_length: "length left_tail = length right_tail"
    using Cons.prems(1) right by simp
  have tail_bound:
    "\<forall>i<length left_tail. left_tail ! i + right_tail ! i < 16"
    using Cons.prems(2) right by (auto; cases i; auto)
  have tail:
    "double_reverse_pack16 (map2 (+) left_tail right_tail) =
      double_reverse_pack16 left_tail + double_reverse_pack16 right_tail"
    by (rule Cons.IH[OF tail_length tail_bound])
  have head_bound: "left_head + right_head < 16"
    using Cons.prems(2) right by (cases left_tail) auto
  show ?case
    using tail head_bound right
    by (auto simp: algebra_simps)
qed

lemma double_reverse_map2_sub_add_right:
  fixes left right :: "nat list"
  assumes length: "length left = length right"
      and lane_order: "\<forall>i<length left. right ! i \<le> left ! i"
  shows "map2 (+) (map2 (\<lambda>x y. x-y) left right) right = left"
  using length lane_order
proof (induction left arbitrary: right)
  case Nil
  then show ?case by simp
next
  case (Cons left_head left_tail)
  then obtain right_head right_tail where
    right: "right = right_head # right_tail"
    by (cases right) auto
  have tail_length: "length left_tail = length right_tail"
    using Cons.prems(1) right by simp
  have tail_order:
    "\<forall>i<length left_tail. right_tail ! i \<le> left_tail ! i"
    using Cons.prems(2) right by (auto; cases i; auto)
  have tail:
    "map2 (+) (map2 (\<lambda>x y. x-y) left_tail right_tail) right_tail =
      left_tail"
    by (rule Cons.IH[OF tail_length tail_order])
  have head_order: "right_head \<le> left_head"
    using Cons.prems(2) right by (cases left_tail) auto
  have head_recombine: "left_head - right_head + right_head = left_head"
    using head_order by arith
  show ?case
    using head_recombine tail right by simp
qed

lemma double_reverse_pack16_sub_no_lane_borrow:
  assumes length: "length left = length right"
      and lane_order: "\<forall>i<length left. right ! i \<le> left ! i"
      and left_bound: "\<forall>i<length left. left ! i < 16"
  shows "double_reverse_pack16 (map2 (\<lambda>x y. x-y) left right) =
      double_reverse_pack16 left - double_reverse_pack16 right"
proof -
  let ?difference = "map2 (\<lambda>x y. x-y) left right"
  have difference_length: "length ?difference = length left"
    using length by simp
  have difference_right_length: "length ?difference = length right"
    using difference_length length by simp
  have recombine: "map2 (+) ?difference right = left"
    by (rule double_reverse_map2_sub_add_right[OF length lane_order])
  have lane_bound: "\<forall>i<length ?difference. ?difference ! i + right ! i < 16"
  proof (intro allI impI)
    fix i
    assume index: "i < length ?difference"
    have left_index: "i < length left"
      using index difference_length by simp
    have right_index: "i < length right"
      using left_index length by simp
    have zip_index: "i < length (zip ?difference right)"
      using index right_index by simp
    have recombined_index: "map2 (+) ?difference right ! i = left ! i"
      using recombine left_index difference_length length by simp
    have nth_pair:
      "map2 (+) ?difference right ! i = ?difference ! i + right ! i"
      using zip_index index right_index
      by (simp only: nth_map nth_zip split_beta fst_conv snd_conv)
    have sum_index: "?difference ! i + right ! i = left ! i"
      by (rule trans[OF nth_pair[symmetric] recombined_index])
    have left_value_bound: "left ! i < 16"
      using left_bound left_index by blast
    show "?difference ! i + right ! i < 16"
      using sum_index left_value_bound by arith
  qed
  have packed_sum:
    "double_reverse_pack16 (map2 (+) ?difference right) =
      double_reverse_pack16 ?difference + double_reverse_pack16 right"
    by (rule double_reverse_pack16_add_no_lane_carry[
      OF difference_right_length lane_bound])
  have packed_equation:
    "double_reverse_pack16 left =
      double_reverse_pack16 ?difference + double_reverse_pack16 right"
    using packed_sum recombine by simp
  show ?thesis
    using packed_equation by arith
qed

lemma double_reverse_pack16_replicate_one_power_identity:
  "15 * double_reverse_pack16 (replicate width 1) + 1 = 2^(4*width)"
proof (induction width)
  case "0"
  then show ?case by simp
next
  case (Suc width)
  have exponent: "4 * Suc width = 4 * width + 4"
    by simp
  show ?case
    using Suc.IH
    by (simp add: exponent power_add algebra_simps; arith)
qed

lemma double_reverse_pack16_replicate_one_numerator:
  "15 * double_reverse_pack16 (replicate width 1) = 2^(4*width) - 1"
proof -
  have identity: "15 * double_reverse_pack16 (replicate width 1) + 1 =
      2^(4*width)"
    by (rule double_reverse_pack16_replicate_one_power_identity)
  show ?thesis using identity by arith
qed

lemma double_reverse_pack16_replicate_one_mask:
  "double_reverse_pack16 (replicate width 1) =
    (2^(4*width) - 1) div 15"
proof -
  have numerator: "15 * double_reverse_pack16 (replicate width 1) =
      2^(4*width) - 1"
    by (rule double_reverse_pack16_replicate_one_numerator)
  show ?thesis
    using numerator by (simp add: div_mult_self1 mult.commute)
qed

lemma double_reverse_pack16_replicate_one_support:
  "bit (int (double_reverse_pack16 (replicate width 1))) index \<longleftrightarrow>
    index mod 4 = 0 \<and> index div 4 < width"
proof -
  have packed:
    "int (double_reverse_pack16 (replicate width 1)) =
      double_reverse_pack16_bits (replicate width True)"
    using double_reverse_pack16_bits_eq_pack16[of "replicate width True"]
    by simp
  show ?thesis
    using packed
    by (auto simp: double_reverse_pack16_bits_bit)
qed

lemma double_reverse_pack16_reverse_source_order:
  "double_reverse_pack16 (rev digits) =
    foldl (\<lambda>packed digit. 16*packed + digit) 0 digits"
proof -
  let ?append = "\<lambda>(packed::nat) (digit::nat). 16*packed + digit"
  have fold_accumulator:
    "foldl ?append accumulator digits =
      16 ^ length digits * accumulator + foldl ?append 0 digits"
    for accumulator :: nat and digits :: "nat list"
  proof (induction digits arbitrary: accumulator)
    case Nil
    then show ?case by simp
  next
    case (Cons digit digits)
    have tail_accumulator:
      "foldl ?append (16*accumulator + digit) digits =
        16 ^ length digits * (16*accumulator + digit) +
          foldl ?append 0 digits"
      by (rule Cons.IH)
    have tail_digit:
      "foldl ?append digit digits =
        16 ^ length digits * digit + foldl ?append 0 digits"
      by (rule Cons.IH)
    have step:
      "foldl ?append accumulator (digit # digits) =
        foldl ?append (16*accumulator + digit) digits"
      by simp
    also have "... =
        16 ^ length digits * (16*accumulator + digit) +
          foldl ?append 0 digits"
      by (rule tail_accumulator)
    also have "... =
        16 ^ Suc (length digits) * accumulator +
          foldl ?append 0 (digit # digits)"
      using tail_digit by (simp add: power_Suc algebra_simps)
    finally show ?case by simp
  qed
  show ?thesis
proof (induction digits)
  case Nil
  then show ?case by simp
next
  case (Cons digit digits)
  have packed_append:
    "double_reverse_pack16 (rev (digit # digits)) =
      double_reverse_pack16 (rev digits) +
        16 ^ length digits * digit"
    using double_reverse_pack16_append[of "rev digits" "[digit]"] by simp
  have fold_cons:
    "foldl ?append 0 (digit # digits) =
      16 ^ length digits * digit + foldl ?append 0 digits"
    using fold_accumulator[of digit digits] by simp
  show ?case
    using Cons.IH packed_append fold_cons by (simp add: algebra_simps)
qed
qed

lemma double_reverse_pack16_head_extract:
  assumes digit: "digit < 16"
  shows "take_bit 4 (int digit + 16 * int rest) = int digit"
    and "drop_bit 4 (int digit + 16 * int rest) = int rest"
proof -
  have digit_bounds: "0 \<le> int digit \<and> int digit < 16"
    using digit by simp
  have digit_quotient: "int digit div 16 = 0"
    using digit_bounds by (simp add: zdiv_eq_0_iff)
  have digit_remainder:
    "(int digit + 16 * int rest) mod 16 = int digit"
    using digit by presburger
  have total_quotient:
    "(int digit + 16 * int rest) div 16 = int rest"
    using digit_quotient by simp
  show "take_bit 4 (int digit + 16 * int rest) = int digit"
    using digit_remainder by (simp add: take_bit_eq_mod)
  show "drop_bit 4 (int digit + 16 * int rest) = int rest"
    using total_quotient by (simp add: drop_bit_eq_div)
qed

lemma double_reverse_pack16_nibble_value:
  assumes bounded: "\<forall>digit\<in>set digits. digit < 16"
      and index: "lane_index < length digits"
  shows "double_reverse_packed_nibble_value
      (int (double_reverse_pack16 digits)) lane_index = int (digits ! lane_index)"
  using bounded index
proof (induction lane_index arbitrary: digits)
  case "0"
  then obtain digit rest where digits: "digits = digit # rest"
    by (cases digits) auto
  have digit_bound: "digit < 16"
    using "0.prems"(1) unfolding digits by simp
  show ?case
    unfolding digits
    using double_reverse_pack16_head_extract(1)[of digit
        "double_reverse_pack16 rest", OF digit_bound]
    by (simp add: double_reverse_packed_nibble_value_def)
next
  case (Suc lane_index)
  then obtain digit rest where digits: "digits = digit # rest"
    by (cases digits) auto
  have digit_bound: "digit < 16"
    using Suc.prems(1) unfolding digits by simp
  have rest_bounded: "\<forall>digit\<in>set rest. digit < 16"
    using Suc.prems(1) unfolding digits by auto
  have rest_index: "lane_index < length rest"
    using Suc.prems(2) unfolding digits by simp
  have drop_head:
    "drop_bit 4 (int (double_reverse_pack16 (digit # rest))) =
      int (double_reverse_pack16 rest)"
    using double_reverse_pack16_head_extract(2)[of digit
        "double_reverse_pack16 rest", OF digit_bound]
    by simp
  have tail:
    "double_reverse_packed_nibble_value
       (int (double_reverse_pack16 rest)) lane_index = int (rest ! lane_index)"
    by (rule Suc.IH[OF rest_bounded rest_index])
  let ?packed = "int (double_reverse_pack16 (digit # rest))"
  have composed_drop:
    "drop_bit (4 * lane_index) (drop_bit 4 ?packed) =
      drop_bit (4 * lane_index + 4) ?packed"
    by (simp only: drop_bit_drop_bit)
  have shift_amount: "4 * Suc lane_index = 4 * lane_index + 4"
    by arith
  have shifted_drop:
    "drop_bit (4 * Suc lane_index) ?packed =
      drop_bit (4 * lane_index) (drop_bit 4 ?packed)"
    using composed_drop shift_amount by (simp add: add.commute)
  have drop_tail:
    "drop_bit (4 * lane_index) (drop_bit 4 ?packed) =
      drop_bit (4 * lane_index) (int (double_reverse_pack16 rest))"
    using drop_head by (rule arg_cong)
  have tail_value:
    "take_bit 4 (drop_bit (4 * lane_index)
       (int (double_reverse_pack16 rest))) = int (rest ! lane_index)"
    using tail unfolding double_reverse_packed_nibble_value_def .
  have result:
    "take_bit 4 (drop_bit (4 * Suc lane_index) ?packed) =
       int (rest ! lane_index)"
    using shifted_drop drop_tail tail_value by simp
  show ?case
    using result
    unfolding digits double_reverse_packed_nibble_value_def
    by simp
qed

lemma double_reverse_packed_nibble_value_bit:
  assumes digit_index_bound: "j < 4"
  shows "bit (double_reverse_packed_nibble_value packed_word lane_index) j =
    bit packed_word (4*lane_index+j)"
  using digit_index_bound
  by (simp add: double_reverse_packed_nibble_value_def
      bit_take_bit_iff bit_drop_bit_eq algebra_simps)

lemma double_reverse_packed_nibble_planes_lane_exact:
  assumes lane: "bit lane_mask (4*i)"
      and digit: "double_reverse_packed_nibble_value packed_word i = int d"
      and decimal: "d < 10"
  shows "bit (fst (double_reverse_packed_nibble_planes packed_word lane_mask)) (4*i) \<longleftrightarrow>
           double_reverse_nibble_plane_mod_ge_three d"
    and "bit (fst (snd (double_reverse_packed_nibble_planes packed_word lane_mask))) (4*i) \<longleftrightarrow>
           double_reverse_nibble_plane_times_four_bit_two d"
    and "bit (fst (snd (snd (double_reverse_packed_nibble_planes packed_word lane_mask)))) (4*i) \<longleftrightarrow>
           double_reverse_nibble_plane_mod_equals_two d"
    and "bit (snd (snd (snd (double_reverse_packed_nibble_planes packed_word lane_mask)))) (4*i) \<longleftrightarrow>
           double_reverse_nibble_plane_high d"
proof -
  have source_bit: "bit packed_word (4*i+j) = bit d j"
    if bit_index: "j < 4" for j
  proof -
    have nibble_bit:
      "bit (double_reverse_packed_nibble_value packed_word i) j = bit d j"
      using digit bit_index by (simp add: bit_of_nat_iff_bit)
    have packed_bit:
      "bit (double_reverse_packed_nibble_value packed_word i) j =
        bit packed_word (4*i+j)"
      by (rule double_reverse_packed_nibble_value_bit[OF bit_index])
    show ?thesis using nibble_bit packed_bit by simp
  qed
  have source0: "bit packed_word (4*i) = bit d 0"
    using source_bit[of 0] by simp
  have source1: "bit packed_word (4*i+1) = bit d 1"
    using source_bit[of 1] by simp
  have source2: "bit packed_word (4*i+2) = bit d 2"
    using source_bit[of 2] by simp
  have source3: "bit packed_word (4*i+3) = bit d 3"
    using source_bit[of 3] by simp
  have input0: "bit (packed_word AND lane_mask) (4*i) = bit d 0"
    using lane source0 by (simp add: bit_and_iff)
  have input1: "bit (drop_bit 1 packed_word AND lane_mask) (4*i) = bit d 1"
    using lane source1 by (simp add: bit_and_iff bit_drop_bit_eq add.commute)
  have input2: "bit (drop_bit 2 packed_word AND lane_mask) (4*i) = bit d 2"
    using lane source2 by (simp add: bit_and_iff bit_drop_bit_eq add.commute)
  have input3: "bit (drop_bit 3 packed_word AND lane_mask) (4*i) = bit d 3"
    using lane source3 by (simp add: bit_and_iff bit_drop_bit_eq add.commute)
  show "bit (fst (double_reverse_packed_nibble_planes packed_word lane_mask)) (4*i) \<longleftrightarrow>
      double_reverse_nibble_plane_mod_ge_three d"
    and "bit (fst (snd (double_reverse_packed_nibble_planes packed_word lane_mask))) (4*i) \<longleftrightarrow>
      double_reverse_nibble_plane_times_four_bit_two d"
    and "bit (fst (snd (snd (double_reverse_packed_nibble_planes packed_word lane_mask)))) (4*i) \<longleftrightarrow>
      double_reverse_nibble_plane_mod_equals_two d"
    and "bit (snd (snd (snd (double_reverse_packed_nibble_planes packed_word lane_mask)))) (4*i) \<longleftrightarrow>
      double_reverse_nibble_plane_high d"
    using lane input0 input1 input2 input3 decimal
    unfolding double_reverse_packed_nibble_planes_def
      double_reverse_nibble_plane_mod_ge_three_def
      double_reverse_nibble_plane_times_four_bit_two_def
      double_reverse_nibble_plane_mod_equals_two_def
      double_reverse_nibble_plane_high_def
    by (simp_all add: Let_def fst_conv snd_conv bit_simps bit_not_int_iff)
qed

lemma double_reverse_nibble_planes_exact:
  assumes digit: "d < 10"
  shows "double_reverse_nibble_plane_mod_ge_three d \<longleftrightarrow>
           (d mod 5 = 3 \<or> d mod 5 = 4)"
    and "double_reverse_nibble_plane_times_four_bit_two d \<longleftrightarrow>
           bit ((4*d) mod 10) 2"
    and "double_reverse_nibble_plane_mod_equals_two d \<longleftrightarrow>
           d mod 5 = 2"
    and "double_reverse_nibble_plane_high d \<longleftrightarrow> 5 \<le> d"
proof -
  have cases: "d = 0 \<or> d = 1 \<or> d = 2 \<or> d = 3 \<or> d = 4 \<or>
      d = 5 \<or> d = 6 \<or> d = 7 \<or> d = 8 \<or> d = 9"
    using digit by arith
  show "double_reverse_nibble_plane_mod_ge_three d \<longleftrightarrow>
      (d mod 5 = 3 \<or> d mod 5 = 4)"
    using cases
    by (elim disjE; simp add: double_reverse_nibble_plane_mod_ge_three_def
        bit_simps)
  show "double_reverse_nibble_plane_times_four_bit_two d \<longleftrightarrow>
      bit ((4*d) mod 10) 2"
    using cases
    by (elim disjE; simp add: double_reverse_nibble_plane_times_four_bit_two_def
        bit_simps)
  show "double_reverse_nibble_plane_mod_equals_two d \<longleftrightarrow>
      d mod 5 = 2"
    using cases
    by (elim disjE; simp add: double_reverse_nibble_plane_mod_equals_two_def
        bit_simps)
  show "double_reverse_nibble_plane_high d \<longleftrightarrow> 5 \<le> d"
    using cases
    by (elim disjE; simp add: double_reverse_nibble_plane_high_def bit_simps)
qed

definition double_reverse_nibble_base :: "nat \<Rightarrow> nat" where
  "double_reverse_nibble_base d =
    2 * (if double_reverse_nibble_plane_mod_ge_three d then 1 else 0) +
    4 * (if double_reverse_nibble_plane_times_four_bit_two d then 1 else 0) +
    8 * (if double_reverse_nibble_plane_mod_equals_two d then 1 else 0)"

lemma double_reverse_nibble_base_exact:
  assumes digit: "d < 10"
  shows "double_reverse_nibble_base d = (4 * (d mod 5)) mod 10"
proof -
  have digit_cases:
    "d = 0 \<or> d = 1 \<or> d = 2 \<or> d = 3 \<or> d = 4 \<or>
     d = 5 \<or> d = 6 \<or> d = 7 \<or> d = 8 \<or> d = 9"
    using digit by arith
  show ?thesis
    using digit_cases
    by (elim disjE; simp add: double_reverse_nibble_base_def
      double_reverse_nibble_plane_mod_ge_three_def
      double_reverse_nibble_plane_times_four_bit_two_def
      double_reverse_nibble_plane_mod_equals_two_def
      bit_simps bit_Suc_0_iff)
qed

definition double_reverse_nibble_lane_result ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "double_reverse_nibble_lane_result left center right =
    (let left_high = (if double_reverse_nibble_plane_high left then 1 else 0);
         center_high = double_reverse_nibble_plane_high center;
         right_carry =
           (double_reverse_nibble_plane_mod_ge_three right \<or>
            (double_reverse_nibble_plane_mod_equals_two right \<and> center_high));
         base = double_reverse_nibble_base center;
         candidate = base + 2*left_high + (if right_carry then 1 else 0);
         overflow = double_reverse_nibble_plane_mod_equals_two center \<and>
           double_reverse_nibble_plane_high left
     in candidate - (if overflow then 10 else 0))"

lemma double_reverse_nibble_candidate_reduction:
  fixes residue left_carry right_carry :: nat
  assumes residue: "residue < 5"
      and left: "left_carry < 2"
      and right: "right_carry < 2"
  shows "(4*residue mod 10 + 2*left_carry + right_carry) -
      (if residue = 2 \<and> left_carry = 1 then 10 else 0) =
    (4*residue + 2*left_carry + right_carry) mod 10"
proof -
  have residue_cases: "residue = 0 \<or> residue = 1 \<or> residue = 2 \<or>
      residue = 3 \<or> residue = 4"
    using residue by arith
  have left_cases: "left_carry = 0 \<or> left_carry = 1"
    using left by arith
  have right_cases: "right_carry = 0 \<or> right_carry = 1"
    using right by arith
  show ?thesis
    using residue_cases left_cases right_cases
    by (elim disjE; simp)
qed

lemma double_reverse_nibble_lane_result_refines_cell:
  assumes digits: "left < 10" "center < 10" "right < 10"
  shows "double_reverse_nibble_lane_result left center right =
    double_reverse_packed_t2_cell left center right"
proof -
  have left_high:
    "double_reverse_nibble_plane_high left \<longleftrightarrow> 5 \<le> left"
    by (rule double_reverse_nibble_planes_exact(4)[OF digits(1)])
  have center_high:
    "double_reverse_nibble_plane_high center \<longleftrightarrow> 5 \<le> center"
    by (rule double_reverse_nibble_planes_exact(4)[OF digits(2)])
  have right_ge_three:
    "double_reverse_nibble_plane_mod_ge_three right \<longleftrightarrow>
      (right mod 5 = 3 \<or> right mod 5 = 4)"
    by (rule double_reverse_nibble_planes_exact(1)[OF digits(3)])
  have right_eq_two:
    "double_reverse_nibble_plane_mod_equals_two right \<longleftrightarrow>
      right mod 5 = 2"
    by (rule double_reverse_nibble_planes_exact(3)[OF digits(3)])
  have center_eq_two:
    "double_reverse_nibble_plane_mod_equals_two center \<longleftrightarrow>
      center mod 5 = 2"
    by (rule double_reverse_nibble_planes_exact(3)[OF digits(2)])
  have base:
    "double_reverse_nibble_base center =
      (4*(center mod 5)) mod 10"
    by (rule double_reverse_nibble_base_exact[OF digits(2)])
  let ?left = "if 5 \<le> left then (1::nat) else 0"
  let ?right = "(if right mod 5 = 3 \<or> right mod 5 = 4 then (1::nat) else 0) +
    (if 5 \<le> center \<and> right mod 5 = 2 then (1::nat) else 0)"
  have left_bound: "?left < 2" by simp
  have right_bound: "?right < 2"
    using right_ge_three right_eq_two by auto
  have right_disjoint:
    "\<not> ((right mod 5 = 3 \<or> right mod 5 = 4) \<and>
       right mod 5 = 2)"
    by presburger
  have right_value:
    "(if double_reverse_nibble_plane_mod_ge_three right \<or>
         (double_reverse_nibble_plane_mod_equals_two right \<and>
           double_reverse_nibble_plane_high center)
     then 1 else 0) = ?right"
    using right_ge_three right_eq_two center_high
  proof (cases "right mod 5 = 3 \<or> right mod 5 = 4")
    case True
    have not_two: "right mod 5 \<noteq> 2"
      using right_disjoint True by blast
    show ?thesis
      using right_ge_three right_eq_two center_high True not_two by simp
  next
    case False
    show ?thesis
      using right_ge_three right_eq_two center_high False by simp
  qed
  have overflow:
    "(if double_reverse_nibble_plane_mod_equals_two center \<and>
         double_reverse_nibble_plane_high left
     then 10 else 0) =
       (if center mod 5 = 2 \<and> 5 \<le> left then 10 else 0)"
    using center_eq_two left_high by simp
  have reduction:
    "(4*(center mod 5) mod 10 + 2*?left + ?right) -
       (if center mod 5 = 2 \<and> ?left = 1 then 10 else 0) =
      (4*(center mod 5) + 2*?left + ?right) mod 10"
    by (rule double_reverse_nibble_candidate_reduction)
      (use left_bound right_bound in simp_all)
  have indicator_one: "?left = 1 \<longleftrightarrow> 5 \<le> left"
    by simp
  have overflow_guard:
    "(double_reverse_nibble_plane_mod_equals_two center \<and>      double_reverse_nibble_plane_high left) \<longleftrightarrow>      (center mod 5 = 2 \<and> ?left = 1)"
    using center_eq_two left_high indicator_one by simp
  have lane_candidate:
    "double_reverse_nibble_lane_result left center right =
      (4*(center mod 5) mod 10 + 2*?left + ?right) -
        (if center mod 5 = 2 \<and> ?left = 1 then 10 else 0)"
    unfolding double_reverse_nibble_lane_result_def
    using base left_high center_eq_two right_value overflow overflow_guard
    by (simp add: Let_def)
  have lane_reduced:
    "double_reverse_nibble_lane_result left center right =
      (4*(center mod 5) + 2*?left + ?right) mod 10"
    using lane_candidate reduction by simp
  have cell_exact:
    "double_reverse_packed_t2_cell left center right =
      (4*(center mod 5) + 2*?left + ?right) mod 10"
    unfolding double_reverse_packed_t2_cell_def
    by (simp add: add.assoc)
  show ?thesis using lane_reduced cell_exact by simp
qed

lemma double_reverse_nibble_candidate_bounds:
  assumes digits: "left < 10" "center < 10" "right < 10"
  shows
    "double_reverse_nibble_base center +
       2 * (if double_reverse_nibble_plane_high left then 1 else 0) +
       (if double_reverse_nibble_plane_mod_ge_three right \<or>
          (double_reverse_nibble_plane_mod_equals_two right \<and>
            double_reverse_nibble_plane_high center) then 1 else 0) < 16 \<and>
     (if double_reverse_nibble_plane_mod_equals_two center \<and>
          double_reverse_nibble_plane_high left then 10 else 0) \<le>
       double_reverse_nibble_base center +
       2 * (if double_reverse_nibble_plane_high left then 1 else 0) +
       (if double_reverse_nibble_plane_mod_ge_three right \<or>
          (double_reverse_nibble_plane_mod_equals_two right \<and>
            double_reverse_nibble_plane_high center) then 1 else 0)"
proof -
  let ?base = "double_reverse_nibble_base center"
  let ?left_bit = "if double_reverse_nibble_plane_high left then (1::nat) else 0"
  let ?right_bit =
    "if double_reverse_nibble_plane_mod_ge_three right \<or>
        (double_reverse_nibble_plane_mod_equals_two right \<and>
          double_reverse_nibble_plane_high center) then (1::nat) else 0"
  let ?overflow =
    "double_reverse_nibble_plane_mod_equals_two center \<and>
      double_reverse_nibble_plane_high left"
  have base_exact:
    "?base = (4*(center mod 5)) mod 10"
    by (simp add: double_reverse_nibble_base_exact[OF digits(2)])
  have residue_cases:
    "center mod 5 = 0 \<or> center mod 5 = 1 \<or> center mod 5 = 2 \<or>
     center mod 5 = 3 \<or> center mod 5 = 4"
    by arith
  have base_bound: "?base \<le> 8"
    using base_exact residue_cases by (elim disjE; simp)
  have left_bound: "?left_bit \<le> 1"
    by simp
  have right_bound: "?right_bit \<le> 1"
    by (simp add: Let_def)
  have candidate_bound: "?base + 2*?left_bit + ?right_bit \<le> 11"
    using base_bound left_bound right_bound by arith
  have candidate_lower: "?overflow \<Longrightarrow> 10 \<le> ?base + 2*?left_bit + ?right_bit"
  proof -
    assume overflow: ?overflow
    have center_predicate:
      "double_reverse_nibble_plane_mod_equals_two center"
      using overflow by simp
    have residue_two: "center mod 5 = 2"
      using double_reverse_nibble_planes_exact(3)[OF digits(2)]
        center_predicate by blast
    have left_predicate:
      "double_reverse_nibble_plane_high left"
      using overflow by simp
    have left_high: "5 \<le> left"
      using double_reverse_nibble_planes_exact(4)[OF digits(1)]
        left_predicate by blast
    have base_eight: "?base = 8"
      using base_exact residue_two by simp
    have left_one: "?left_bit = 1"
      using left_high by (simp add: double_reverse_nibble_planes_exact(4)[OF digits(1)])
    show "10 \<le> ?base + 2*?left_bit + ?right_bit"
      using base_eight left_one right_bound by arith
  qed
  show ?thesis
    using candidate_bound candidate_lower by auto
qed

text \<open>A packed little-endian lane at index i is source cell i.  Shifting
one nibble selects i+1; shifting two selects i+2.  The mask hypothesis is
exactly the lane support condition supplied by the bounded packed loop.\<close>

lemma double_reverse_nibble_shifted_lane:
  fixes plane lanes :: int
  assumes lane: "bit lanes (4*i)"
  shows "bit (drop_bit 4 plane AND lanes) (4*i) \<longleftrightarrow>
           bit plane (4*(i+1))"
    and "bit (drop_bit 8 plane AND lanes) (4*i) \<longleftrightarrow>
           bit plane (4*(i+2))"
    and "bit (plane AND lanes) (4*i) \<longleftrightarrow> bit plane (4*i)"
  using lane
  by (simp_all add: bit_and_iff bit_drop_bit_eq algebra_simps)

lemma double_reverse_nibble_shifted_lane_from_support:
  fixes plane full_lanes :: int
  assumes source_lane: "bit full_lanes (4*(i+2))"
  defines "lanes \<equiv> drop_bit 8 full_lanes"
  shows "bit (drop_bit 4 plane AND lanes) (4*i) \<longleftrightarrow>
           bit plane (4*(i+1))"
    and "bit (drop_bit 8 plane AND lanes) (4*i) \<longleftrightarrow>
           bit plane (4*(i+2))"
    and "bit (plane AND lanes) (4*i) \<longleftrightarrow> bit plane (4*i)"
  using source_lane
  unfolding lanes_def
  by (simp_all add: bit_and_iff bit_drop_bit_eq algebra_simps)

definition double_reverse_nibble_row_step :: "nat list \<Rightarrow> nat list" where
  "double_reverse_nibble_row_step row =
    map (\<lambda>i. double_reverse_nibble_lane_result
      (row ! i) (row ! (i+1)) (row ! (i+2))) [0..<length row - 2]"

lemma double_reverse_nibble_row_step_length:
  "length (double_reverse_nibble_row_step row) = length row - 2"
  by (simp add: double_reverse_nibble_row_step_def)

lemma double_reverse_nibble_row_step_refines_packed:
  assumes decimal: "double_reverse_decimal_row row"
  shows "double_reverse_nibble_row_step row =
    double_reverse_packed_row_step row"
proof (rule nth_equalityI)
  show "length (double_reverse_nibble_row_step row) =
      length (double_reverse_packed_row_step row)"
    by (simp add: double_reverse_nibble_row_step_length
        double_reverse_packed_row_step_length)
next
  fix i
  assume index: "i < length (double_reverse_nibble_row_step row)"
  have index': "i < length row - 2"
    using index by (simp add: double_reverse_nibble_row_step_length)
  have left_bound: "row ! i < 10"
    using decimal index' unfolding double_reverse_decimal_row_def by auto
  have center_bound: "row ! (i+1) < 10"
    using decimal index' unfolding double_reverse_decimal_row_def by auto
  have right_bound: "row ! (i+2) < 10"
    using decimal index' unfolding double_reverse_decimal_row_def by auto
  have cell:
    "double_reverse_nibble_lane_result (row ! i) (row ! (i+1)) (row ! (i+2)) =
      double_reverse_packed_t2_cell (row ! i) (row ! (i+1)) (row ! (i+2))"
    by (rule double_reverse_nibble_lane_result_refines_cell[
        OF left_bound center_bound right_bound])
  show "double_reverse_nibble_row_step row ! i =
      double_reverse_packed_row_step row ! i"
    using cell index'
    by (simp add: double_reverse_nibble_row_step_def
        double_reverse_packed_row_step_cell)
qed

lemma double_reverse_packed_row_step_refines_spacetime:
  assumes decimal: "double_reverse_decimal_row row"
  shows "double_reverse_packed_row_step row =
    double_reverse_spacetime_step row"
proof (rule nth_equalityI)
  show "length (double_reverse_packed_row_step row) =
      length (double_reverse_spacetime_step row)"
    by (simp add: double_reverse_packed_row_step_length
        double_reverse_spacetime_step_length)
next
  fix i
  assume index: "i < length (double_reverse_packed_row_step row)"
  have index': "i < length row - 2"
    using index by (simp add: double_reverse_packed_row_step_length)
  have left_bound: "row ! i < 10"
    using decimal index' unfolding double_reverse_decimal_row_def by auto
  have center_bound: "row ! (i+1) < 10"
    using decimal index' unfolding double_reverse_decimal_row_def by auto
  have right_bound: "row ! (i+2) < 10"
    using decimal index' unfolding double_reverse_decimal_row_def by auto
  have cell:
    "double_reverse_packed_t2_cell (row ! i) (row ! (i+1)) (row ! (i+2)) =
      double_reverse_t2_digit (row ! i) (row ! (i+1)) (row ! (i+2))"
    by (rule double_reverse_packed_t2_cell_refines_stencil[
        OF left_bound center_bound right_bound])
  show "double_reverse_packed_row_step row ! i =
      double_reverse_spacetime_step row ! i"
    using cell index'
    by (simp add: double_reverse_packed_row_step_cell
        double_reverse_spacetime_step_cell)
qed

lemma double_reverse_spacetime_power_preserves_decimal:
  assumes decimal: "double_reverse_decimal_row row"
  shows "double_reverse_decimal_row
    (double_reverse_spacetime_power steps row)"
  using decimal
proof (induction steps arbitrary: row)
  case "0"
  then show ?case by simp
next
  case (Suc steps)
  have next_decimal:
    "double_reverse_decimal_row
      (double_reverse_spacetime_step
        (double_reverse_spacetime_power steps row))"
  proof -
    show ?thesis
      unfolding double_reverse_decimal_row_def
    proof (intro allI impI)
      fix i
      assume index: "i < length
        (double_reverse_spacetime_step
          (double_reverse_spacetime_power steps row))"
      then have index': "i < length
        (double_reverse_spacetime_power steps row) - 2"
        by (simp add: double_reverse_spacetime_step_length)
      have extent: "i+2 < length
        (double_reverse_spacetime_power steps row)"
        using index' by arith
      have cell:
        "double_reverse_spacetime_step
            (double_reverse_spacetime_power steps row) ! i =
          double_reverse_t2_digit
            (double_reverse_spacetime_power steps row ! i)
            (double_reverse_spacetime_power steps row ! (i+1))
            (double_reverse_spacetime_power steps row ! (i+2))"
        by (rule double_reverse_spacetime_step_cell[OF extent])
      show "double_reverse_spacetime_step
          (double_reverse_spacetime_power steps row) ! i < 10"
        unfolding cell
        by (rule double_reverse_t2_output_bounded)
    qed
  qed
  show ?case
    using next_decimal
    by (simp only: double_reverse_spacetime_power.simps)
qed

lemma double_reverse_nibble_row_step_refines_spacetime:
  assumes decimal: "double_reverse_decimal_row row"
  shows "double_reverse_nibble_row_step row =
    double_reverse_spacetime_step row"
  using double_reverse_nibble_row_step_refines_packed[OF decimal]
    double_reverse_packed_row_step_refines_spacetime[OF decimal]
  by simp

fun double_reverse_nibble_row_power :: "nat \<Rightarrow> nat list \<Rightarrow> nat list" where
  "double_reverse_nibble_row_power 0 row = row"
| "double_reverse_nibble_row_power (Suc steps) row =
    double_reverse_nibble_row_step
      (double_reverse_nibble_row_power steps row)"

lemma double_reverse_nibble_row_power_refines_spacetime:
  assumes decimal: "double_reverse_decimal_row row"
  shows "double_reverse_nibble_row_power steps row =
    double_reverse_spacetime_power steps row"
  using decimal
proof (induction steps arbitrary: row)
  case "0"
  then show ?case by simp
next
  case (Suc steps)
  have prior_decimal:
    "double_reverse_decimal_row
      (double_reverse_spacetime_power steps row)"
    by (rule double_reverse_spacetime_power_preserves_decimal[OF Suc.prems])
  have prior:
    "double_reverse_nibble_row_power steps row =
      double_reverse_spacetime_power steps row"
    by (rule Suc.IH[OF Suc.prems])
  show ?case
    using prior prior_decimal
    by (simp add: double_reverse_nibble_row_step_refines_spacetime)
qed

corollary double_reverse_nibble_row_power_exact_window:
  assumes decimal: "double_reverse_decimal_row row"
      and extent: "start + window_width + 2*steps \<le> length source"
      and local: "row = take (window_width + 2*steps) (drop start source)"
  shows "double_reverse_nibble_row_power steps row =
    take window_width (drop start
      (double_reverse_spacetime_power steps source))"
  using double_reverse_nibble_row_power_refines_spacetime[OF decimal]
    double_reverse_spacetime_window_power[OF extent] local
  by simp

ML \<open>
  val checked = @{thms double_reverse_pack16_append
    double_reverse_pack16_add_no_lane_carry
    double_reverse_map2_sub_add_right
    double_reverse_pack16_sub_no_lane_borrow
    double_reverse_pack16_replicate_one_power_identity
    double_reverse_pack16_replicate_one_numerator
    double_reverse_pack16_replicate_one_mask
    double_reverse_pack16_replicate_one_support
    double_reverse_pack16_reverse_source_order
    double_reverse_pack16_nibble_value
    double_reverse_pack16_bits_bit
    double_reverse_pack16_bits_eq_pack16
    double_reverse_nibble_planes_exact
    double_reverse_packed_nibble_value_bit
    double_reverse_packed_nibble_planes_lane_exact
    double_reverse_nibble_base_exact
    double_reverse_nibble_lane_result_refines_cell
    double_reverse_nibble_candidate_bounds
    double_reverse_nibble_shifted_lane
    double_reverse_nibble_shifted_lane_from_support
    double_reverse_nibble_row_step_refines_packed
    double_reverse_packed_row_step_refines_spacetime
    double_reverse_spacetime_power_preserves_decimal
    double_reverse_nibble_row_step_refines_spacetime
    double_reverse_nibble_row_power_refines_spacetime
    double_reverse_nibble_row_power_exact_window};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Packed nibble lane refinement depends on an oracle";
\<close>

end
