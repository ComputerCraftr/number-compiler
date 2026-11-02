theory Double_Reverse_Packed_Nibble_Word_Refinement
  imports Double_Reverse_Nibble_Lane_Refinement
begin

unbundle bit_operations_syntax

text \<open>This theory connects the packed integer selector planes to the
little-endian nibble word consumed by the production diagonal helper.  The
pack/add/subtract lemmas in the imported lane theory make the remaining
within-lane arithmetic explicit; they do not assume an endpoint equality.\<close>

lemma double_reverse_packed_nibble_planes_support:
  shows
    "bit (fst (double_reverse_packed_nibble_planes packed_word lane_mask)) i
       \<Longrightarrow> bit lane_mask i"
    and
    "bit (fst (snd (double_reverse_packed_nibble_planes packed_word lane_mask))) i
       \<Longrightarrow> bit lane_mask i"
    and
    "bit (fst (snd (snd (double_reverse_packed_nibble_planes packed_word lane_mask)))) i
       \<Longrightarrow> bit lane_mask i"
    and
    "bit (snd (snd (snd (double_reverse_packed_nibble_planes packed_word lane_mask)))) i
       \<Longrightarrow> bit lane_mask i"
  by (auto simp: double_reverse_packed_nibble_planes_def bit_simps Let_def)

definition double_reverse_packed_nibble_source_planes ::
    "nat list \<Rightarrow> int \<times> int \<times> int \<times> int" where
  "double_reverse_packed_nibble_source_planes source_digits =
    double_reverse_packed_nibble_planes
      (int (double_reverse_pack16 source_digits))
      (int (double_reverse_pack16 (replicate (length source_digits) 1)))"

lemma double_reverse_packed_nibble_source_lane:
  assumes digits: "\<forall>d\<in>set source_digits. d < 10"
      and index: "i < length source_digits"
  shows
    "bit (fst (double_reverse_packed_nibble_source_planes source_digits))
        (4*i) \<longleftrightarrow>
       source_digits ! i mod 5 = 3 \<or> source_digits ! i mod 5 = 4"
    and
    "bit (fst (snd (double_reverse_packed_nibble_source_planes source_digits)))
        (4*i) \<longleftrightarrow>
       bit ((4 * source_digits ! i) mod 10) 2"
    and
    "bit (fst (snd (snd (double_reverse_packed_nibble_source_planes source_digits))))
        (4*i) \<longleftrightarrow>
       source_digits ! i mod 5 = 2"
    and
    "bit (snd (snd (snd (double_reverse_packed_nibble_source_planes source_digits))))
        (4*i) \<longleftrightarrow> 5 \<le> source_digits ! i"
proof -
  have digit_bound: "source_digits ! i < 10"
    using digits index by auto
  have source_bounded: "\<forall>d\<in>set source_digits. d < 16"
    using digits by auto
  have mask_lane:
    "bit (int (double_reverse_pack16 (replicate (length source_digits) 1)))
       (4*i)"
    using double_reverse_pack16_replicate_one_support[of
        "length source_digits" "4*i"] index by simp
  have nibble:
    "double_reverse_packed_nibble_value
        (int (double_reverse_pack16 source_digits)) i =
      int (source_digits ! i)"
    by (rule double_reverse_pack16_nibble_value[OF source_bounded index])
  have p1:
    "bit (fst (double_reverse_packed_nibble_source_planes source_digits))
        (4*i) \<longleftrightarrow>
      double_reverse_nibble_plane_mod_ge_three (source_digits ! i)"
    unfolding double_reverse_packed_nibble_source_planes_def
    by (rule double_reverse_packed_nibble_planes_lane_exact(1)
      [OF mask_lane nibble digit_bound])
  have p2:
    "bit (fst (snd (double_reverse_packed_nibble_source_planes source_digits)))
        (4*i) \<longleftrightarrow>
      double_reverse_nibble_plane_times_four_bit_two (source_digits ! i)"
    unfolding double_reverse_packed_nibble_source_planes_def
    by (rule double_reverse_packed_nibble_planes_lane_exact(2)
      [OF mask_lane nibble digit_bound])
  have p3:
    "bit (fst (snd (snd (double_reverse_packed_nibble_source_planes source_digits))))
        (4*i) \<longleftrightarrow>
      double_reverse_nibble_plane_mod_equals_two (source_digits ! i)"
    unfolding double_reverse_packed_nibble_source_planes_def
    by (rule double_reverse_packed_nibble_planes_lane_exact(3)
      [OF mask_lane nibble digit_bound])
  have p4:
    "bit (snd (snd (snd (double_reverse_packed_nibble_source_planes source_digits))))
        (4*i) \<longleftrightarrow>
      double_reverse_nibble_plane_high (source_digits ! i)"
    unfolding double_reverse_packed_nibble_source_planes_def
    by (rule double_reverse_packed_nibble_planes_lane_exact(4)
      [OF mask_lane nibble digit_bound])
  have scalar1:
    "double_reverse_nibble_plane_mod_ge_three (source_digits ! i) \<longleftrightarrow>
       (source_digits ! i mod 5 = 3 \<or> source_digits ! i mod 5 = 4)"
    by (rule double_reverse_nibble_planes_exact(1)[OF digit_bound])
  have scalar2:
    "double_reverse_nibble_plane_times_four_bit_two (source_digits ! i) \<longleftrightarrow>
       bit ((4 * source_digits ! i) mod 10) 2"
    by (rule double_reverse_nibble_planes_exact(2)[OF digit_bound])
  have scalar3:
    "double_reverse_nibble_plane_mod_equals_two (source_digits ! i) \<longleftrightarrow>
       source_digits ! i mod 5 = 2"
    by (rule double_reverse_nibble_planes_exact(3)[OF digit_bound])
  have scalar4:
    "double_reverse_nibble_plane_high (source_digits ! i) \<longleftrightarrow>
       5 \<le> source_digits ! i"
    by (rule double_reverse_nibble_planes_exact(4)[OF digit_bound])
  show "bit (fst (double_reverse_packed_nibble_source_planes source_digits))
      (4*i) \<longleftrightarrow>
      source_digits ! i mod 5 = 3 \<or> source_digits ! i mod 5 = 4"
    using p1 scalar1 by simp
  show "bit (fst (snd (double_reverse_packed_nibble_source_planes source_digits)))
      (4*i) \<longleftrightarrow>
      bit ((4 * source_digits ! i) mod 10) 2"
    using p2 scalar2 by simp
  show "bit (fst (snd (snd (double_reverse_packed_nibble_source_planes source_digits))))
      (4*i) \<longleftrightarrow> source_digits ! i mod 5 = 2"
    using p3 scalar3 by simp
  show "bit (snd (snd (snd (double_reverse_packed_nibble_source_planes source_digits))))
      (4*i) \<longleftrightarrow> 5 \<le> source_digits ! i"
    using p4 scalar4 by simp
qed

lemma double_reverse_packed_plane_from_lanes:
  fixes plane :: int and selector :: "nat \<Rightarrow> bool"
  assumes mask: "\<forall>j. bit lane_mask j \<longleftrightarrow>
      j mod 4 = 0 \<and> j div 4 < length source_digits"
      and support: "\<forall>j. bit plane j \<longrightarrow> bit lane_mask j"
      and lanes: "\<forall>i<length source_digits.
        bit plane (4*i) \<longleftrightarrow> selector (source_digits ! i)"
  shows "plane = double_reverse_pack16_bits (map selector source_digits)"
proof (rule bit_eqI)
  fix j :: nat
  let ?i = "j div 4"
  let ?offset = "j mod 4"
  have index_decomposition: "j = 4 * ?i + ?offset"
    using div_mult_mod_eq[of j 4] by (simp add: mult.commute)
  show "bit plane j =
      bit (double_reverse_pack16_bits (map selector source_digits)) j"
  proof (cases "?offset = 0 \<and> ?i < length source_digits")
    case True
    then have lane_index: "?i < length source_digits" and offset: "?offset = 0"
      by auto
    have lane_coordinate: "4*?i = j"
      using index_decomposition offset by arith
    have lane_bits:
      "bit plane (4*?i) \<longleftrightarrow> selector (source_digits ! ?i)"
      using lanes lane_index by blast
    have packed_bit:
      "bit (double_reverse_pack16_bits (map selector source_digits)) j =
        selector (source_digits ! ?i)"
      using True
      by (simp add: double_reverse_pack16_bits_bit)
    show ?thesis
      using lane_bits packed_bit lane_coordinate by simp
  next
    case False
    have mask_bit: "\<not> bit lane_mask j"
      using mask False by blast
    have plane_bit: "\<not> bit plane j"
      using support mask_bit by blast
    have packed_bit:
      "\<not> bit (double_reverse_pack16_bits (map selector source_digits)) j"
      using False
      by (auto simp: double_reverse_pack16_bits_bit)
    show ?thesis using plane_bit packed_bit by simp
  qed
qed

lemma double_reverse_pack16_bits_masked_drop:
  assumes extent: "width + shift \<le> length bits"
  shows "drop_bit (4*shift) (double_reverse_pack16_bits bits) AND
      int (double_reverse_pack16 (replicate width 1)) =
    double_reverse_pack16_bits (take width (drop shift bits))"
proof (rule bit_eqI)
  fix j :: nat
  let ?i = "j div 4"
  let ?offset = "j mod 4"
  have lane_mask:
    "bit (int (double_reverse_pack16 (replicate width 1))) j \<longleftrightarrow>
      j mod 4 = 0 \<and> j div 4 < width"
    by (rule double_reverse_pack16_replicate_one_support)
  show "bit (drop_bit (4*shift) (double_reverse_pack16_bits bits) AND
      int (double_reverse_pack16 (replicate width 1))) j =
    bit (double_reverse_pack16_bits (take width (drop shift bits))) j"
  proof (cases "?offset = 0 \<and> ?i < width")
    case True
    have j_lane: "j = 4*?i"
      using div_mult_mod_eq[of j 4] True by (simp add: mult.commute)
    have source_index: "shift + ?i < length bits"
      using extent True by arith
    have drop_index: "?i < length (drop shift bits)"
      using source_index by (simp add: length_drop; arith)
    have shifted_lane: "4*shift + j = 4*(shift + ?i)"
      using j_lane by (simp add: algebra_simps)
    have left_value:
      "bit (drop_bit (4*shift) (double_reverse_pack16_bits bits)) j =
        bits ! (shift + ?i)"
      using shifted_lane source_index True
      by (simp add: bit_drop_bit_eq double_reverse_pack16_bits_bit
          div_mult_self1_is_m mod_mult_self1_is_0)
    have right_value:
      "bit (double_reverse_pack16_bits (take width (drop shift bits))) j =
        bits ! (shift + ?i)"
      using True drop_index
      by (simp add: double_reverse_pack16_bits_bit nth_take nth_drop)
    have mask_value:
      "bit (int (double_reverse_pack16 (replicate width 1))) j"
      using lane_mask True by simp
    show ?thesis using left_value right_value mask_value
      by (simp add: bit_and_iff)
  next
    case False
    have mask_zero:
      "\<not> bit (int (double_reverse_pack16 (replicate width 1))) j"
      using lane_mask False by simp
    have result_zero:
      "\<not> bit (double_reverse_pack16_bits (take width (drop shift bits))) j"
      using False
      by (auto simp: double_reverse_pack16_bits_bit)
    show ?thesis using mask_zero result_zero
      by (simp add: bit_and_iff)
  qed
qed

lemma double_reverse_map2_nested_aligned_maps:
  assumes length: "length xs = length ys"
  shows "map2 f (map g xs)
      (map2 h (map k xs) (map l ys)) =
    map2 (\<lambda>x y. f (g x) (h (k x) (l y))) xs ys"
  using length
proof (induction xs arbitrary: ys)
  case Nil
  then show ?case by (cases ys) simp_all
next
  case (Cons x xs)
  then obtain y ys' where ys: "ys = y # ys'" by (cases ys) auto
  have tail: "map2 f (map g xs)
      (map2 h (map k xs) (map l ys')) =
    map2 (\<lambda>x y. f (g x) (h (k x) (l y))) xs ys'"
    using Cons.IH Cons.prems ys by simp
  show ?case using ys tail by simp
qed

lemma double_reverse_pack16_shifted_bit_support:
  fixes source_bits :: "bool list" and shift index :: nat
  assumes shift_below: "shift < 4"
      and shifted:
        "bit (push_bit shift (double_reverse_pack16_bits source_bits)) index"
  shows "index mod 4 = shift"
proof -
  have shift_bound: "shift \<le> index"
    using shifted by (auto simp: bit_push_bit_iff)
  have lane_bit:
    "bit (double_reverse_pack16_bits source_bits) (index - shift)"
    using shifted shift_bound by (simp add: bit_push_bit_iff)
  have lane_residue: "(index - shift) mod 4 = 0"
    using lane_bit by (simp add: double_reverse_pack16_bits_bit)
  show ?thesis
    using shift_below shift_bound lane_residue by presburger
qed

lemma double_reverse_pack16_shifted_disjoint:
  fixes left right :: "bool list" and left_shift right_shift :: nat
  assumes left_below: "left_shift < 4"
      and right_below: "right_shift < 4"
      and distinct: "left_shift \<noteq> right_shift"
  shows "push_bit left_shift (double_reverse_pack16_bits left) AND
      push_bit right_shift (double_reverse_pack16_bits right) = (0::int)"
proof (rule bit_eqI)
  fix index :: nat
  have left_support:
    "bit (push_bit left_shift (double_reverse_pack16_bits left)) index
      \<Longrightarrow> index mod 4 = left_shift"
    by (rule double_reverse_pack16_shifted_bit_support[OF left_below])
  have right_support:
    "bit (push_bit right_shift (double_reverse_pack16_bits right)) index
      \<Longrightarrow> index mod 4 = right_shift"
    by (rule double_reverse_pack16_shifted_bit_support[OF right_below])
  have disjoint:
    "\<not> (bit (push_bit left_shift (double_reverse_pack16_bits left)) index \<and>
      bit (push_bit right_shift (double_reverse_pack16_bits right)) index)"
    using left_support right_support distinct by blast
  show "bit (push_bit left_shift (double_reverse_pack16_bits left) AND
      push_bit right_shift (double_reverse_pack16_bits right)) index =
      bit (0::int) index"
    using disjoint by (simp add: bit_and_iff)
qed

lemma double_reverse_pack16_boolean_weight:
  assumes shift: "shift < 4"
  shows "push_bit shift (double_reverse_pack16_bits bits) =
      int (double_reverse_pack16
        (map (\<lambda>b. if b then 2^shift else 0) bits))"
  using shift
proof (induction bits)
  case Nil
  then show ?case by simp
next
  case (Cons bit_value bit_values)
  then show ?case
    by (simp add: double_reverse_pack16_bits_eq_pack16
        push_bit_eq_mult algebra_simps)
qed

lemma double_reverse_pack16_selector_weight:
  fixes selector :: "'a \<Rightarrow> bool" and digits :: "'a list"
      and shift weight :: nat
  assumes shift_bound: "shift < 4"
      and weight: "2^shift = weight"
  shows "push_bit shift (double_reverse_pack16_bits (map selector digits)) =
      int (double_reverse_pack16
        (map (\<lambda>d. if selector d then weight else 0) digits))"
proof -
  have boolean_weight:
    "push_bit shift (double_reverse_pack16_bits (map selector digits)) =
      int (double_reverse_pack16
        (map (\<lambda>b. if b then 2^shift else 0) (map selector digits)))"
    by (rule double_reverse_pack16_boolean_weight[OF shift_bound])
  have map_weight:
    "map (\<lambda>b. if b then 2^shift else 0) (map selector digits) =
      map (\<lambda>d. if selector d then weight else 0) digits"
    using weight
  proof (induction digits)
    case Nil
    then show ?case by simp
  next
    case (Cons digit rest)
    then show ?case by (cases "selector digit") simp_all
  qed
  have packed_map:
    "int (double_reverse_pack16
        (map (\<lambda>b. if b then 2^shift else 0) (map selector digits))) =
      int (double_reverse_pack16
        (map (\<lambda>d. if selector d then weight else 0) digits))"
    by (simp only: map_weight)
  show ?thesis by (rule trans[OF boolean_weight packed_map])
qed

lemma double_reverse_boolean_weight_add:
  fixes selectors :: "bool list"
      and left_weight right_weight total_weight :: nat
  assumes total: "left_weight + right_weight = total_weight"
  shows "map2 (+) (map (\<lambda>b. if b then left_weight else 0) selectors)
      (map (\<lambda>b. if b then right_weight else 0) selectors) =
    map (\<lambda>b. if b then total_weight else 0) selectors"
proof -
  have fused:
    "map2 (+) (map (\<lambda>b. if b then left_weight else 0) selectors)
        (map (\<lambda>b. if b then right_weight else 0) selectors) =
      map (\<lambda>b. (if b then left_weight else 0) +
        (if b then right_weight else 0)) selectors"
    by (simp add: map2_map_map)
  have mapped:
    "map (\<lambda>b. (if b then left_weight else 0) +
        (if b then right_weight else 0)) selectors =
      map (\<lambda>b. if b then total_weight else 0) selectors"
  proof (induction selectors)
    case Nil
    then show ?case by simp
  next
    case (Cons bit_value rest)
    have head:
      "(if bit_value then left_weight else 0) +
        (if bit_value then right_weight else 0) =
        (if bit_value then total_weight else 0)"
      using total by (cases bit_value) simp_all
    show ?case using head Cons.IH by simp
  qed
  show ?thesis by (rule trans[OF fused mapped])
qed

lemma double_reverse_pack16_lane_mask_drop_two:
  assumes width: "2 \<le> width"
  shows "drop_bit 8 (int (double_reverse_pack16 (replicate width 1))) =
      int (double_reverse_pack16 (replicate (width - 2) 1))"
proof (rule bit_eqI)
  fix j :: nat
  have shifted_div: "(8 + j) div 4 = j div 4 + 2"
    by presburger
  have shifted_mod: "(8 + j) mod 4 = j mod 4"
    by presburger
  show "bit (drop_bit 8
      (int (double_reverse_pack16 (replicate width 1)))) j =
    bit (int (double_reverse_pack16 (replicate (width - 2) 1))) j"
    using width
    by (simp only: bit_drop_bit_eq comp_apply
        double_reverse_pack16_replicate_one_support shifted_div shifted_mod;
        arith)
qed

lemma double_reverse_pack16_add_no_lane_carry_int:
  assumes length: "length left = length right"
      and bound: "\<forall>i<length left. left ! i + right ! i < 16"
  shows "int (double_reverse_pack16 (map2 (+) left right)) =
      int (double_reverse_pack16 left) + int (double_reverse_pack16 right)"
  using double_reverse_pack16_add_no_lane_carry(1)[OF length bound]
  by simp

lemma double_reverse_pack16_pointwise_mono:
  assumes length: "length left = length right"
      and order: "\<forall>i<length left. right ! i \<le> left ! i"
  shows "double_reverse_pack16 right \<le> double_reverse_pack16 left"
  using length order
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
  proof (intro allI impI)
    fix i :: nat
    assume index: "i < length left_tail"
    have successor: "Suc i < length (left_head # left_tail)"
      using index by simp
    have order_at_successor:
      "right ! Suc i \<le> (left_head # left_tail) ! Suc i"
      using Cons.prems(2) successor by blast
    show "right_tail ! i \<le> left_tail ! i"
      using right order_at_successor by simp
  qed
  have head_index: "0 < length (left_head # left_tail)"
    by simp
  have head_order_full:
    "right ! 0 \<le> (left_head # left_tail) ! 0"
    using Cons.prems(2) head_index by blast
  have head_order: "right_head \<le> left_head"
    using right head_order_full by simp
  have tail:
    "double_reverse_pack16 right_tail \<le>
      double_reverse_pack16 left_tail"
    by (rule Cons.IH[OF tail_length tail_order])
  show ?case using head_order tail right by (simp; arith)
qed

lemma double_reverse_pack16_sub_no_lane_borrow_int:
  assumes length: "length left = length right"
      and order: "\<forall>i<length left. right ! i \<le> left ! i"
      and bound: "\<forall>i<length left. left ! i < 16"
  shows "int (double_reverse_pack16
      (map2 (\<lambda>x y. x-y) left right)) =
    int (double_reverse_pack16 left) - int (double_reverse_pack16 right)"
proof -
  have packed_order:
    "double_reverse_pack16 right \<le> double_reverse_pack16 left"
    by (rule double_reverse_pack16_pointwise_mono[OF length order])
  have natural_difference:
    "double_reverse_pack16 (map2 (\<lambda>x y. x-y) left right) =
      double_reverse_pack16 left - double_reverse_pack16 right"
    by (rule double_reverse_pack16_sub_no_lane_borrow[OF length order bound])
  show ?thesis
    using natural_difference packed_order
    by (simp add: of_nat_diff)
qed

definition double_reverse_packed_diagonal_state_step :: "nat \<Rightarrow> int \<Rightarrow> int" where
  "double_reverse_packed_diagonal_state_step width packed_word =
    (let full_lanes = int (double_reverse_pack16 (replicate width 1));
         lanes = drop_bit 8 full_lanes;
         planes = double_reverse_packed_nibble_planes packed_word full_lanes;
         mod_ge_three = fst planes;
         times_four_bit_two = fst (snd planes);
         mod_equals_two = fst (snd (snd planes));
         high = snd (snd (snd planes));
         center_bit_one = drop_bit 4 mod_ge_three AND lanes;
         center_bit_two = drop_bit 4 times_four_bit_two AND lanes;
         center_bit_three = drop_bit 4 mod_equals_two AND lanes;
         center_high = drop_bit 4 high AND lanes;
         left_high = drop_bit 8 high AND lanes;
         right_carry = (mod_ge_three AND lanes) OR
           ((mod_equals_two AND lanes) AND center_high);
         candidate = (push_bit 1 center_bit_one OR
             push_bit 2 center_bit_two OR push_bit 3 center_bit_three) +
           push_bit 1 left_high + right_carry;
         overflow = center_bit_three AND left_high;
         correction = push_bit 3 overflow OR push_bit 1 overflow
     in candidate - correction)"

definition double_reverse_packed_diagonal_word_step :: "nat list \<Rightarrow> int" where
  "double_reverse_packed_diagonal_word_step source_digits =
    double_reverse_packed_diagonal_state_step
      (length source_digits) (int (double_reverse_pack16 source_digits))"

definition double_reverse_packed_diagonal_scalar_step ::
    "nat list \<Rightarrow> nat list" where
  "double_reverse_packed_diagonal_scalar_step source_digits =
    map (\<lambda>i. double_reverse_nibble_lane_result
      (source_digits ! (i+2)) (source_digits ! (i+1)) (source_digits ! i))
      [0..<length source_digits - 2]"

lemma double_reverse_packed_diagonal_scalar_step_length:
  "length (double_reverse_packed_diagonal_scalar_step source_digits) =
    length source_digits - 2"
  by (simp add: double_reverse_packed_diagonal_scalar_step_def)

theorem double_reverse_packed_nibble_planes_source_exact:
  assumes digits: "\<forall>d\<in>set source_digits. d < 10"
  shows
    "double_reverse_packed_nibble_planes
       (int (double_reverse_pack16 source_digits))
       (int (double_reverse_pack16 (replicate (length source_digits) 1))) =
      (double_reverse_pack16_bits
          (map (\<lambda>d. d mod 5 = 3 \<or> d mod 5 = 4) source_digits),
       double_reverse_pack16_bits
          (map (\<lambda>d. bit ((4*d) mod 10) 2) source_digits),
       double_reverse_pack16_bits
          (map (\<lambda>d. d mod 5 = 2) source_digits),
       double_reverse_pack16_bits (map (\<lambda>d. 5 \<le> d) source_digits))"
proof -
  let ?mask = "int (double_reverse_pack16 (replicate (length source_digits) 1))"
  let ?planes = "double_reverse_packed_nibble_planes
      (int (double_reverse_pack16 source_digits)) ?mask"
  have mask_support:
    "\<forall>j. bit ?mask j \<longleftrightarrow>
      j mod 4 = 0 \<and> j div 4 < length source_digits"
    using double_reverse_pack16_replicate_one_support[of
        "length source_digits"] by simp
  have p1_support: "\<forall>j. bit (fst ?planes) j \<longrightarrow> bit ?mask j"
  proof (intro allI impI)
    fix j :: nat
    assume lane_bit: "bit (fst ?planes) j"
    show "bit ?mask j"
      using lane_bit by (rule double_reverse_packed_nibble_planes_support(1))
  qed
  have p2_support:
    "\<forall>j. bit (fst (snd ?planes)) j \<longrightarrow> bit ?mask j"
  proof (intro allI impI)
    fix j :: nat
    assume lane_bit: "bit (fst (snd ?planes)) j"
    show "bit ?mask j"
      using lane_bit by (rule double_reverse_packed_nibble_planes_support(2))
  qed
  have p3_support:
    "\<forall>j. bit (fst (snd (snd ?planes))) j \<longrightarrow> bit ?mask j"
  proof (intro allI impI)
    fix j :: nat
    assume lane_bit: "bit (fst (snd (snd ?planes))) j"
    show "bit ?mask j"
      using lane_bit by (rule double_reverse_packed_nibble_planes_support(3))
  qed
  have p4_support:
    "\<forall>j. bit (snd (snd (snd ?planes))) j \<longrightarrow> bit ?mask j"
  proof (intro allI impI)
    fix j :: nat
    assume lane_bit: "bit (snd (snd (snd ?planes))) j"
    show "bit ?mask j"
      using lane_bit by (rule double_reverse_packed_nibble_planes_support(4))
  qed
  have p1_lane:
    "\<forall>i<length source_digits. bit (fst ?planes) (4*i) \<longleftrightarrow>
      source_digits ! i mod 5 = 3 \<or> source_digits ! i mod 5 = 4"
  proof (intro allI impI)
    fix i :: nat
    assume index: "i < length source_digits"
    have source_lane:
      "bit (fst (double_reverse_packed_nibble_source_planes source_digits))
          (4*i) \<longleftrightarrow>
        source_digits ! i mod 5 = 3 \<or> source_digits ! i mod 5 = 4"
      by (rule double_reverse_packed_nibble_source_lane(1)[OF digits index])
    show "bit (fst ?planes) (4*i) \<longleftrightarrow>
      source_digits ! i mod 5 = 3 \<or> source_digits ! i mod 5 = 4"
      using source_lane by (simp only: double_reverse_packed_nibble_source_planes_def)
  qed
  have p2_lane:
    "\<forall>i<length source_digits. bit (fst (snd ?planes)) (4*i) \<longleftrightarrow>
      bit ((4 * source_digits ! i) mod 10) 2"
  proof (intro allI impI)
    fix i :: nat
    assume index: "i < length source_digits"
    have source_lane:
      "bit (fst (snd (double_reverse_packed_nibble_source_planes source_digits)))
          (4*i) \<longleftrightarrow>
        bit ((4 * source_digits ! i) mod 10) 2"
      by (rule double_reverse_packed_nibble_source_lane(2)[OF digits index])
    show "bit (fst (snd ?planes)) (4*i) \<longleftrightarrow>
      bit ((4 * source_digits ! i) mod 10) 2"
      using source_lane by (simp only: double_reverse_packed_nibble_source_planes_def)
  qed
  have p3_lane:
    "\<forall>i<length source_digits. bit (fst (snd (snd ?planes))) (4*i) \<longleftrightarrow>
      source_digits ! i mod 5 = 2"
  proof (intro allI impI)
    fix i :: nat
    assume index: "i < length source_digits"
    have source_lane:
      "bit (fst (snd (snd (double_reverse_packed_nibble_source_planes source_digits))))
          (4*i) \<longleftrightarrow>
        source_digits ! i mod 5 = 2"
      by (rule double_reverse_packed_nibble_source_lane(3)[OF digits index])
    show "bit (fst (snd (snd ?planes))) (4*i) \<longleftrightarrow>
      source_digits ! i mod 5 = 2"
      using source_lane by (simp only: double_reverse_packed_nibble_source_planes_def)
  qed
  have p4_lane:
    "\<forall>i<length source_digits. bit (snd (snd (snd ?planes))) (4*i) \<longleftrightarrow>
      5 \<le> source_digits ! i"
  proof (intro allI impI)
    fix i :: nat
    assume index: "i < length source_digits"
    have source_lane:
      "bit (snd (snd (snd (double_reverse_packed_nibble_source_planes source_digits))))
          (4*i) \<longleftrightarrow>
        5 \<le> source_digits ! i"
      by (rule double_reverse_packed_nibble_source_lane(4)[OF digits index])
    show "bit (snd (snd (snd ?planes))) (4*i) \<longleftrightarrow>
      5 \<le> source_digits ! i"
      using source_lane by (simp only: double_reverse_packed_nibble_source_planes_def)
  qed
  have p1: "fst ?planes = double_reverse_pack16_bits
      (map (\<lambda>d. d mod 5 = 3 \<or> d mod 5 = 4) source_digits)"
    by (rule double_reverse_packed_plane_from_lanes[OF mask_support p1_support p1_lane])
  have p2: "fst (snd ?planes) = double_reverse_pack16_bits
      (map (\<lambda>d. bit ((4*d) mod 10) 2) source_digits)"
    by (rule double_reverse_packed_plane_from_lanes[OF mask_support p2_support p2_lane])
  have p3: "fst (snd (snd ?planes)) = double_reverse_pack16_bits
      (map (\<lambda>d. d mod 5 = 2) source_digits)"
    by (rule double_reverse_packed_plane_from_lanes[OF mask_support p3_support p3_lane])
  have p4: "snd (snd (snd ?planes)) = double_reverse_pack16_bits
      (map (\<lambda>d. 5 \<le> d) source_digits)"
    by (rule double_reverse_packed_plane_from_lanes[OF mask_support p4_support p4_lane])
  show ?thesis using p1 p2 p3 p4
    by (simp add: double_reverse_packed_nibble_planes_def Let_def)
qed


lemma double_reverse_packed_source_selector_slice:
  assumes width: "2 \<le> length source_digits"
      and shift: "shift \<le> 2"
  shows "drop_bit (4*shift)
      (double_reverse_pack16_bits (map selector source_digits)) AND
      int (double_reverse_pack16
        (replicate (length source_digits - 2) 1)) =
    double_reverse_pack16_bits
      (map selector
        (take (length source_digits - 2) (drop shift source_digits)))"
proof -
  have extent:
    "length source_digits - 2 + shift \<le> length (map selector source_digits)"
    using width shift by (simp only: length_map; arith)
  show ?thesis
    using double_reverse_pack16_bits_masked_drop[OF extent]
    by (simp add: drop_map take_map)
qed

lemma double_reverse_packed_nibble_source_planes_tuple:
  assumes digits: "\<forall>d\<in>set source_digits. d < 10"
  shows
    "double_reverse_packed_nibble_source_planes source_digits =
      (double_reverse_pack16_bits
          (map (\<lambda>d. d mod 5 = 3 \<or> d mod 5 = 4) source_digits),
       double_reverse_pack16_bits
          (map (\<lambda>d. bit ((4*d) mod 10) 2) source_digits),
       double_reverse_pack16_bits
          (map (\<lambda>d. d mod 5 = 2) source_digits),
       double_reverse_pack16_bits (map (\<lambda>d. 5 \<le> d) source_digits))"
  using double_reverse_packed_nibble_planes_source_exact[OF digits]
  by (simp add: double_reverse_packed_nibble_source_planes_def)


definition double_reverse_nibble_source_base :: "nat list \<Rightarrow> nat list" where
  "double_reverse_nibble_source_base source_digits =
    map double_reverse_nibble_base
      (take (length source_digits - 2) (drop 1 source_digits))"

definition double_reverse_nibble_source_left :: "nat list \<Rightarrow> nat list" where
  "double_reverse_nibble_source_left source_digits =
    map (\<lambda>d. if double_reverse_nibble_plane_high d then 2 else 0)
      (take (length source_digits - 2) (drop 2 source_digits))"

definition double_reverse_nibble_source_right :: "nat list \<Rightarrow> nat list" where
  "double_reverse_nibble_source_right source_digits =
    map2 (\<lambda>right center.
      if double_reverse_nibble_plane_mod_ge_three right \<or>
         (double_reverse_nibble_plane_mod_equals_two right \<and>
           double_reverse_nibble_plane_high center)
      then 1 else 0)
      (take (length source_digits - 2) source_digits)
      (take (length source_digits - 2) (drop 1 source_digits))"

definition double_reverse_nibble_source_candidate :: "nat list \<Rightarrow> nat list" where
  "double_reverse_nibble_source_candidate source_digits =
    map2 (+)
      (map2 (+) (double_reverse_nibble_source_base source_digits)
        (double_reverse_nibble_source_left source_digits))
      (double_reverse_nibble_source_right source_digits)"

definition double_reverse_nibble_source_overflow :: "nat list \<Rightarrow> nat list" where
  "double_reverse_nibble_source_overflow source_digits =
    map2 (\<lambda>center left.
      if double_reverse_nibble_plane_mod_equals_two center \<and>
         double_reverse_nibble_plane_high left
      then 10 else 0)
      (take (length source_digits - 2) (drop 1 source_digits))
      (take (length source_digits - 2) (drop 2 source_digits))"

definition double_reverse_nibble_source_result :: "nat list \<Rightarrow> nat list" where
  "double_reverse_nibble_source_result source_digits =
    map2 (\<lambda>candidate correction. candidate - correction)
      (double_reverse_nibble_source_candidate source_digits)
      (double_reverse_nibble_source_overflow source_digits)"

lemma double_reverse_pack16_bits_and:
  assumes length: "length left = length right"
  shows "double_reverse_pack16_bits left AND double_reverse_pack16_bits right =
    double_reverse_pack16_bits (map2 (\<and>) left right)"
proof (rule bit_eqI)
  fix j :: nat
  show "bit (double_reverse_pack16_bits left AND
      double_reverse_pack16_bits right) j =
    bit (double_reverse_pack16_bits (map2 (\<and>) left right)) j"
    using length
    by (auto simp: bit_and_iff double_reverse_pack16_bits_bit)
qed

lemma double_reverse_pack16_bits_or:
  assumes length: "length left = length right"
  shows "double_reverse_pack16_bits left OR double_reverse_pack16_bits right =
    double_reverse_pack16_bits (map2 (\<or>) left right)"
proof (rule bit_eqI)
  fix j :: nat
  show "bit (double_reverse_pack16_bits left OR
      double_reverse_pack16_bits right) j =
    bit (double_reverse_pack16_bits (map2 (\<or>) left right)) j"
    using length
    by (auto simp: bit_or_iff double_reverse_pack16_bits_bit)
qed

lemma double_reverse_nibble_source_result_scalar_exact:
  "double_reverse_nibble_source_result source_digits =
    double_reverse_packed_diagonal_scalar_step source_digits"
proof (rule nth_equalityI)
  show "length (double_reverse_nibble_source_result source_digits) =
      length (double_reverse_packed_diagonal_scalar_step source_digits)"
    by (simp add: double_reverse_nibble_source_result_def
        double_reverse_nibble_source_candidate_def
        double_reverse_nibble_source_overflow_def
        double_reverse_nibble_source_base_def
        double_reverse_nibble_source_left_def
        double_reverse_nibble_source_right_def
        double_reverse_packed_diagonal_scalar_step_def)
next
  fix i :: nat
  assume index: "i < length (double_reverse_nibble_source_result source_digits)"
  then have bound: "i < length source_digits - 2"
    by (simp add: double_reverse_nibble_source_result_def
        double_reverse_nibble_source_candidate_def
        double_reverse_nibble_source_overflow_def
        double_reverse_nibble_source_base_def
        double_reverse_nibble_source_left_def
        double_reverse_nibble_source_right_def)
  show "double_reverse_nibble_source_result source_digits ! i =
      double_reverse_packed_diagonal_scalar_step source_digits ! i"
    using bound
    by (simp add: double_reverse_nibble_source_result_def
        double_reverse_nibble_source_candidate_def
        double_reverse_nibble_source_overflow_def
        double_reverse_nibble_source_base_def
        double_reverse_nibble_source_left_def
        double_reverse_nibble_source_right_def
        double_reverse_packed_diagonal_scalar_step_def
        double_reverse_nibble_lane_result_def)
qed


lemma double_reverse_nibble_base_at_most_eight:
  assumes decimal: "d < 10"
  shows "double_reverse_nibble_base d \<le> 8"
proof -
  have remainder_bound: "d mod 5 < 5"
    by simp
  then have remainder_cases:
    "d mod 5 = 0 \<or> d mod 5 = 1 \<or> d mod 5 = 2 \<or>
      d mod 5 = 3 \<or> d mod 5 = 4"
    by arith
  have base_formula:
    "double_reverse_nibble_base d = (4 * (d mod 5)) mod 10"
    by (rule double_reverse_nibble_base_exact[OF decimal])
  show ?thesis
    using base_formula remainder_cases
    by (elim disjE; simp)
qed

lemma double_reverse_nibble_source_candidate_bounds:
  assumes width: "2 \<le> length source_digits"
      and decimal: "\<forall>d\<in>set source_digits. d < 10"
  shows "\<forall>i<length source_digits - 2.
      double_reverse_nibble_source_candidate source_digits ! i < 16 \<and>
      double_reverse_nibble_source_overflow source_digits ! i \<le>
        double_reverse_nibble_source_candidate source_digits ! i"
proof (intro allI impI)
  fix i :: nat
  assume index: "i < length source_digits - 2"
  let ?left = "source_digits ! (i+2)"
  let ?center = "source_digits ! (i+1)"
  let ?right = "source_digits ! i"
  have extent: "i+2 < length source_digits"
    using index by arith
  have left_bound: "?left < 10"
    using decimal extent by auto
  have center_bound: "?center < 10"
    using decimal extent by auto
  have right_bound: "?right < 10"
    using decimal index by auto
  have lane_bound:
    "double_reverse_nibble_base ?center +
       2 * (if double_reverse_nibble_plane_high ?left then 1 else 0) +
       (if double_reverse_nibble_plane_mod_ge_three ?right \<or>
          (double_reverse_nibble_plane_mod_equals_two ?right \<and>
            double_reverse_nibble_plane_high ?center) then 1 else 0) < 16 \<and>
     (if double_reverse_nibble_plane_mod_equals_two ?center \<and>
          double_reverse_nibble_plane_high ?left then 10 else 0) \<le>
       double_reverse_nibble_base ?center +
       2 * (if double_reverse_nibble_plane_high ?left then 1 else 0) +
       (if double_reverse_nibble_plane_mod_ge_three ?right \<or>
          (double_reverse_nibble_plane_mod_equals_two ?right \<and>
            double_reverse_nibble_plane_high ?center) then 1 else 0)"
    using double_reverse_nibble_candidate_bounds
      [OF left_bound center_bound right_bound]
    by simp
  have source_left: "take (length source_digits - 2)
      (drop 2 source_digits) ! i = ?left"
    using index by (simp add: nth_take nth_drop)
  have source_center: "take (length source_digits - 2)
      (drop 1 source_digits) ! i = ?center"
    using index by (simp add: nth_take nth_drop)
  have source_right: "take (length source_digits - 2) source_digits ! i = ?right"
    using index by (simp add: nth_take)
  have candidate_value:
    "double_reverse_nibble_source_candidate source_digits ! i =
      double_reverse_nibble_base ?center +
        2 * (if double_reverse_nibble_plane_high ?left then 1 else 0) +
        (if double_reverse_nibble_plane_mod_ge_three ?right \<or>
            (double_reverse_nibble_plane_mod_equals_two ?right \<and>
              double_reverse_nibble_plane_high ?center)
         then 1 else 0)"
    using index source_left source_center source_right
    by (simp add: double_reverse_nibble_source_candidate_def
        double_reverse_nibble_source_base_def
        double_reverse_nibble_source_left_def
        double_reverse_nibble_source_right_def)
  have overflow_value:
    "double_reverse_nibble_source_overflow source_digits ! i =
      (if double_reverse_nibble_plane_mod_equals_two ?center \<and>
          double_reverse_nibble_plane_high ?left then 10 else 0)"
    using index source_center source_left
    by (simp add: double_reverse_nibble_source_overflow_def)
  show "double_reverse_nibble_source_candidate source_digits ! i < 16 \<and>
      double_reverse_nibble_source_overflow source_digits ! i \<le>
        double_reverse_nibble_source_candidate source_digits ! i"
    using lane_bound
    by (simp only: candidate_value overflow_value)
qed


ML \<open>
  val checked = @{thms
    double_reverse_packed_nibble_planes_support
    double_reverse_map2_nested_aligned_maps
    double_reverse_packed_nibble_source_lane
    double_reverse_packed_plane_from_lanes
    double_reverse_pack16_bits_masked_drop
    double_reverse_pack16_shifted_bit_support
    double_reverse_pack16_shifted_disjoint
    double_reverse_pack16_boolean_weight
    double_reverse_pack16_selector_weight
    double_reverse_boolean_weight_add
    double_reverse_pack16_lane_mask_drop_two
    double_reverse_pack16_add_no_lane_carry_int
    double_reverse_pack16_pointwise_mono
    double_reverse_pack16_sub_no_lane_borrow_int
    double_reverse_packed_nibble_planes_source_exact
    double_reverse_packed_source_selector_slice
    double_reverse_packed_nibble_source_planes_tuple
    double_reverse_nibble_source_result_scalar_exact
    double_reverse_nibble_base_at_most_eight
    double_reverse_nibble_source_candidate_bounds};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Packed nibble word refinement depends on an oracle";
\<close>

end
