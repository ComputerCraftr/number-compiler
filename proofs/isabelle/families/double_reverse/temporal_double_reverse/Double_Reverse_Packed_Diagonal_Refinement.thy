theory Double_Reverse_Packed_Diagonal_Refinement
  imports Double_Reverse_Packed_Nibble_Word_Refinement
begin

lemma double_reverse_decimal_row_set:
  "double_reverse_decimal_row row \<longleftrightarrow> (\<forall>d\<in>set row. d < 10)"
  by (simp only: double_reverse_decimal_row_def all_set_conv_all_nth)

lemma double_reverse_disjoint_and_bit:
  fixes x y :: int and i :: nat
  assumes "x AND y = 0"
  shows "\<not> (bit x i \<and> bit y i)"
proof -
  have bit_zero: "bit (x AND y) i = False"
    using assms by simp
  then show ?thesis by (simp add: bit_and_iff)
qed

lemma double_reverse_packed_diagonal_word_step_exact:
  assumes width: "2 \<le> length source_digits"
      and decimal: "\<forall>d\<in>set source_digits. d < 10"
  shows "double_reverse_packed_diagonal_word_step source_digits =
    int (double_reverse_pack16
      (double_reverse_nibble_source_result source_digits))"
proof -
  let ?n = "length source_digits"
  let ?m = "?n - 2"
  let ?centers = "take ?m (drop 1 source_digits)"
  let ?lefts = "take ?m (drop 2 source_digits)"
  let ?rights = "take ?m source_digits"
  have centers_length[simp]: "length ?centers = ?m"
    using width by simp
  have lefts_length[simp]: "length ?lefts = ?m"
    using width by simp
  have rights_length[simp]: "length ?rights = ?m" by simp
  let ?mask = "int (double_reverse_pack16 (replicate ?n 1))"
  let ?planes = "double_reverse_packed_nibble_planes
    (int (double_reverse_pack16 source_digits)) ?mask"
  let ?p1 = "fst ?planes"
  let ?p2 = "fst (snd ?planes)"
  let ?p3 = "fst (snd (snd ?planes))"
  let ?p4 = "snd (snd (snd ?planes))"
  let ?lanes = "int (double_reverse_pack16 (replicate ?m 1))"
  have source_planes:
    "?planes =
      (double_reverse_pack16_bits
          (map (\<lambda>d. d mod 5 = 3 \<or> d mod 5 = 4) source_digits),
       double_reverse_pack16_bits
          (map (\<lambda>d. bit ((4*d) mod 10) 2) source_digits),
       double_reverse_pack16_bits
          (map (\<lambda>d. d mod 5 = 2) source_digits),
       double_reverse_pack16_bits (map (\<lambda>d. 5 \<le> d) source_digits))"
    by (rule double_reverse_packed_nibble_planes_source_exact[OF decimal])
  have lanes: "drop_bit 8 ?mask = ?lanes"
    by (rule double_reverse_pack16_lane_mask_drop_two[OF width])
  have p1: "?p1 = double_reverse_pack16_bits
      (map (\<lambda>d. d mod 5 = 3 \<or> d mod 5 = 4) source_digits)"
    using source_planes by simp
  have p2: "?p2 = double_reverse_pack16_bits
      (map (\<lambda>d. bit ((4*d) mod 10) 2) source_digits)"
    using source_planes by simp
  have p3: "?p3 = double_reverse_pack16_bits
      (map (\<lambda>d. d mod 5 = 2) source_digits)"
    using source_planes by simp
  have p4: "?p4 = double_reverse_pack16_bits
      (map (\<lambda>d. 5 \<le> d) source_digits)"
    using source_planes by simp
  have c1:
    "drop_bit 4 ?p1 AND ?lanes = double_reverse_pack16_bits
      (map (\<lambda>d. d mod 5 = 3 \<or> d mod 5 = 4) ?centers)"
    using double_reverse_packed_source_selector_slice
      [where source_digits=source_digits
        and selector="\<lambda>d. d mod 5 = 3 \<or> d mod 5 = 4" and shift=1]
      width unfolding p1 by simp
  have c2:
    "drop_bit 4 ?p2 AND ?lanes = double_reverse_pack16_bits
      (map (\<lambda>d. bit ((4*d) mod 10) 2) ?centers)"
    using double_reverse_packed_source_selector_slice
      [where source_digits=source_digits
        and selector="\<lambda>d. bit ((4*d) mod 10) 2" and shift=1]
      width unfolding p2 by simp
  have c3:
    "drop_bit 4 ?p3 AND ?lanes = double_reverse_pack16_bits
      (map (\<lambda>d. d mod 5 = 2) ?centers)"
    using double_reverse_packed_source_selector_slice
      [where source_digits=source_digits
        and selector="\<lambda>d. d mod 5 = 2" and shift=1]
      width unfolding p3 by simp
  have ch:
    "drop_bit 4 ?p4 AND ?lanes = double_reverse_pack16_bits
      (map (\<lambda>d. 5 \<le> d) ?centers)"
    using double_reverse_packed_source_selector_slice
      [where source_digits=source_digits
        and selector="\<lambda>d. 5 \<le> d" and shift=1]
      width unfolding p4 by simp
  have lh:
    "drop_bit 8 ?p4 AND ?lanes = double_reverse_pack16_bits
      (map (\<lambda>d. 5 \<le> d) ?lefts)"
    using double_reverse_packed_source_selector_slice
      [where source_digits=source_digits
        and selector="\<lambda>d. 5 \<le> d" and shift=2]
      width unfolding p4 by simp
  have r1:
    "?p1 AND ?lanes = double_reverse_pack16_bits
      (map (\<lambda>d. d mod 5 = 3 \<or> d mod 5 = 4) ?rights)"
    using double_reverse_packed_source_selector_slice
      [where source_digits=source_digits
        and selector="\<lambda>d. d mod 5 = 3 \<or> d mod 5 = 4" and shift=0]
      width unfolding p1 by simp
  have r2:
    "?p3 AND ?lanes = double_reverse_pack16_bits
      (map (\<lambda>d. d mod 5 = 2) ?rights)"
    using double_reverse_packed_source_selector_slice
      [where source_digits=source_digits
        and selector="\<lambda>d. d mod 5 = 2" and shift=0]
      width unfolding p3 by simp
  have right:
    "(?p1 AND ?lanes) OR ((?p3 AND ?lanes) AND
        (drop_bit 4 ?p4 AND ?lanes)) =
      double_reverse_pack16_bits (map2 (\<or>)
        (map (\<lambda>d. d mod 5 = 3 \<or> d mod 5 = 4) ?rights)
        (map2 (\<and>) (map (\<lambda>d. d mod 5 = 2) ?rights)
          (map (\<lambda>d. 5 \<le> d) ?centers)))"
    unfolding r1 r2 ch
    apply (subst double_reverse_pack16_bits_and)
     apply (simp only: length_map rights_length centers_length)
    apply (rule double_reverse_pack16_bits_or)
    by (simp only: length_map length_zip rights_length centers_length; simp)
  let ?b1 = "push_bit 1 (double_reverse_pack16_bits
      (map (\<lambda>d. d mod 5 = 3 \<or> d mod 5 = 4) ?centers))"
  let ?b2 = "push_bit 2 (double_reverse_pack16_bits
      (map (\<lambda>d. bit ((4*d) mod 10) 2) ?centers))"
  let ?b3 = "push_bit 3 (double_reverse_pack16_bits
      (map (\<lambda>d. d mod 5 = 2) ?centers))"
  have b12_disjoint: "?b1 AND ?b2 = 0"
    by (rule double_reverse_pack16_shifted_disjoint) simp_all
  have b13_disjoint: "?b1 AND ?b3 = 0"
    by (rule double_reverse_pack16_shifted_disjoint) simp_all
  have b23_disjoint: "?b2 AND ?b3 = 0"
    by (rule double_reverse_pack16_shifted_disjoint) simp_all
  have b12_sum_disjoint: "(?b1 OR ?b2) AND ?b3 = 0"
  proof (rule bit_eqI)
    fix i :: nat
    have no_b1_b3: "\<not> (bit ?b1 i \<and> bit ?b3 i)"
      by (rule double_reverse_disjoint_and_bit[OF b13_disjoint])
    have no_b2_b3: "\<not> (bit ?b2 i \<and> bit ?b3 i)"
      by (rule double_reverse_disjoint_and_bit[OF b23_disjoint])
    show "bit ((?b1 OR ?b2) AND ?b3) i = bit 0 i"
      using no_b1_b3 no_b2_b3 by (auto simp: bit_and_iff bit_or_iff)
  qed
  have base_or:
    "(?b1 OR ?b2) OR ?b3 = ?b1 + ?b2 + ?b3"
  proof -
    have first: "?b1 OR ?b2 = ?b1 + ?b2"
      by (rule sym[OF disjunctive_add_eq_or[OF b12_disjoint]])
    have second: "(?b1 OR ?b2) OR ?b3 = (?b1 OR ?b2) + ?b3"
      by (rule sym[OF disjunctive_add_eq_or[OF b12_sum_disjoint]])
    show ?thesis using first second by (simp add: algebra_simps)
  qed
  have b1_weight:
    "?b1 = int (double_reverse_pack16
      (map (\<lambda>d. if d mod 5 = 3 \<or> d mod 5 = 4 then 2 else 0) ?centers))"
    by (rule double_reverse_pack16_selector_weight) simp_all
  have b2_weight:
    "?b2 = int (double_reverse_pack16
      (map (\<lambda>d. if bit ((4*d) mod 10) 2 then 4 else 0) ?centers))"
    by (rule double_reverse_pack16_selector_weight) simp_all
  have b3_weight:
    "?b3 = int (double_reverse_pack16
      (map (\<lambda>d. if d mod 5 = 2 then 8 else 0) ?centers))"
    by (rule double_reverse_pack16_selector_weight) simp_all
  have base_decomposition:
    "double_reverse_nibble_source_base source_digits =
      map (\<lambda>d. (if d mod 5 = 3 \<or> d mod 5 = 4 then 2 else 0) +
        (if bit ((4*d) mod 10) 2 then 4 else 0) +
        (if d mod 5 = 2 then 8 else 0)) ?centers"
  proof -
    have center_decimal: "\<forall>d\<in>set ?centers. d < 10"
      using decimal by (auto dest: in_set_takeD in_set_dropD)
    show ?thesis
      unfolding double_reverse_nibble_source_base_def
    proof (rule map_cong[OF refl])
      fix d
      assume member: "d \<in> set ?centers"
      have bound: "d < 10"
        using center_decimal member by blast
      have e1: "double_reverse_nibble_plane_mod_ge_three d \<longleftrightarrow>
          (d mod 5 = 3 \<or> d mod 5 = 4)"
        by (rule double_reverse_nibble_planes_exact(1)[OF bound])
      have e2: "double_reverse_nibble_plane_times_four_bit_two d \<longleftrightarrow>
          bit ((4*d) mod 10) 2"
        by (rule double_reverse_nibble_planes_exact(2)[OF bound])
      have e3: "double_reverse_nibble_plane_mod_equals_two d \<longleftrightarrow>
          d mod 5 = 2"
        by (rule double_reverse_nibble_planes_exact(3)[OF bound])
      show "double_reverse_nibble_base d =
          (if d mod 5 = 3 \<or> d mod 5 = 4 then 2 else 0) +
          (if bit ((4*d) mod 10) 2 then 4 else 0) +
          (if d mod 5 = 2 then 8 else 0)"
        using e1 e2 e3
        by (auto simp: double_reverse_nibble_base_def split: if_splits)
    qed
  qed
  have base_pack:
    "int (double_reverse_pack16
      (double_reverse_nibble_source_base source_digits)) = ?b1 + ?b2 + ?b3"
  proof -
    have add12:
      "int (double_reverse_pack16
          (map (\<lambda>d. (if d mod 5 = 3 \<or> d mod 5 = 4 then 2 else 0) +
            (if bit ((4*d) mod 10) 2 then 4 else 0)) ?centers)) =
        ?b1 + ?b2"
    proof -
      have lengths: "length (map (\<lambda>d.
          if d mod 5 = 3 \<or> d mod 5 = 4 then 2 else 0) ?centers) =
        length (map (\<lambda>d. if bit ((4*d) mod 10) 2 then 4 else 0)
          ?centers)" by simp
      have bound: "\<forall>i<length ?centers.
          (map (\<lambda>d. if d mod 5 = 3 \<or> d mod 5 = 4 then 2 else 0)
             ?centers) ! i +
          (map (\<lambda>d. if bit ((4*d) mod 10) 2 then 4 else 0)
             ?centers) ! i < (16::nat)"
        by (auto simp: nth_map)
      have packed:
        "int (double_reverse_pack16 (map2 (+)
          (map (\<lambda>d. if d mod 5 = 3 \<or> d mod 5 = 4 then 2 else 0)
            ?centers)
          (map (\<lambda>d. if bit ((4*d) mod 10) 2 then 4 else 0)
            ?centers))) = ?b1 + ?b2"
        using double_reverse_pack16_add_no_lane_carry_int[OF lengths] bound
          b1_weight b2_weight by simp
      show ?thesis using packed by (simp add: map2_map_map)
    qed
    have add123:
      "int (double_reverse_pack16 (map (\<lambda>d.
          (if d mod 5 = 3 \<or> d mod 5 = 4 then 2 else 0) +
          (if bit ((4*d) mod 10) 2 then 4 else 0) +
          (if d mod 5 = 2 then 8 else 0)) ?centers)) =
        ?b1 + ?b2 + ?b3"
    proof -
      have lengths: "length (map (\<lambda>d.
          (if d mod 5 = 3 \<or> d mod 5 = 4 then 2 else 0) +
          (if bit ((4*d) mod 10) 2 then 4 else 0)) ?centers) =
        length (map (\<lambda>d. if d mod 5 = 2 then 8 else 0) ?centers)"
        by simp
      have bound: "\<forall>i<length ?centers.
          (map (\<lambda>d. (if d mod 5 = 3 \<or> d mod 5 = 4 then 2 else 0) +
                (if bit ((4*d) mod 10) 2 then 4 else 0)) ?centers) ! i +
          (map (\<lambda>d. if d mod 5 = 2 then 8 else 0) ?centers) ! i < (16::nat)"
        by (auto simp: nth_map)
      have packed:
        "int (double_reverse_pack16 (map2 (+)
          (map (\<lambda>d. (if d mod 5 = 3 \<or> d mod 5 = 4 then 2 else 0) +
                (if bit ((4*d) mod 10) 2 then 4 else 0)) ?centers)
          (map (\<lambda>d. if d mod 5 = 2 then 8 else 0) ?centers))) =
            ?b1 + ?b2 + ?b3"
        using double_reverse_pack16_add_no_lane_carry_int[OF lengths] bound
          add12 b3_weight by simp
      show ?thesis using packed by (simp add: map2_map_map)
    qed
    show ?thesis using add123 base_decomposition by simp
  qed
  have left_source:
    "double_reverse_nibble_source_left source_digits =
      map (\<lambda>d. if 5 \<le> d then 2 else 0) ?lefts"
    unfolding double_reverse_nibble_source_left_def
  proof (rule map_cong[OF refl])
    fix d assume member: "d \<in> set ?lefts"
    have bound: "d < 10" using decimal member
      by (auto dest: in_set_takeD in_set_dropD)
    then show "(if double_reverse_nibble_plane_high d then 2 else 0) =
        (if 5 \<le> d then 2 else 0)"
      by (simp add: double_reverse_nibble_planes_exact)
  qed
  have left_word:
    "push_bit 1 (drop_bit 8 ?p4 AND ?lanes) =
      int (double_reverse_pack16
        (double_reverse_nibble_source_left source_digits))"
    unfolding lh left_source
    by (rule double_reverse_pack16_selector_weight) simp_all
  let ?right_predicate = "\<lambda>r c. (r mod 5 = 3 \<or> r mod 5 = 4) \<or>
    (r mod 5 = 2 \<and> 5 \<le> c)"
  let ?right_selector = "\<lambda>r c. if ?right_predicate r c then 1 else 0"
  have right_source:
    "double_reverse_nibble_source_right source_digits =
      map2 ?right_selector ?rights ?centers"
  proof -
    show ?thesis
      unfolding double_reverse_nibble_source_right_def
    proof (rule map_cong[OF refl])
      fix pair assume member: "pair \<in> set (zip ?rights ?centers)"
      obtain r c where pair: "pair = (r, c)" by (cases pair) simp
      have r_member: "r \<in> set ?rights" and c_member: "c \<in> set ?centers"
        using member unfolding pair by (auto dest: set_zip_leftD set_zip_rightD)
      have rb: "r < 10" and cb: "c < 10"
        using decimal r_member c_member by (auto dest: in_set_takeD in_set_dropD)
      show "case_prod (\<lambda>r c. if double_reverse_nibble_plane_mod_ge_three r \<or>
          (double_reverse_nibble_plane_mod_equals_two r \<and>
            double_reverse_nibble_plane_high c) then 1 else 0) pair =
        case_prod ?right_selector pair"
        using pair rb cb by (simp add: double_reverse_nibble_planes_exact)
    qed
  qed
  have right_fusion:
    "map2 (\<or>) (map (\<lambda>d. d mod 5 = 3 \<or> d mod 5 = 4) ?rights)
      (map2 (\<and>) (map (\<lambda>d. d mod 5 = 2) ?rights)
        (map (\<lambda>d. 5 \<le> d) ?centers)) =
      map2 ?right_predicate ?rights ?centers"
  proof -
    have same_length: "length ?rights = length ?centers"
      using width by (simp; arith)
    show ?thesis
      by (rule double_reverse_map2_nested_aligned_maps[OF same_length])
  qed
  have right_word:
    "(?p1 AND ?lanes) OR ((?p3 AND ?lanes) AND
        (drop_bit 4 ?p4 AND ?lanes)) =
      int (double_reverse_pack16
        (double_reverse_nibble_source_right source_digits))"
    using right[unfolded right_fusion]
    by (simp add: right_source double_reverse_pack16_bits_eq_pack16
        map_map comp_def case_prod_unfold)
  let ?overflow_bits = "map2 (\<and>)
      (map (\<lambda>d. d mod 5 = 2) ?centers)
      (map (\<lambda>d. 5 \<le> d) ?lefts)"
  have overflow_word:
    "(drop_bit 4 ?p3 AND ?lanes) AND
        (drop_bit 8 ?p4 AND ?lanes) =
      double_reverse_pack16_bits ?overflow_bits"
    using c3 lh
    by (simp add: double_reverse_pack16_bits_and)
  have overflow_source:
    "double_reverse_nibble_source_overflow source_digits =
      map2 (\<lambda>c l. if c mod 5 = 2 \<and> 5 \<le> l then 10 else 0)
        ?centers ?lefts"
  proof -
    show ?thesis
      unfolding double_reverse_nibble_source_overflow_def
    proof (rule map_cong[OF refl])
      fix pair assume member: "pair \<in> set (zip ?centers ?lefts)"
      obtain c l where pair: "pair = (c, l)" by (cases pair) simp
      have c_member: "c \<in> set ?centers" and l_member: "l \<in> set ?lefts"
        using member unfolding pair by (auto dest: set_zip_leftD set_zip_rightD)
      have cb: "c < 10" and lb: "l < 10"
        using decimal c_member l_member by (auto dest: in_set_takeD in_set_dropD)
      show "case_prod (\<lambda>c l. if double_reverse_nibble_plane_mod_equals_two c \<and>
          double_reverse_nibble_plane_high l then 10 else 0) pair =
        case_prod (\<lambda>c l. if c mod 5 = 2 \<and> 5 \<le> l then 10 else 0) pair"
        using pair cb lb by (simp add: double_reverse_nibble_planes_exact)
    qed
  qed
  have overflow_fusion:
    "?overflow_bits =
      map2 (\<lambda>c l. (c mod 5 = 2) \<and> (5 \<le> l)) ?centers ?lefts"
    by (simp add: zip_map_map map_map comp_def case_prod_unfold)
  have correction_disjoint:
    "push_bit 3 (double_reverse_pack16_bits ?overflow_bits) AND
       push_bit 1 (double_reverse_pack16_bits ?overflow_bits) = 0"
    by (rule double_reverse_pack16_shifted_disjoint) simp_all
  have correction_lanes:
    "push_bit 3 (double_reverse_pack16_bits ?overflow_bits) OR
       push_bit 1 (double_reverse_pack16_bits ?overflow_bits) =
      int (double_reverse_pack16
        (map (\<lambda>b. if b then 10 else 0) ?overflow_bits))"
  proof -
    have add_bound:
      "\<forall>i<length ?overflow_bits.
        (map (\<lambda>b. if b then 8 else 0) ?overflow_bits) ! i +
        (map (\<lambda>b. if b then 2 else 0) ?overflow_bits) ! i < (16::nat)"
      by (auto simp: nth_map)
    have add:
      "int (double_reverse_pack16
          (map2 (+) (map (\<lambda>b. if b then 8 else 0) ?overflow_bits)
            (map (\<lambda>b. if b then 2 else 0) ?overflow_bits))) =
        push_bit 3 (double_reverse_pack16_bits ?overflow_bits) +
        push_bit 1 (double_reverse_pack16_bits ?overflow_bits)"
      using double_reverse_pack16_add_no_lane_carry_int[of
          "map (\<lambda>b. if b then 8 else 0) ?overflow_bits"
          "map (\<lambda>b. if b then 2 else 0) ?overflow_bits"]
        add_bound
        double_reverse_pack16_selector_weight[where shift=3 and weight=8
          and selector="id" and digits="?overflow_bits"]
        double_reverse_pack16_selector_weight[where shift=1 and weight=2
          and selector="id" and digits="?overflow_bits"]
      by (simp add: id_def)
    have disjunctive:
      "push_bit 3 (double_reverse_pack16_bits ?overflow_bits) +
         push_bit 1 (double_reverse_pack16_bits ?overflow_bits) =
       push_bit 3 (double_reverse_pack16_bits ?overflow_bits) OR
         push_bit 1 (double_reverse_pack16_bits ?overflow_bits)"
      by (rule disjunctive_add_eq_or[OF correction_disjoint])
    have weighted_sum:
      "map2 (+) (map (\<lambda>b. if b then 8 else 0) ?overflow_bits)
          (map (\<lambda>b. if b then 2 else 0) ?overflow_bits) =
        map (\<lambda>b. if b then (10::nat) else 0) ?overflow_bits"
      by (rule double_reverse_boolean_weight_add) simp
    have packed_sum:
      "int (double_reverse_pack16
          (map (\<lambda>b. if b then 10 else 0) ?overflow_bits)) =
        push_bit 3 (double_reverse_pack16_bits ?overflow_bits) +
        push_bit 1 (double_reverse_pack16_bits ?overflow_bits)"
      using add by (simp only: weighted_sum)
    show ?thesis by (rule sym[OF trans[OF packed_sum disjunctive]])
  qed
  have correction_word:
    "push_bit 3 ((drop_bit 4 ?p3 AND ?lanes) AND
        (drop_bit 8 ?p4 AND ?lanes)) OR
       push_bit 1 ((drop_bit 4 ?p3 AND ?lanes) AND
        (drop_bit 8 ?p4 AND ?lanes)) =
      int (double_reverse_pack16
        (double_reverse_nibble_source_overflow source_digits))"
    unfolding overflow_word overflow_fusion
    using correction_lanes[unfolded overflow_fusion]
    by (simp add: overflow_source double_reverse_pack16_bits_eq_pack16
        map_map comp_def case_prod_unfold)
  have component_lengths:
    "length (double_reverse_nibble_source_base source_digits) = ?m"
    "length (double_reverse_nibble_source_left source_digits) = ?m"
    "length (double_reverse_nibble_source_right source_digits) = ?m"
    using width
    by (simp_all add: double_reverse_nibble_source_base_def
        double_reverse_nibble_source_left_def
        double_reverse_nibble_source_right_def)
  have candidate_length:
    "length (double_reverse_nibble_source_candidate source_digits) = ?m"
    using width component_lengths
    by (simp add: double_reverse_nibble_source_candidate_def)
  have base_left_bound:
    "\<forall>i<length (double_reverse_nibble_source_base source_digits).
       double_reverse_nibble_source_base source_digits ! i +
       double_reverse_nibble_source_left source_digits ! i < (16::nat)"
  proof (intro allI impI)
    fix i :: nat
    assume index: "i < length (double_reverse_nibble_source_base source_digits)"
    have row_index: "i < ?m"
      using index component_lengths(1) by simp
    have center_index: "i + 1 < length source_digits" and
      left_index: "i + 2 < length source_digits"
      using row_index by arith+
    have center_decimal: "source_digits ! (i + 1) < 10"
      by (rule list_ball_nth[OF center_index decimal])
    have left_decimal: "source_digits ! (i + 2) < 10"
      by (rule list_ball_nth[OF left_index decimal])
    have base_cell:
      "double_reverse_nibble_source_base source_digits ! i =
        double_reverse_nibble_base (source_digits ! (i + 1))"
      using row_index by (simp add: double_reverse_nibble_source_base_def
          nth_take nth_drop)
    have left_cell:
      "double_reverse_nibble_source_left source_digits ! i \<le> 2"
      using row_index left_index
      by (simp add: double_reverse_nibble_source_left_def nth_take nth_drop
          split: if_splits)
    have base_bound: "double_reverse_nibble_base (source_digits ! (i + 1)) \<le> 8"
      by (rule double_reverse_nibble_base_at_most_eight[OF center_decimal])
    show "double_reverse_nibble_source_base source_digits ! i +
        double_reverse_nibble_source_left source_digits ! i < (16::nat)"
      using base_cell left_cell base_bound by arith
  qed
  have candidate_bound:
    "\<forall>i<?m. double_reverse_nibble_source_candidate source_digits ! i < (16::nat)"
    using double_reverse_nibble_source_candidate_bounds[OF width decimal]
    by blast
  have base_left_pack:
    "int (double_reverse_pack16
        (map2 (+) (double_reverse_nibble_source_base source_digits)
          (double_reverse_nibble_source_left source_digits))) =
      int (double_reverse_pack16
        (double_reverse_nibble_source_base source_digits)) +
      int (double_reverse_pack16
        (double_reverse_nibble_source_left source_digits))"
  proof -
    have same_length:
      "length (double_reverse_nibble_source_base source_digits) =
        length (double_reverse_nibble_source_left source_digits)"
      using component_lengths(1) component_lengths(2) by simp
    show ?thesis
      by (rule double_reverse_pack16_add_no_lane_carry_int
          [OF same_length base_left_bound])
  qed
  have candidate_pack:
    "int (double_reverse_pack16
        (double_reverse_nibble_source_candidate source_digits)) =
      int (double_reverse_pack16
        (double_reverse_nibble_source_base source_digits)) +
      int (double_reverse_pack16
        (double_reverse_nibble_source_left source_digits)) +
      int (double_reverse_pack16
        (double_reverse_nibble_source_right source_digits))"
  proof -
    have final_bound:
      "\<forall>i<length (map2 (+)
          (double_reverse_nibble_source_base source_digits)
          (double_reverse_nibble_source_left source_digits)).
        map2 (+) (double_reverse_nibble_source_base source_digits)
          (double_reverse_nibble_source_left source_digits) ! i +
        double_reverse_nibble_source_right source_digits ! i < (16::nat)"
    proof (intro allI impI)
      fix i :: nat
      assume index: "i < length (map2 (+)
        (double_reverse_nibble_source_base source_digits)
        (double_reverse_nibble_source_left source_digits))"
      have row_index: "i < ?m"
        using index component_lengths by simp
      have candidate_cell:
        "double_reverse_nibble_source_candidate source_digits ! i < (16::nat)"
        using candidate_bound row_index by blast
      show "map2 (+) (double_reverse_nibble_source_base source_digits)
          (double_reverse_nibble_source_left source_digits) ! i +
          double_reverse_nibble_source_right source_digits ! i < (16::nat)"
        using candidate_cell row_index component_lengths
        by (simp add: double_reverse_nibble_source_candidate_def)
    qed
    have packed:
      "int (double_reverse_pack16
          (map2 (+)
            (map2 (+) (double_reverse_nibble_source_base source_digits)
              (double_reverse_nibble_source_left source_digits))
            (double_reverse_nibble_source_right source_digits))) =
        int (double_reverse_pack16
          (map2 (+) (double_reverse_nibble_source_base source_digits)
            (double_reverse_nibble_source_left source_digits))) +
        int (double_reverse_pack16
          (double_reverse_nibble_source_right source_digits))"
      by (rule double_reverse_pack16_add_no_lane_carry_int
          [OF _ final_bound]) (simp add: component_lengths)
    show ?thesis
      using packed base_left_pack
      by (simp add: double_reverse_nibble_source_candidate_def)
  qed
  have candidate_word:
    "((push_bit 1 (drop_bit 4 ?p1 AND ?lanes) OR
        push_bit 2 (drop_bit 4 ?p2 AND ?lanes)) OR
        push_bit 3 (drop_bit 4 ?p3 AND ?lanes)) +
       push_bit 1 (drop_bit 8 ?p4 AND ?lanes) +
       ((?p1 AND ?lanes) OR ((?p3 AND ?lanes) AND
         (drop_bit 4 ?p4 AND ?lanes))) =
      int (double_reverse_pack16
        (double_reverse_nibble_source_candidate source_digits))"
    using c1 c2 c3 base_or base_pack left_word right_word candidate_pack
    by (simp add: algebra_simps)
  have result_order:
    "\<forall>i<length (double_reverse_nibble_source_candidate source_digits).
       double_reverse_nibble_source_overflow source_digits ! i \<le>
       double_reverse_nibble_source_candidate source_digits ! i"
    unfolding candidate_length
    using double_reverse_nibble_source_candidate_bounds[OF width decimal] by blast
  have result_upper:
    "\<forall>i<length (double_reverse_nibble_source_candidate source_digits).
       double_reverse_nibble_source_candidate source_digits ! i < (16::nat)"
    unfolding candidate_length
    using double_reverse_nibble_source_candidate_bounds[OF width decimal] by blast
  have result_lengths:
    "length (double_reverse_nibble_source_candidate source_digits) =
        length (double_reverse_nibble_source_overflow source_digits)"
    using width
    by (simp add: double_reverse_nibble_source_candidate_def
        double_reverse_nibble_source_overflow_def
        double_reverse_nibble_source_base_def
        double_reverse_nibble_source_left_def
        double_reverse_nibble_source_right_def)
  have result_pack:
    "int (double_reverse_pack16
       (double_reverse_nibble_source_result source_digits)) =
      int (double_reverse_pack16
        (double_reverse_nibble_source_candidate source_digits)) -
      int (double_reverse_pack16
        (double_reverse_nibble_source_overflow source_digits))"
    unfolding double_reverse_nibble_source_result_def
    by (rule double_reverse_pack16_sub_no_lane_borrow_int
        [OF result_lengths result_order result_upper])
  show ?thesis
    unfolding double_reverse_packed_diagonal_word_step_def
      double_reverse_packed_diagonal_state_step_def Let_def lanes
    by (simp only: candidate_word[unfolded or.assoc] correction_word result_pack)
qed

lemma double_reverse_packed_diagonal_scalar_step_reverse:
  "double_reverse_packed_diagonal_scalar_step source_digits =
    rev (double_reverse_nibble_row_step (rev source_digits))"
proof (rule nth_equalityI)
  show "length (double_reverse_packed_diagonal_scalar_step source_digits) =
      length (rev (double_reverse_nibble_row_step (rev source_digits)))"
    by (simp add: double_reverse_packed_diagonal_scalar_step_def
        double_reverse_nibble_row_step_length)
next
  fix i :: nat
  assume index:
    "i < length (double_reverse_packed_diagonal_scalar_step source_digits)"
  then have bound: "i < length source_digits - 2"
    by (simp add: double_reverse_packed_diagonal_scalar_step_def)
  let ?j = "length source_digits - 2 - Suc i"
  have row_bound: "?j + 2 < length source_digits"
    using bound by arith
  have output_index: "?j < length source_digits - 2" using row_bound by arith
  have reverse_indices:
    "length source_digits - Suc ?j = i+2"
    "length source_digits - Suc (?j+1) = i+1"
    "length source_digits - Suc (?j+2) = i"
    using bound by arith+
  have row_indices: "?j < length source_digits" "?j+1 < length source_digits"
    "?j+2 < length source_digits" using row_bound by arith+
  have rev0: "rev source_digits ! ?j = source_digits ! (i+2)"
    by (simp only: rev_nth[OF row_indices(1)] reverse_indices(1))
  have rev1: "rev source_digits ! (?j+1) = source_digits ! (i+1)"
    by (simp only: rev_nth[OF row_indices(2)] reverse_indices(2))
  have rev2: "rev source_digits ! (?j+2) = source_digits ! i"
    by (simp only: rev_nth[OF row_indices(3)] reverse_indices(3))
  have row_cell:
    "double_reverse_nibble_row_step (rev source_digits) ! ?j =
      double_reverse_nibble_lane_result
        (source_digits ! (i+2)) (source_digits ! (i+1))
        (source_digits ! i)"
    using output_index rev0 rev1 rev2
    by (simp add: double_reverse_nibble_row_step_def)
  show "double_reverse_packed_diagonal_scalar_step source_digits ! i =
      rev (double_reverse_nibble_row_step (rev source_digits)) ! i"
    using bound row_cell
    by (simp add: double_reverse_packed_diagonal_scalar_step_def
        rev_nth double_reverse_nibble_row_step_length)
qed

theorem double_reverse_packed_diagonal_word_step_refines_stencil:
  assumes width: "2 \<le> length source_digits"
      and decimal: "\<forall>d\<in>set source_digits. d < 10"
  shows "double_reverse_packed_diagonal_word_step source_digits =
    int (double_reverse_pack16
      (rev (double_reverse_spacetime_step (rev source_digits))))"
proof -
  have row_decimal:
    "double_reverse_decimal_row (rev source_digits)"
    using decimal
    by (simp add: double_reverse_decimal_row_set)
  show ?thesis
    using double_reverse_packed_diagonal_word_step_exact[OF width decimal]
      double_reverse_nibble_source_result_scalar_exact
      double_reverse_packed_diagonal_scalar_step_reverse
      double_reverse_nibble_row_step_refines_spacetime[OF row_decimal]
    by simp
qed


definition double_reverse_unpack16 :: "nat \<Rightarrow> int \<Rightarrow> nat list" where
  "double_reverse_unpack16 width packed_word =
    map (\<lambda>i. nat (double_reverse_packed_nibble_value packed_word i))
      [0..<width]"

lemma double_reverse_unpack16_pack16:
  assumes bounded: "\<forall>d\<in>set digits. d < 16"
  shows "double_reverse_unpack16 (length digits)
      (int (double_reverse_pack16 digits)) = digits"
proof (rule nth_equalityI)
  show "length (double_reverse_unpack16 (length digits)
      (int (double_reverse_pack16 digits))) = length digits"
    by (simp add: double_reverse_unpack16_def)
next
  fix i :: nat
  assume index: "i < length
      (double_reverse_unpack16 (length digits)
        (int (double_reverse_pack16 digits)))"
  then have index': "i < length digits"
    by (simp add: double_reverse_unpack16_def)
  have nibble:
    "double_reverse_packed_nibble_value
       (int (double_reverse_pack16 digits)) i = int (digits ! i)"
    by (rule double_reverse_pack16_nibble_value[OF bounded index'])
  show "double_reverse_unpack16 (length digits)
      (int (double_reverse_pack16 digits)) ! i = digits ! i"
    using index' nibble
    by (simp add: double_reverse_unpack16_def)
qed

fun double_reverse_packed_diagonal_integer_power ::
    "nat \<Rightarrow> nat list \<Rightarrow> int" where
  "double_reverse_packed_diagonal_integer_power 0 source_digits =
    int (double_reverse_pack16 source_digits)"
| "double_reverse_packed_diagonal_integer_power (Suc steps) source_digits =
    double_reverse_packed_diagonal_word_step
      (double_reverse_unpack16
        (length source_digits - 2*steps)
        (double_reverse_packed_diagonal_integer_power steps source_digits))"

fun double_reverse_packed_diagonal_state_power ::
    "nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int" where
  "double_reverse_packed_diagonal_state_power 0 width packed_word = packed_word"
| "double_reverse_packed_diagonal_state_power (Suc steps) width packed_word =
    double_reverse_packed_diagonal_state_step
      (width - 2*steps)
      (double_reverse_packed_diagonal_state_power steps width packed_word)"

theorem double_reverse_packed_diagonal_integer_power_exact:
  assumes extent: "2*steps \<le> length source_digits"
      and decimal: "\<forall>d\<in>set source_digits. d < 10"
  shows "double_reverse_packed_diagonal_integer_power steps source_digits =
    int (double_reverse_pack16
      (rev (double_reverse_spacetime_power steps (rev source_digits))))"
  using extent decimal
proof (induction steps arbitrary: source_digits)
  case "0"
  then show ?case by simp
next
  case (Suc steps)
  have prior_extent: "2*steps \<le> length source_digits"
    using Suc.prems(1) by arith
  have prior:
    "double_reverse_packed_diagonal_integer_power steps source_digits =
      int (double_reverse_pack16
        (rev (double_reverse_spacetime_power steps (rev source_digits))))"
    by (rule Suc.IH[OF prior_extent Suc.prems(2)])
  have row_decimal:
    "double_reverse_decimal_row (rev source_digits)"
    using Suc.prems(2)
    by (simp add: double_reverse_decimal_row_set)
  have previous_decimal:
    "double_reverse_decimal_row
      (double_reverse_spacetime_power steps (rev source_digits))"
    by (rule double_reverse_spacetime_power_preserves_decimal[OF row_decimal])
  have previous_length:
    "length (double_reverse_spacetime_power steps (rev source_digits)) =
        length source_digits - 2*steps"
    using double_reverse_spacetime_power_length[of steps "rev source_digits"]
    by simp
  have previous_bounded:
    "\<forall>d\<in>set
      (rev (double_reverse_spacetime_power steps (rev source_digits))). d < 16"
    using previous_decimal
    by (auto simp: double_reverse_decimal_row_set)
  have decoded:
    "double_reverse_unpack16 (length source_digits - 2*steps)
      (double_reverse_packed_diagonal_integer_power steps source_digits) =
      rev (double_reverse_spacetime_power steps (rev source_digits))"
    using prior previous_length previous_bounded
      double_reverse_unpack16_pack16[OF previous_bounded]
    by simp
  have row_width:
    "2 \<le> length
      (rev (double_reverse_spacetime_power steps (rev source_digits)))"
    using Suc.prems(1) previous_length by (simp only: length_rev; arith)
  have packed_row:
    "double_reverse_packed_diagonal_word_step
       (rev (double_reverse_spacetime_power steps (rev source_digits))) =
      int (double_reverse_pack16
        (rev (double_reverse_spacetime_step
          (double_reverse_spacetime_power steps (rev source_digits)))))"
    using double_reverse_packed_diagonal_word_step_refines_stencil[OF row_width]
      previous_decimal by (simp add: double_reverse_decimal_row_set)
  show ?case
    using decoded packed_row
    by (simp add: double_reverse_spacetime_power.simps)
qed

theorem double_reverse_packed_diagonal_state_power_matches_integer_power:
  assumes extent: "2*steps \<le> length source_digits"
      and decimal: "\<forall>d\<in>set source_digits. d < 10"
  shows "double_reverse_packed_diagonal_state_power steps (length source_digits)
      (int (double_reverse_pack16 source_digits)) =
    double_reverse_packed_diagonal_integer_power steps source_digits"
  using extent decimal
proof (induction steps arbitrary: source_digits)
  case "0"
  then show ?case by simp
next
  case (Suc steps)
  have prior_extent: "2*steps \<le> length source_digits"
    using Suc.prems(1) by arith
  have prior:
    "double_reverse_packed_diagonal_state_power steps (length source_digits)
        (int (double_reverse_pack16 source_digits)) =
      double_reverse_packed_diagonal_integer_power steps source_digits"
    by (rule Suc.IH[OF prior_extent Suc.prems(2)])
  let ?row = "rev (double_reverse_spacetime_power steps (rev source_digits))"
  have previous_exact:
    "double_reverse_packed_diagonal_integer_power steps source_digits =
      int (double_reverse_pack16 ?row)"
    by (rule double_reverse_packed_diagonal_integer_power_exact
        [OF prior_extent Suc.prems(2)])
  have previous_decimal:
    "double_reverse_decimal_row
      (double_reverse_spacetime_power steps (rev source_digits))"
    by (rule double_reverse_spacetime_power_preserves_decimal)
      (use Suc.prems(2) in \<open>simp add: double_reverse_decimal_row_set\<close>)
  have row_bounded: "\<forall>d\<in>set ?row. d < 16"
    using previous_decimal
    by (auto simp: double_reverse_decimal_row_set)
  have row_length:
    "length ?row = length source_digits - 2*steps"
    using double_reverse_spacetime_power_length[of steps "rev source_digits"]
    by simp
  have decoded:
    "double_reverse_unpack16 (length source_digits - 2*steps)
      (double_reverse_packed_diagonal_integer_power steps source_digits) = ?row"
    using previous_exact row_length row_bounded
      double_reverse_unpack16_pack16[OF row_bounded]
    by simp
  have current_step:
    "double_reverse_packed_diagonal_state_step
        (length source_digits - 2*steps)
        (double_reverse_packed_diagonal_integer_power steps source_digits) =
      double_reverse_packed_diagonal_word_step
        (double_reverse_unpack16 (length source_digits - 2*steps)
          (double_reverse_packed_diagonal_integer_power steps source_digits))"
    using previous_exact row_length decoded
    by (simp add: double_reverse_packed_diagonal_word_step_def)
  show ?case
    unfolding double_reverse_packed_diagonal_state_power.simps
      double_reverse_packed_diagonal_integer_power.simps
    using prior current_step by simp
qed

corollary double_reverse_packed_diagonal_integer_power_high_first_exact:
  assumes extent: "2*steps \<le> length row"
      and decimal: "\<forall>d\<in>set row. d < 10"
  shows "double_reverse_packed_diagonal_integer_power steps (rev row) =
    int (double_reverse_pack16
      (rev (double_reverse_spacetime_power steps row)))"
  using double_reverse_packed_diagonal_integer_power_exact[of steps "rev row"]
    extent decimal
  by simp

corollary double_reverse_packed_diagonal_state_power_high_first_exact:
  assumes extent: "2*steps \<le> length row"
      and decimal: "\<forall>d\<in>set row. d < 10"
  shows "double_reverse_packed_diagonal_state_power steps (length (rev row))
      (int (double_reverse_pack16 (rev row))) =
    int (double_reverse_pack16
      (rev (double_reverse_spacetime_power steps row)))"
proof -
  have reversed_extent: "2*steps \<le> length (rev row)"
    using extent by simp
  have reversed_decimal: "\<forall>d\<in>set (rev row). d < 10"
    using decimal by auto
  have state_matches:
    "double_reverse_packed_diagonal_state_power steps (length (rev row))
        (int (double_reverse_pack16 (rev row))) =
      double_reverse_packed_diagonal_integer_power steps (rev row)"
    by (rule double_reverse_packed_diagonal_state_power_matches_integer_power
        [OF reversed_extent reversed_decimal])
  have integer_exact:
    "double_reverse_packed_diagonal_integer_power steps (rev row) =
      int (double_reverse_pack16
        (rev (double_reverse_spacetime_power steps row)))"
    by (rule double_reverse_packed_diagonal_integer_power_high_first_exact
        [OF extent decimal])
  show ?thesis
    by (rule trans[OF state_matches integer_exact])
qed


theorem double_reverse_packed_diagonal_causal_window_exact:
  assumes extent: "start + window_width + 2*steps \<le> length source"
      and decimal: "\<forall>d\<in>set source. d < 10"
  shows "double_reverse_packed_diagonal_state_power steps
      (length (rev (take (window_width + 2*steps) (drop start source))))
      (int (double_reverse_pack16
        (rev (take (window_width + 2*steps) (drop start source))))) =
    int (double_reverse_pack16
      (rev (take window_width
        (drop start (double_reverse_spacetime_power steps source)))))"
proof -
  let ?row = "take (window_width + 2*steps) (drop start source)"
  have row_decimal: "\<forall>d\<in>set ?row. d < 10"
    using decimal by (auto dest: in_set_takeD in_set_dropD)
  have row_length: "length ?row = window_width + 2*steps"
    using extent by simp
  have row_extent: "2*steps \<le> length ?row" using row_length by arith
  have power_exact:
    "double_reverse_packed_diagonal_state_power steps (length (rev ?row))
        (int (double_reverse_pack16 (rev ?row))) =
      int (double_reverse_pack16
        (rev (double_reverse_spacetime_power steps ?row)))"
    by (rule double_reverse_packed_diagonal_state_power_high_first_exact
        [OF row_extent row_decimal])
  have window_exact:
    "double_reverse_spacetime_power steps ?row =
      take window_width
        (drop start (double_reverse_spacetime_power steps source))"
    by (rule double_reverse_spacetime_window_power[OF extent])
  show ?thesis using power_exact window_exact by simp
qed

corollary double_reverse_packed_diagonal_helper_window_refines:
  assumes width: "length row = 4*steps"
      and decimal: "\<forall>d\<in>set row. d < 10"
  shows "double_reverse_packed_diagonal_state_power steps (length (rev row))
      (int (double_reverse_pack16 (rev row))) =
    int (double_reverse_pack16
      (rev (double_reverse_spacetime_power steps row)))"
proof (rule double_reverse_packed_diagonal_state_power_high_first_exact)
  show "2*steps \<le> length row" using width by arith
  show "\<forall>d\<in>set row. d < 10" by (rule decimal)
qed

corollary double_reverse_packed_diagonal_helper_output_exact:
  assumes width: "length row = 4*steps"
      and decimal: "\<forall>d\<in>set row. d < 10"
  shows "rev (double_reverse_unpack16 (2*steps)
      (double_reverse_packed_diagonal_state_power steps (length (rev row))
        (int (double_reverse_pack16 (rev row))))) =
    double_reverse_spacetime_power steps row"
proof -
  have power:
    "double_reverse_packed_diagonal_state_power steps (length (rev row))
        (int (double_reverse_pack16 (rev row))) =
      int (double_reverse_pack16
        (rev (double_reverse_spacetime_power steps row)))"
    by (rule double_reverse_packed_diagonal_state_power_high_first_exact)
      (simp_all add: width decimal)
  have output_decimal:
    "double_reverse_decimal_row
      (double_reverse_spacetime_power steps row)"
    by (rule double_reverse_spacetime_power_preserves_decimal)
      (use decimal in \<open>simp add: double_reverse_decimal_row_set\<close>)
  have output_bound:
    "\<forall>d\<in>set
      (rev (double_reverse_spacetime_power steps row)). d < 16"
    using output_decimal
    by (auto simp: double_reverse_decimal_row_set)
  have output_length:
    "length (double_reverse_spacetime_power steps row) = 2*steps"
    using double_reverse_spacetime_power_length[of steps row] width
    by simp
  have decoded:
    "double_reverse_unpack16 (2*steps)
      (int (double_reverse_pack16
        (rev (double_reverse_spacetime_power steps row)))) =
      rev (double_reverse_spacetime_power steps row)"
    using double_reverse_unpack16_pack16[OF output_bound]
      output_length by simp
  show ?thesis using power decoded by simp
qed

corollary double_reverse_packed_diagonal_causal_window_digits_exact:
  assumes extent: "start + window_width + 2*steps \<le> length source"
      and decimal: "\<forall>d\<in>set source. d < 10"
  shows "rev (double_reverse_unpack16 window_width
      (double_reverse_packed_diagonal_state_power steps
        (length (rev (take (window_width + 2*steps) (drop start source))))
        (int (double_reverse_pack16
          (rev (take (window_width + 2*steps) (drop start source))))))) =
    take window_width
      (drop start (double_reverse_spacetime_power steps source))"
proof -
  let ?row = "take (window_width + 2*steps) (drop start source)"
  let ?output = "take window_width
    (drop start (double_reverse_spacetime_power steps source))"
  have powered_decimal:
    "double_reverse_decimal_row
      (double_reverse_spacetime_power steps source)"
    by (rule double_reverse_spacetime_power_preserves_decimal)
      (use decimal in \<open>simp add: double_reverse_decimal_row_set\<close>)
  have output_decimal: "\<forall>d\<in>set ?output. d < 10"
    using powered_decimal
    by (auto simp: double_reverse_decimal_row_set dest: in_set_takeD in_set_dropD)
  have output_length: "length ?output = window_width"
    using extent double_reverse_spacetime_power_length[of steps source]
    by simp
  have output_packed:
    "double_reverse_packed_diagonal_state_power steps (length (rev ?row))
        (int (double_reverse_pack16 (rev ?row))) =
      int (double_reverse_pack16 (rev ?output))"
    by (rule double_reverse_packed_diagonal_causal_window_exact[OF extent decimal])
  have output_bounded: "\<forall>d\<in>set (rev ?output). d < 16"
    using output_decimal by auto
  have decoded:
    "double_reverse_unpack16 window_width
       (int (double_reverse_pack16 (rev ?output))) = rev ?output"
    using double_reverse_unpack16_pack16[OF output_bounded]
      output_length by simp
  show ?thesis using output_packed decoded by simp
qed

ML \<open>
  val checked = @{thms
    double_reverse_packed_nibble_planes_source_exact
    double_reverse_packed_nibble_source_planes_tuple
    double_reverse_packed_source_selector_slice
    double_reverse_pack16_add_no_lane_carry_int
    double_reverse_pack16_sub_no_lane_borrow_int
    double_reverse_packed_diagonal_word_step_exact
    double_reverse_packed_diagonal_word_step_refines_stencil
    double_reverse_unpack16_pack16
    double_reverse_packed_diagonal_integer_power_exact
    double_reverse_packed_diagonal_integer_power_high_first_exact
    double_reverse_packed_diagonal_state_power_matches_integer_power
    double_reverse_packed_diagonal_state_power_high_first_exact
    double_reverse_packed_diagonal_causal_window_exact
    double_reverse_packed_diagonal_helper_window_refines
    double_reverse_packed_diagonal_helper_output_exact
    double_reverse_packed_diagonal_causal_window_digits_exact};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Packed diagonal word refinement depends on an oracle";
\<close>

end
