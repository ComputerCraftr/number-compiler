theory Comma_CRT_Cofactor_Selection
  imports Comma_Semantic_B1.Comma_CRT_Phase_Clock
begin

unbundle bit_operations_syntax

text \<open>
The four selector coordinates are the external CRT clock C4 x C3 x C7 x C11.
The weights below are CRT idempotents: each is one on its own coordinate and
zero on the other three.  A word cofactor is a pullback along that coordinate
replacement.  The word cofactor below lets the publisher build the ordered MDD directly
from cofactored children, without constructing a phase-indexed rank table.
\<close>

definition comma_phase_word_cofactor :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_phase_word_cofactor axis slot word =
    comma_phase_mask (\<lambda>phase. bit word (comma_crt_rebase axis slot phase))"

lemma comma_phase_word_cofactor_bounded:
  "take_bit 924 (comma_phase_word_cofactor axis slot word)=
    comma_phase_word_cofactor axis slot word"
  unfolding comma_phase_word_cofactor_def
  by (rule comma_symbolic_phase_mask_bounded)

lemma comma_phase_word_cofactor_bit:
  assumes phase: "phase<924"
  shows "bit (comma_phase_word_cofactor axis slot word) phase=
    bit word (comma_crt_rebase axis slot phase)"
  using phase by (simp add: comma_phase_word_cofactor_def comma_phase_mask_bit)

lemma comma_phase_word_cofactor_zero:
  "comma_phase_word_cofactor axis slot 0=0"
proof (rule bit_eqI)
  fix phase
  show "bit (comma_phase_word_cofactor axis slot 0) phase=bit (0::nat) phase"
    by (simp add: comma_phase_word_cofactor_def comma_phase_mask_bit)
qed

lemma comma_phase_word_cofactor_full:
  "comma_phase_word_cofactor axis slot (mask 924::nat)=(mask 924::nat)"
proof (rule bit_eqI)
  fix phase
  show "bit (comma_phase_word_cofactor axis slot (mask 924::nat)) phase=
      bit (mask 924::nat) phase"
  proof (cases "phase<924")
    case True
    have rebased: "comma_crt_rebase axis slot phase<924"
      by (rule comma_crt_rebase_bounded)
    show ?thesis using True rebased
      by (simp add: comma_phase_word_cofactor_def comma_phase_mask_bit
        bit_mask_iff possible_bit_nat simp_thms)
  next
    case False
    have bounded: "take_bit 924
        (comma_phase_word_cofactor axis slot (mask 924::nat))=
        comma_phase_word_cofactor axis slot (mask 924::nat)"
      by (rule comma_phase_word_cofactor_bounded)
    have left: "bit (comma_phase_word_cofactor axis slot (mask 924::nat)) phase=False"
      by (rule comma_symbolic_phase_bit_outside[OF bounded]) (use False in arith)
    have right: "bit (mask 924::nat) phase=False"
      using False by (simp add: bit_mask_iff possible_bit_nat simp_thms)
    show ?thesis using left right by simp
  qed
qed

lemma comma_phase_word_cofactor_selected:
  assumes axis: "axis<4" and slot: "slot<comma_crt_axis_radix axis"
    and phase: "phase<924"
    and selected: "slot=phase mod comma_crt_axis_radix axis"
  shows "bit (comma_phase_word_cofactor axis slot word) phase=bit word phase"
  using comma_crt_rebase_selected[OF axis slot selected] phase
  by (simp add: comma_phase_word_cofactor_bit)

lemma comma_phase_word_cofactor_reassemble:
  assumes axis: "axis<4"
  shows "comma_indexed_phase_union
      (\<lambda>slot phase. phase mod comma_crt_axis_radix axis=slot)
      (map (\<lambda>slot. comma_phase_word_cofactor axis slot word)
        [0..<comma_crt_axis_radix axis])=take_bit 924 word"
proof -
  let ?period = "comma_crt_axis_radix axis"
  let ?rows = "map (\<lambda>slot. comma_phase_word_cofactor axis slot word)
    [0..<?period]"
  let ?union = "comma_indexed_phase_union
    (\<lambda>slot phase. phase mod ?period=slot) ?rows"
  have positive: "0<?period"
    using comma_crt_axis_cases[OF axis] by (auto simp: comma_crt_axis_radix_def)
  have rows_length: "length ?rows=?period" by simp
  have union_bounded: "take_bit 924 ?union=?union"
    by (rule comma_indexed_phase_union_bounded)
  show ?thesis
  proof (rule bit_eqI)
    fix phase
    show "bit ?union phase=bit (take_bit 924 word) phase"
    proof (cases "phase<924")
      case True
      let ?slot = "phase mod ?period"
      have slot_bound: "?slot<?period" using positive by simp
      have selected:
        "comma_phase_member ?union phase=
          comma_phase_member (?rows!?slot) phase"
        by (rule comma_indexed_phase_union_select[OF positive rows_length])
      have row: "?rows!?slot=comma_phase_word_cofactor axis ?slot word"
        using slot_bound by simp
      have member: "comma_phase_member ?union phase=bit word phase"
        using selected row True axis slot_bound
        by (simp add: comma_phase_member_def
          comma_phase_word_cofactor_selected)
      show ?thesis using member True
        by (simp add: bit_take_bit_iff comma_phase_member_def)
    next
      case False
      have union_zero: "bit ?union phase=False"
        by (rule comma_symbolic_phase_bit_outside[OF union_bounded])
          (use False in arith)
      have word_zero: "bit (take_bit 924 word) phase=False"
        using False by (simp add: bit_take_bit_iff)
      show ?thesis using union_zero word_zero by simp
    qed
  qed
qed

lemma comma_phase_word_cofactor_same_axis_union:
  assumes axis: "axis<4" and slot: "slot<comma_crt_axis_radix axis"
    and row_length: "length rows=comma_crt_axis_radix axis"
  shows "comma_phase_word_cofactor axis slot
      (comma_indexed_phase_union
        (\<lambda>j phase. phase mod comma_crt_axis_radix axis=j) rows)=
    comma_phase_word_cofactor axis slot
      (rows!slot)"
proof -
  let ?q = "comma_crt_axis_radix axis"
  let ?rebase = "comma_crt_rebase axis slot"
  let ?source = "comma_indexed_phase_union
    (\<lambda>j phase. phase mod ?q=j) rows"
  have positive: "0<?q"
    using comma_crt_axis_cases[OF axis] by (auto simp: comma_crt_axis_radix_def)
  have q_divides: "?q dvd 924" by (rule comma_crt_axis_radices_divide_924[OF axis])
  have source_bounded: "take_bit 924 ?source=?source"
    by (rule comma_indexed_phase_union_bounded)
  have cofactor_bounded:
    "take_bit 924 (comma_phase_word_cofactor axis slot ?source)=
      comma_phase_word_cofactor axis slot ?source"
    by (rule comma_phase_word_cofactor_bounded)
  have row_cofactor_bounded:
    "take_bit 924 (comma_phase_word_cofactor axis slot (rows!slot))=
      comma_phase_word_cofactor axis slot (rows!slot)"
    by (rule comma_phase_word_cofactor_bounded)
  show ?thesis
  proof (rule bit_eqI)
    fix phase
    show "bit (comma_phase_word_cofactor axis slot ?source) phase=
      bit (comma_phase_word_cofactor axis slot (rows!slot)) phase"
    proof (cases "phase<924")
      case True
      have rebase_bound: "?rebase phase<924"
        by (rule comma_crt_rebase_bounded)
      have rebase_slot: "?rebase phase mod ?q=slot"
      proof -
        have "?rebase phase mod ?q=slot"
          using comma_crt_rebase_selected_axis[OF axis slot, of phase] .
        then show ?thesis .
      qed
      have selected:
        "comma_phase_member ?source (?rebase phase)=
          comma_phase_member (rows!((?rebase phase) mod ?q)) (?rebase phase)"
        by (rule comma_indexed_phase_union_select[OF positive row_length])
      have selected_row: "rows!((?rebase phase) mod ?q)=rows!slot"
        using rebase_slot by simp
      show ?thesis using True rebase_bound selected selected_row
        by (simp add: comma_phase_word_cofactor_bit comma_phase_member_def)
    next
      case False
      have left_zero: "bit (comma_phase_word_cofactor axis slot ?source) phase=False"
        by (rule comma_symbolic_phase_bit_outside[OF cofactor_bounded])
          (use False in arith)
      have right_zero:
        "bit (comma_phase_word_cofactor axis slot (rows!slot)) phase=False"
        by (rule comma_symbolic_phase_bit_outside[OF row_cofactor_bounded])
          (use False in arith)
      show ?thesis using left_zero right_zero by simp
    qed
  qed
qed

lemma comma_phase_word_cofactor_other_axis_union:
  assumes axis: "axis<4" and other: "other<4" and distinct: "axis\<noteq>other"
    and row_length: "length rows=comma_crt_axis_radix other"
  shows "comma_phase_word_cofactor axis slot
      (comma_indexed_phase_union
        (\<lambda>j phase. phase mod comma_crt_axis_radix other=j) rows)=
    comma_indexed_phase_union
      (\<lambda>j phase. phase mod comma_crt_axis_radix other=j)
      (map (comma_phase_word_cofactor axis slot) rows)"
proof -
  let ?q = "comma_crt_axis_radix other"
  let ?source = "comma_indexed_phase_union
    (\<lambda>j phase. phase mod ?q=j) rows"
  let ?target = "comma_indexed_phase_union
    (\<lambda>j phase. phase mod ?q=j)
      (map (comma_phase_word_cofactor axis slot) rows)"
  let ?rebase = "comma_crt_rebase axis slot"
  have positive: "0<?q"
    using comma_crt_axis_cases[OF other] by (auto simp: comma_crt_axis_radix_def)
  have source_bounded: "take_bit 924 ?source=?source"
    by (rule comma_indexed_phase_union_bounded)
  have target_bounded: "take_bit 924 ?target=?target"
    by (rule comma_indexed_phase_union_bounded)
  have cofactor_bounded:
    "take_bit 924 (comma_phase_word_cofactor axis slot ?source)=
      comma_phase_word_cofactor axis slot ?source"
    by (rule comma_phase_word_cofactor_bounded)
  show ?thesis
  proof (rule bit_eqI)
    fix phase
    show "bit (comma_phase_word_cofactor axis slot ?source) phase=bit ?target phase"
    proof (cases "phase<924")
      case True
      have rebase_bound: "?rebase phase<924"
        by (rule comma_crt_rebase_bounded)
      have rebase_slot:
        "?rebase phase mod ?q=phase mod ?q"
        using comma_crt_rebase_other_axis[OF axis other distinct, of slot phase] .
      have source_select:
        "comma_phase_member ?source (?rebase phase)=
          comma_phase_member (rows!((?rebase phase) mod ?q)) (?rebase phase)"
        by (rule comma_indexed_phase_union_select[OF positive row_length])
      have target_select:
        "comma_phase_member ?target phase=
          comma_phase_member ((map (comma_phase_word_cofactor axis slot) rows)!
            (phase mod ?q)) phase"
        by (rule comma_indexed_phase_union_select[OF positive])
          (simp add: row_length)
      have selected_row:
        "rows!((?rebase phase) mod ?q)=rows!(phase mod ?q)"
        using rebase_slot by simp
      have map_row:
        "(map (comma_phase_word_cofactor axis slot) rows)!(phase mod ?q)=
          comma_phase_word_cofactor axis slot (rows!(phase mod ?q))"
        using row_length True positive by simp
      show ?thesis using True rebase_bound source_select target_select
        selected_row map_row
        by (simp add: comma_phase_word_cofactor_bit comma_phase_member_def)
    next
      case False
      have left_zero: "bit (comma_phase_word_cofactor axis slot ?source) phase=False"
        by (rule comma_symbolic_phase_bit_outside[OF cofactor_bounded])
          (use False in arith)
      have right_zero: "bit ?target phase=False"
        by (rule comma_symbolic_phase_bit_outside[OF target_bounded])
          (use False in arith)
      show ?thesis using left_zero right_zero by simp
    qed
  qed
qed

lemma comma_phase_word_cofactor_same_axis_q:
  fixes axis q slot :: nat
  assumes axis: "axis<4" and radix: "q=comma_crt_axis_radix axis"
    and slot: "slot<q" and row_length: "length rows=q"
  shows "comma_phase_word_cofactor axis slot
      (comma_indexed_phase_union (\<lambda>j phase. phase mod q=j) rows)=
    comma_phase_word_cofactor axis slot (rows!slot)"
proof -
  have length: "length rows=comma_crt_axis_radix axis"
    using row_length radix by simp
  have slot_bound: "slot<comma_crt_axis_radix axis"
    using slot radix by simp
  show ?thesis
    using comma_phase_word_cofactor_same_axis_union[OF axis slot_bound length]
      radix by simp
qed

lemma comma_phase_word_cofactor_other_axis_q:
  fixes axis other q slot :: nat
  assumes axis: "axis<4" and other: "other<4" and distinct: "axis\<noteq>other"
    and radix: "q=comma_crt_axis_radix other"
    and row_length: "length rows=q"
  shows "comma_phase_word_cofactor axis slot
      (comma_indexed_phase_union (\<lambda>j phase. phase mod q=j) rows)=
    comma_indexed_phase_union (\<lambda>j phase. phase mod q=j)
      (map (comma_phase_word_cofactor axis slot) rows)"
proof -
  have length: "length rows=comma_crt_axis_radix other"
    using row_length radix by simp
  show ?thesis
    using comma_phase_word_cofactor_other_axis_union
      [OF axis other distinct length] radix by simp
qed

ML \<open>Comma_Fast_Kernel.report "CRT cofactor checkpoint=word-laws"\<close>

definition comma_crt_select4 :: "nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat" where
  "comma_crt_select4 period offset rows=rows!(offset mod period)"

definition comma_crt_select3 :: "nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat" where
  "comma_crt_select3 period offset rows=
    comma_indexed_phase_union (\<lambda>slot phase. phase mod 11=slot)
      (map (\<lambda>slot. comma_crt_select4 period
        ((offset+comma_crt_axis_weight 3*slot) mod period)
        (map (comma_phase_word_cofactor 3 slot) rows)) [0..<11])"

definition comma_crt_select2 :: "nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat" where
  "comma_crt_select2 period offset rows=
    comma_indexed_phase_union (\<lambda>slot phase. phase mod 7=slot)
      (map (\<lambda>slot. comma_crt_select3 period
        ((offset+comma_crt_axis_weight 2*slot) mod period)
        (map (comma_phase_word_cofactor 2 slot) rows)) [0..<7])"

definition comma_crt_select1 :: "nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat" where
  "comma_crt_select1 period offset rows=
    comma_indexed_phase_union (\<lambda>slot phase. phase mod 3=slot)
      (map (\<lambda>slot. comma_crt_select2 period
        ((offset+comma_crt_axis_weight 1*slot) mod period)
        (map (comma_phase_word_cofactor 1 slot) rows)) [0..<3])"

definition comma_crt_select0 :: "nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat" where
  "comma_crt_select0 period offset rows=
    comma_indexed_phase_union (\<lambda>slot phase. phase mod 4=slot)
      (map (\<lambda>slot. comma_crt_select1 period
        ((offset+comma_crt_axis_weight 0*slot) mod period)
        (map (comma_phase_word_cofactor 0 slot) rows)) [0..<4])"

lemma comma_crt_select4_equation:
  shows "comma_crt_select4 period offset rows=rows!(offset mod period)"
  by (simp add: comma_crt_select4_def)

lemma comma_crt_select3_equation:
  shows "comma_crt_select3 period offset rows=
    comma_indexed_phase_union (\<lambda>slot phase. phase mod 11=slot)
      (map (\<lambda>slot. comma_crt_select4 period
        ((offset+comma_crt_axis_weight 3*slot) mod period)
        (map (comma_phase_word_cofactor 3 slot) rows)) [0..<11])"
  by (simp add: comma_crt_select3_def)

lemma comma_crt_select2_equation:
  shows "comma_crt_select2 period offset rows=
    comma_indexed_phase_union (\<lambda>slot phase. phase mod 7=slot)
      (map (\<lambda>slot. comma_crt_select3 period
        ((offset+comma_crt_axis_weight 2*slot) mod period)
        (map (comma_phase_word_cofactor 2 slot) rows)) [0..<7])"
  by (simp add: comma_crt_select2_def)

lemma comma_crt_select1_equation:
  shows "comma_crt_select1 period offset rows=
    comma_indexed_phase_union (\<lambda>slot phase. phase mod 3=slot)
      (map (\<lambda>slot. comma_crt_select2 period
        ((offset+comma_crt_axis_weight 1*slot) mod period)
        (map (comma_phase_word_cofactor 1 slot) rows)) [0..<3])"
  by (simp add: comma_crt_select1_def)

lemma comma_crt_select0_equation:
  shows "comma_crt_select0 period offset rows=
    comma_indexed_phase_union (\<lambda>slot phase. phase mod 4=slot)
      (map (\<lambda>slot. comma_crt_select1 period
        ((offset+comma_crt_axis_weight 0*slot) mod period)
        (map (comma_phase_word_cofactor 0 slot) rows)) [0..<4])"
  by (simp add: comma_crt_select0_def)

lemma comma_crt_select4_bit:
  assumes positive: "0<period" and row_length: "length rows=period"
  shows "bit (comma_crt_select4 period offset rows) phase=
    bit (rows!(offset mod period)) phase"
  using positive row_length by (simp add: comma_crt_select4_def)

lemma comma_crt_cofactored_step_bit:
  fixes axis period q offset phase :: nat and rows :: "nat list"
    and lower :: "nat \<Rightarrow> nat list \<Rightarrow> nat"
  assumes axis: "axis<4"
    and radix: "q=comma_crt_axis_radix axis"
    and positive_period: "0<period"
    and row_length: "length rows=period"
    and phase: "phase<924"
    and lower_exact:
      "\<And>lower_offset lower_rows. length lower_rows=period \<Longrightarrow>
        bit (lower lower_offset lower_rows) phase=
          bit (lower_rows!((lower_offset+comma_crt_suffix (Suc axis) phase)
            mod period)) phase"
  shows "bit (comma_indexed_phase_union (\<lambda>slot phase. phase mod q=slot)
      (map (\<lambda>slot. lower ((offset+comma_crt_axis_weight axis*slot) mod period)
        (map (comma_phase_word_cofactor axis slot) rows)) [0..<q])) phase=
    bit (rows!((offset+comma_crt_suffix axis phase) mod period)) phase"
proof -
  have positive_q: "0<q"
    using comma_crt_axis_cases[OF axis] radix
    by (auto simp: comma_crt_axis_radix_def)
  let ?children = "map (\<lambda>slot.
    lower ((offset+comma_crt_axis_weight axis*slot) mod period)
      (map (comma_phase_word_cofactor axis slot) rows)) [0..<q]"
  let ?result = "comma_indexed_phase_union (\<lambda>slot phase. phase mod q=slot)
    ?children"
  have children_length: "length ?children=q" by simp
  have slot_bound: "phase mod q<q" using positive_q by simp
  have selected:
    "comma_phase_member ?result phase=
      comma_phase_member (?children!(phase mod q)) phase"
    by (rule comma_indexed_phase_union_select[OF positive_q children_length])
  have child_row:
    "?children!(phase mod q)=
      lower ((offset+comma_crt_axis_weight axis*(phase mod q)) mod period)
        (map (comma_phase_word_cofactor axis (phase mod q)) rows)"
    using slot_bound by simp
  have mapped_length:
    "length (map (comma_phase_word_cofactor axis (phase mod q)) rows)=period"
    using row_length by simp
  have lower_value:
    "bit (lower ((offset+comma_crt_axis_weight axis*(phase mod q)) mod period)
        (map (comma_phase_word_cofactor axis (phase mod q)) rows)) phase=
      bit (map (comma_phase_word_cofactor axis (phase mod q)) rows !
        ((((offset+comma_crt_axis_weight axis*(phase mod q)) mod period)+
          comma_crt_suffix (Suc axis) phase) mod period)) phase"
    by (rule lower_exact[OF mapped_length])
  have row_index:
    "(((offset+comma_crt_axis_weight axis*(phase mod q)) mod period+
        comma_crt_suffix (Suc axis) phase) mod period)=
      (offset+comma_crt_suffix axis phase) mod period"
    using radix by (simp only: radix mod_add_left_eq
      comma_crt_suffix_step[OF axis] add.assoc)
  have period_slot:
    "(offset+comma_crt_suffix axis phase) mod period<period"
    using positive_period by simp
  have mapped_row:
    "map (comma_phase_word_cofactor axis (phase mod q)) rows !
        ((offset+comma_crt_suffix axis phase) mod period)=
      comma_phase_word_cofactor axis (phase mod q)
        (rows!((offset+comma_crt_suffix axis phase) mod period))"
    using row_length period_slot by simp
  have selected_axis:
    "phase mod q=phase mod comma_crt_axis_radix axis"
    using radix by simp
  have cofactor_value:
    "bit (comma_phase_word_cofactor axis (phase mod q)
        (rows!((offset+comma_crt_suffix axis phase) mod period))) phase=
      bit (rows!((offset+comma_crt_suffix axis phase) mod period)) phase"
  proof -
    have axis_slot_bound:
      "phase mod q<comma_crt_axis_radix axis"
      using slot_bound radix by simp
    show ?thesis
      by (rule comma_phase_word_cofactor_selected
        [OF axis axis_slot_bound phase selected_axis])
  qed
  show ?thesis using selected child_row lower_value mapped_row cofactor_value phase
      row_index by (simp add: comma_phase_member_def)
qed

lemma comma_crt_select3_bit:
  assumes positive: "0<period" and row_length: "length rows=period"
    and phase: "phase<924"
  shows "bit (comma_crt_select3 period offset rows) phase=
    bit (rows!((offset+comma_crt_suffix 3 phase) mod period)) phase"
  unfolding comma_crt_select3_def
  apply (rule comma_crt_cofactored_step_bit
    [where axis=3 and q=11 and lower="comma_crt_select4 period"])
  using assms
  by (simp_all add: comma_crt_axis_radix_def comma_crt_suffix_def
    comma_crt_select4_bit)

lemma comma_crt_select2_bit:
  assumes positive: "0<period" and row_length: "length rows=period"
    and phase: "phase<924"
  shows "bit (comma_crt_select2 period offset rows) phase=
    bit (rows!((offset+comma_crt_suffix 2 phase) mod period)) phase"
  unfolding comma_crt_select2_def
  apply (rule comma_crt_cofactored_step_bit
    [where axis=2 and q=7 and lower="comma_crt_select3 period"])
  using assms
  by (simp_all add: comma_crt_axis_radix_def comma_crt_suffix_def
    comma_crt_select3_bit)

lemma comma_crt_select1_bit:
  assumes positive: "0<period" and row_length: "length rows=period"
    and phase: "phase<924"
  shows "bit (comma_crt_select1 period offset rows) phase=
    bit (rows!((offset+comma_crt_suffix 1 phase) mod period)) phase"
  unfolding comma_crt_select1_def
  apply (rule comma_crt_cofactored_step_bit
    [where axis=1 and q=3 and lower="comma_crt_select2 period"])
  using assms
  by (simp_all add: comma_crt_axis_radix_def comma_crt_suffix_def
    comma_crt_select2_bit)

lemma comma_crt_select0_bit:
  assumes positive: "0<period" and row_length: "length rows=period"
    and phase: "phase<924"
  shows "bit (comma_crt_select0 period offset rows) phase=
    bit (rows!((offset+comma_crt_suffix 0 phase) mod period)) phase"
  unfolding comma_crt_select0_def
  apply (rule comma_crt_cofactored_step_bit
    [where axis=0 and q=4 and lower="comma_crt_select1 period"])
  using assms
  by (simp_all add: comma_crt_axis_radix_def comma_crt_suffix_def
    comma_crt_select1_bit)

lemma comma_crt_select0_bounded:
  "take_bit 924 (comma_crt_select0 period offset rows)=
    comma_crt_select0 period offset rows"
  unfolding comma_crt_select0_def by (rule comma_indexed_phase_union_bounded)

lemma comma_crt_select1_bounded:
  "take_bit 924 (comma_crt_select1 period offset rows)=
    comma_crt_select1 period offset rows"
  unfolding comma_crt_select1_def by (rule comma_indexed_phase_union_bounded)

lemma comma_crt_select2_bounded:
  "take_bit 924 (comma_crt_select2 period offset rows)=
    comma_crt_select2 period offset rows"
  unfolding comma_crt_select2_def by (rule comma_indexed_phase_union_bounded)

lemma comma_crt_select3_bounded:
  "take_bit 924 (comma_crt_select3 period offset rows)=
    comma_crt_select3 period offset rows"
  unfolding comma_crt_select3_def by (rule comma_indexed_phase_union_bounded)

lemma comma_crt_select4_uniform:
  assumes positive: "0<period" and bounded: "take_bit 924 word=word"
  shows "comma_crt_select4 period offset (replicate period word)=word"
  using positive bounded by (simp add: comma_crt_select4_def)

lemma comma_crt_select3_uniform:
  assumes positive: "0<period" and bounded: "take_bit 924 word=word"
  shows "comma_crt_select3 period offset (replicate period word)=word"
  by (rule comma_crt_bounded_word_ext
    [OF comma_crt_select3_bounded bounded])
    (simp add: comma_crt_select3_bit positive)

lemma comma_crt_select2_uniform:
  assumes positive: "0<period" and bounded: "take_bit 924 word=word"
  shows "comma_crt_select2 period offset (replicate period word)=word"
  by (rule comma_crt_bounded_word_ext
    [OF comma_crt_select2_bounded bounded])
    (simp add: comma_crt_select2_bit positive)

lemma comma_crt_select1_uniform:
  assumes positive: "0<period" and bounded: "take_bit 924 word=word"
  shows "comma_crt_select1 period offset (replicate period word)=word"
  by (rule comma_crt_bounded_word_ext
    [OF comma_crt_select1_bounded bounded])
    (simp add: comma_crt_select1_bit positive)

lemma comma_crt_select0_uniform:
  assumes positive: "0<period" and bounded: "take_bit 924 word=word"
  shows "comma_crt_select0 period offset (replicate period word)=word"
  by (rule comma_crt_bounded_word_ext
    [OF comma_crt_select0_bounded bounded])
    (simp add: comma_crt_select0_bit positive)

lemma comma_crt_select_exact:
  assumes positive: "0<period" and divides: "period dvd 924"
    and row_length: "length rows=period"
  shows "comma_crt_select0 period 0 rows=
    comma_indexed_phase_union (\<lambda>slot phase. phase mod period=slot) rows"
proof (rule bit_eqI)
  fix phase
  show "bit (comma_crt_select0 period 0 rows) phase=
    bit (comma_indexed_phase_union (\<lambda>slot phase. phase mod period=slot) rows) phase"
  proof (cases "phase<924")
    case True
    have left:
      "bit (comma_crt_select0 period 0 rows) phase=
        bit (rows!((0+comma_crt_suffix 0 phase) mod period)) phase"
      by (rule comma_crt_select0_bit[OF positive row_length True])
    have clock: "comma_crt_suffix 0 phase mod 924=comma_crt_clock phase"
      by (rule comma_crt_suffix_zero_is_clock)
    have clock_mod: "comma_crt_clock phase mod period=phase mod period"
      by (rule comma_crt_clock_mod[OF divides])
    have suffix_norm:
      "(comma_crt_suffix 0 phase mod 924) mod period=
        comma_crt_suffix 0 phase mod period"
      by (rule mod_mod_cancel[OF divides])
    have index: "(0+comma_crt_suffix 0 phase) mod period=phase mod period"
      using clock clock_mod suffix_norm by simp
    have right_member:
      "comma_phase_member
        (comma_indexed_phase_union (\<lambda>slot phase. phase mod period=slot) rows)
        phase=comma_phase_member (rows!(phase mod period)) phase"
      by (rule comma_indexed_phase_union_select[OF positive row_length])
    show ?thesis using left right_member True index
      by (simp add: comma_phase_member_def)
  next
    case False
    have left_bounded:
      "take_bit 924 (comma_crt_select0 period 0 rows)=comma_crt_select0 period 0 rows"
      by (rule comma_crt_select0_bounded)
    have right_bounded:
      "take_bit 924
        (comma_indexed_phase_union (\<lambda>slot phase. phase mod period=slot) rows)=
        comma_indexed_phase_union (\<lambda>slot phase. phase mod period=slot) rows"
      by (rule comma_indexed_phase_union_bounded)
    have left_zero: "bit (comma_crt_select0 period 0 rows) phase=False"
      by (rule comma_symbolic_phase_bit_outside[OF left_bounded]) (use False in arith)
    have right_zero:
      "bit (comma_indexed_phase_union (\<lambda>slot phase. phase mod period=slot) rows)
        phase=False"
      by (rule comma_symbolic_phase_bit_outside[OF right_bounded]) (use False in arith)
    show ?thesis using left_zero right_zero by simp
  qed
qed

ML \<open>Comma_Fast_Kernel.report "CRT cofactor checkpoint=selector-exact"\<close>

lemma comma_crt_select_suffix_collapse:
  fixes evaluate :: "nat \<Rightarrow> nat list \<Rightarrow> nat"
    and suffix :: "nat \<Rightarrow> nat"
  assumes positive: "0<period" and row_length: "length rows=period"
    and exact:
      "\<And>phase. phase<924 \<Longrightarrow>
        bit (evaluate offset rows) phase=
          bit (rows!((offset+suffix phase) mod period)) phase"
    and suffix_zero: "\<And>phase. phase<924 \<Longrightarrow> suffix phase mod period=0"
    and result_bounded: "take_bit 924 (evaluate offset rows)=evaluate offset rows"
    and selected_bounded:
      "take_bit 924 (rows!(offset mod period))=rows!(offset mod period)"
  shows "evaluate offset rows=rows!(offset mod period)"
proof (rule bit_eqI)
  fix phase
  show "bit (evaluate offset rows) phase=bit (rows!(offset mod period)) phase"
  proof (cases "phase<924")
    case True
    have selected:
      "bit (evaluate offset rows) phase=
        bit (rows!((offset+suffix phase) mod period)) phase"
      by (rule exact[OF True])
    have index: "(offset+suffix phase) mod period=offset mod period"
    proof -
      have "(offset+suffix phase) mod period=
          (offset+(suffix phase mod period)) mod period"
        by (rule mod_add_right_eq[symmetric])
      also have "...=offset mod period"
        using suffix_zero[OF True] by simp
      finally show ?thesis .
    qed
    show ?thesis using selected index by simp
  next
    case False
    have left_zero: "bit (evaluate offset rows) phase=False"
      by (rule comma_symbolic_phase_bit_outside[OF result_bounded])
        (use False in arith)
    have right_zero: "bit (rows!(offset mod period)) phase=False"
      by (rule comma_symbolic_phase_bit_outside[OF selected_bounded])
        (use False in arith)
    show ?thesis using left_zero right_zero by simp
  qed
qed

lemma comma_crt_select3_suffix_collapse:
  assumes positive: "0<period" and row_length: "length rows=period"
    and suffix_zero: "\<And>phase. phase<924 \<Longrightarrow>
      comma_crt_suffix 3 phase mod period=0"
    and selected_bounded:
      "take_bit 924 (rows!(offset mod period))=rows!(offset mod period)"
  shows "comma_crt_select3 period offset rows=rows!(offset mod period)"
proof (rule comma_crt_select_suffix_collapse[OF positive row_length])
  show "\<And>phase. phase<924 \<Longrightarrow>
      bit (comma_crt_select3 period offset rows) phase=
        bit (rows!((offset+comma_crt_suffix 3 phase) mod period)) phase"
    by (rule comma_crt_select3_bit[OF positive row_length])
  show "\<And>phase. phase<924 \<Longrightarrow>
      comma_crt_suffix 3 phase mod period=0"
    by (rule suffix_zero)
  show "take_bit 924 (comma_crt_select3 period offset rows)=
      comma_crt_select3 period offset rows"
    unfolding comma_crt_select3_def by (rule comma_indexed_phase_union_bounded)
  show "take_bit 924 (rows!(offset mod period))=rows!(offset mod period)"
    by (rule selected_bounded)
qed

lemma comma_crt_select2_suffix_collapse:
  assumes positive: "0<period" and row_length: "length rows=period"
    and suffix_zero: "\<And>phase. phase<924 \<Longrightarrow>
      comma_crt_suffix 2 phase mod period=0"
    and selected_bounded:
      "take_bit 924 (rows!(offset mod period))=rows!(offset mod period)"
  shows "comma_crt_select2 period offset rows=rows!(offset mod period)"
proof (rule comma_crt_select_suffix_collapse[OF positive row_length])
  show "\<And>phase. phase<924 \<Longrightarrow>
      bit (comma_crt_select2 period offset rows) phase=
        bit (rows!((offset+comma_crt_suffix 2 phase) mod period)) phase"
    by (rule comma_crt_select2_bit[OF positive row_length])
  show "\<And>phase. phase<924 \<Longrightarrow>
      comma_crt_suffix 2 phase mod period=0"
    by (rule suffix_zero)
  show "take_bit 924 (comma_crt_select2 period offset rows)=
      comma_crt_select2 period offset rows"
    unfolding comma_crt_select2_def by (rule comma_indexed_phase_union_bounded)
  show "take_bit 924 (rows!(offset mod period))=rows!(offset mod period)"
    by (rule selected_bounded)
qed

lemma comma_crt_select1_suffix_collapse:
  assumes positive: "0<period" and row_length: "length rows=period"
    and suffix_zero: "\<And>phase. phase<924 \<Longrightarrow>
      comma_crt_suffix 1 phase mod period=0"
    and selected_bounded:
      "take_bit 924 (rows!(offset mod period))=rows!(offset mod period)"
  shows "comma_crt_select1 period offset rows=rows!(offset mod period)"
proof (rule comma_crt_select_suffix_collapse[OF positive row_length])
  show "\<And>phase. phase<924 \<Longrightarrow>
      bit (comma_crt_select1 period offset rows) phase=
        bit (rows!((offset+comma_crt_suffix 1 phase) mod period)) phase"
    by (rule comma_crt_select1_bit[OF positive row_length])
  show "\<And>phase. phase<924 \<Longrightarrow>
      comma_crt_suffix 1 phase mod period=0"
    by (rule suffix_zero)
  show "take_bit 924 (comma_crt_select1 period offset rows)=
      comma_crt_select1 period offset rows"
    unfolding comma_crt_select1_def by (rule comma_indexed_phase_union_bounded)
  show "take_bit 924 (rows!(offset mod period))=rows!(offset mod period)"
    by (rule selected_bounded)
qed

lemma comma_crt_select0_suffix_collapse:
  assumes positive: "0<period" and row_length: "length rows=period"
    and suffix_zero: "\<And>phase. phase<924 \<Longrightarrow>
      comma_crt_suffix 0 phase mod period=0"
    and selected_bounded:
      "take_bit 924 (rows!(offset mod period))=rows!(offset mod period)"
  shows "comma_crt_select0 period offset rows=rows!(offset mod period)"
proof (rule comma_crt_select_suffix_collapse[OF positive row_length])
  show "\<And>phase. phase<924 \<Longrightarrow>
      bit (comma_crt_select0 period offset rows) phase=
        bit (rows!((offset+comma_crt_suffix 0 phase) mod period)) phase"
    by (rule comma_crt_select0_bit[OF positive row_length])
  show "\<And>phase. phase<924 \<Longrightarrow>
      comma_crt_suffix 0 phase mod period=0"
    by (rule suffix_zero)
  show "take_bit 924 (comma_crt_select0 period offset rows)=
      comma_crt_select0 period offset rows"
    by (rule comma_crt_select0_bounded)
  show "take_bit 924 (rows!(offset mod period))=rows!(offset mod period)"
    by (rule selected_bounded)
qed

lemma comma_crt_suffix_zero_if_weights_divide:
  assumes axis: "axis<4"
    and weights:
      "\<And>index. axis\<le>index \<Longrightarrow> index<4 \<Longrightarrow>
        comma_crt_axis_weight index mod period=0"
  shows "comma_crt_suffix axis phase mod period=0"
proof -
  have axis_cases: "axis=0 \<or> axis=1 \<or> axis=2 \<or> axis=3"
    by (rule comma_crt_axis_cases[OF axis])
  have w0: "axis\<le>(0::nat) \<Longrightarrow>
      comma_crt_axis_weight (0::nat) mod period=0"
    using weights[of "0::nat"] by simp
  have w1: "axis\<le>(1::nat) \<Longrightarrow>
      comma_crt_axis_weight (1::nat) mod period=0"
    using weights[of "1::nat"] by simp
  have w2: "axis\<le>(2::nat) \<Longrightarrow>
      comma_crt_axis_weight (2::nat) mod period=0"
    using weights[of "2::nat"] by simp
  have w3: "axis\<le>(3::nat) \<Longrightarrow>
      comma_crt_axis_weight (3::nat) mod period=0"
    using weights[of "3::nat"] by simp
  have t0: "axis\<le>(0::nat) \<Longrightarrow>
      (comma_crt_axis_weight (0::nat)*(phase mod 4)) mod period=0"
  proof -
    assume active: "axis\<le>(0::nat)"
    have coefficient:
      "comma_crt_axis_weight (0::nat) mod period=0"
      by (rule w0[OF active])
    show "(comma_crt_axis_weight (0::nat)*(phase mod 4)) mod period=0"
      using comma_crt_weighted_term[OF coefficient] by simp
  qed
  have t1: "axis\<le>(1::nat) \<Longrightarrow>
      (comma_crt_axis_weight (1::nat)*(phase mod 3)) mod period=0"
  proof -
    assume active: "axis\<le>(1::nat)"
    have coefficient:
      "comma_crt_axis_weight (1::nat) mod period=0"
      by (rule w1[OF active])
    show "(comma_crt_axis_weight (1::nat)*(phase mod 3)) mod period=0"
      using comma_crt_weighted_term[OF coefficient] by simp
  qed
  have t2: "axis\<le>(2::nat) \<Longrightarrow>
      (comma_crt_axis_weight (2::nat)*(phase mod 7)) mod period=0"
  proof -
    assume active: "axis\<le>(2::nat)"
    have coefficient:
      "comma_crt_axis_weight (2::nat) mod period=0"
      by (rule w2[OF active])
    show "(comma_crt_axis_weight (2::nat)*(phase mod 7)) mod period=0"
      using comma_crt_weighted_term[OF coefficient] by simp
  qed
  have t3: "axis\<le>(3::nat) \<Longrightarrow>
      (comma_crt_axis_weight (3::nat)*(phase mod 11)) mod period=0"
  proof -
    assume active: "axis\<le>(3::nat)"
    have coefficient:
      "comma_crt_axis_weight (3::nat) mod period=0"
      by (rule w3[OF active])
    show "(comma_crt_axis_weight (3::nat)*(phase mod 11)) mod period=0"
      using comma_crt_weighted_term[OF coefficient] by simp
  qed
  show ?thesis using axis_cases t0 t1 t2 t3
    by (auto simp: comma_crt_suffix_def comma_crt_axis_weight_def mod_add_eq)
qed

lemma comma_crt_select3_zero_suffix:
  assumes positive: "0<period" and row_length: "length rows=period"
    and weight3: "comma_crt_axis_weight 3 mod period=0"
    and selected_bounded:
      "take_bit 924 (rows!(offset mod period))=rows!(offset mod period)"
  shows "comma_crt_select3 period offset rows=rows!(offset mod period)"
proof (rule comma_crt_select3_suffix_collapse[OF positive row_length])
  show "\<And>phase. phase<924 \<Longrightarrow>
      comma_crt_suffix 3 phase mod period=0"
  proof -
    fix phase :: nat
    assume phase_bound: "phase<924"
    have coefficient: "(672::nat) mod period=0"
      using weight3 by (simp add: comma_crt_axis_weight_def)
    have term_residue: "(672*(phase mod 11)) mod period=0"
      using comma_crt_weighted_term[OF coefficient] by simp
    show "comma_crt_suffix 3 phase mod period=0"
      using term_residue by (simp add: comma_crt_suffix_def)
  qed
  show "take_bit 924 (rows!(offset mod period))=rows!(offset mod period)"
    by (rule selected_bounded)
qed

lemma comma_crt_select2_zero_suffix:
  assumes positive: "0<period" and row_length: "length rows=period"
    and weight2: "comma_crt_axis_weight 2 mod period=0"
    and weight3: "comma_crt_axis_weight 3 mod period=0"
    and selected_bounded:
      "take_bit 924 (rows!(offset mod period))=rows!(offset mod period)"
  shows "comma_crt_select2 period offset rows=rows!(offset mod period)"
proof (rule comma_crt_select2_suffix_collapse[OF positive row_length])
  show "\<And>phase. phase<924 \<Longrightarrow>
      comma_crt_suffix 2 phase mod period=0"
  proof -
    fix phase :: nat
    assume phase_bound: "phase<924"
    have coefficient2: "(792::nat) mod period=0"
      using weight2 by (simp add: comma_crt_axis_weight_def)
    have coefficient3: "(672::nat) mod period=0"
      using weight3 by (simp add: comma_crt_axis_weight_def)
    have term2: "(792*(phase mod 7)) mod period=0"
      using comma_crt_weighted_term[OF coefficient2] by simp
    have term3: "(672*(phase mod 11)) mod period=0"
      using comma_crt_weighted_term[OF coefficient3] by simp
    have suffix:
      "(792*(phase mod 7)+672*(phase mod 11)) mod period=0"
      by (rule comma_crt_mod_zero_add[OF term2 term3])
    show "comma_crt_suffix 2 phase mod period=0"
      using suffix by (simp add: comma_crt_suffix_def)
  qed
  show "take_bit 924 (rows!(offset mod period))=rows!(offset mod period)"
    by (rule selected_bounded)
qed

lemma comma_crt_select1_zero_suffix:
  assumes positive: "0<period" and row_length: "length rows=period"
    and weight1: "comma_crt_axis_weight 1 mod period=0"
    and weight2: "comma_crt_axis_weight 2 mod period=0"
    and weight3: "comma_crt_axis_weight 3 mod period=0"
    and selected_bounded:
      "take_bit 924 (rows!(offset mod period))=rows!(offset mod period)"
  shows "comma_crt_select1 period offset rows=rows!(offset mod period)"
proof (rule comma_crt_select1_suffix_collapse[OF positive row_length])
  show "\<And>phase. phase<924 \<Longrightarrow>
      comma_crt_suffix 1 phase mod period=0"
  proof -
    fix phase :: nat
    assume phase_bound: "phase<924"
    have coefficient1: "(616::nat) mod period=0"
      using weight1 by (simp add: comma_crt_axis_weight_def)
    have coefficient2: "(792::nat) mod period=0"
      using weight2 by (simp add: comma_crt_axis_weight_def)
    have coefficient3: "(672::nat) mod period=0"
      using weight3 by (simp add: comma_crt_axis_weight_def)
    have term1: "(616*(phase mod 3)) mod period=0"
      using comma_crt_weighted_term[OF coefficient1] by simp
    have term2: "(792*(phase mod 7)) mod period=0"
      using comma_crt_weighted_term[OF coefficient2] by simp
    have term3: "(672*(phase mod 11)) mod period=0"
      using comma_crt_weighted_term[OF coefficient3] by simp
    have prefix:
      "(616*(phase mod 3)+792*(phase mod 7)) mod period=0"
      by (rule comma_crt_mod_zero_add[OF term1 term2])
    have suffix:
      "(616*(phase mod 3)+792*(phase mod 7)+672*(phase mod 11))
        mod period=0"
      by (rule comma_crt_mod_zero_add[OF prefix term3])
    show "comma_crt_suffix 1 phase mod period=0"
      using suffix by (simp add: comma_crt_suffix_def)
  qed
  show "take_bit 924 (rows!(offset mod period))=rows!(offset mod period)"
    by (rule selected_bounded)
qed

lemma comma_crt_select0_zero_suffix:
  assumes positive: "0<period" and row_length: "length rows=period"
    and weight0: "comma_crt_axis_weight 0 mod period=0"
    and weight1: "comma_crt_axis_weight 1 mod period=0"
    and weight2: "comma_crt_axis_weight 2 mod period=0"
    and weight3: "comma_crt_axis_weight 3 mod period=0"
    and selected_bounded:
      "take_bit 924 (rows!(offset mod period))=rows!(offset mod period)"
  shows "comma_crt_select0 period offset rows=rows!(offset mod period)"
proof (rule comma_crt_select0_suffix_collapse[OF positive row_length])
  show "\<And>phase. phase<924 \<Longrightarrow>
      comma_crt_suffix 0 phase mod period=0"
  proof -
    fix phase :: nat
    assume phase_bound: "phase<924"
    have coefficient0: "(693::nat) mod period=0"
      using weight0 by (simp add: comma_crt_axis_weight_def)
    have coefficient1: "(616::nat) mod period=0"
      using weight1 by (simp add: comma_crt_axis_weight_def)
    have coefficient2: "(792::nat) mod period=0"
      using weight2 by (simp add: comma_crt_axis_weight_def)
    have coefficient3: "(672::nat) mod period=0"
      using weight3 by (simp add: comma_crt_axis_weight_def)
    have term0: "(693*(phase mod 4)) mod period=0"
      using comma_crt_weighted_term[OF coefficient0] by simp
    have term1: "(616*(phase mod 3)) mod period=0"
      using comma_crt_weighted_term[OF coefficient1] by simp
    have term2: "(792*(phase mod 7)) mod period=0"
      using comma_crt_weighted_term[OF coefficient2] by simp
    have term3: "(672*(phase mod 11)) mod period=0"
      using comma_crt_weighted_term[OF coefficient3] by simp
    have prefix01:
      "(693*(phase mod 4)+616*(phase mod 3)) mod period=0"
      by (rule comma_crt_mod_zero_add[OF term0 term1])
    have prefix012:
      "(693*(phase mod 4)+616*(phase mod 3)+792*(phase mod 7))
        mod period=0"
      by (rule comma_crt_mod_zero_add[OF prefix01 term2])
    have suffix:
      "(693*(phase mod 4)+616*(phase mod 3)+
        792*(phase mod 7)+672*(phase mod 11)) mod period=0"
      by (rule comma_crt_mod_zero_add[OF prefix012 term3])
    show "comma_crt_suffix 0 phase mod period=0"
      using suffix by (simp add: comma_crt_suffix_def)
  qed
  show "take_bit 924 (rows!(offset mod period))=rows!(offset mod period)"
    by (rule selected_bounded)
qed

ML \<open>Comma_Fast_Kernel.report "CRT cofactor checkpoint=suffix-collapse"\<close>

ML \<open>
  val comma_crt_cofactor_selection_rules = @{thms
    comma_crt_axis_cases comma_crt_suffix_step comma_crt_clock_reconstruct
    comma_crt_clock_mod comma_crt_suffix_zero_if_weights_divide
    comma_crt_rebase_selected comma_crt_rebase_other_axis
    comma_crt_rebase_selected_axis comma_crt_rebase_bounded
    comma_phase_word_cofactor_zero comma_phase_word_cofactor_full
    comma_phase_word_cofactor_selected
    comma_phase_word_cofactor_reassemble
    comma_phase_word_cofactor_same_axis_union
    comma_phase_word_cofactor_other_axis_union
    comma_phase_word_cofactor_same_axis_q
    comma_phase_word_cofactor_other_axis_q
    comma_crt_select0_equation comma_crt_select1_equation
    comma_crt_select2_equation comma_crt_select3_equation
    comma_crt_select4_equation comma_crt_select0_bit
    comma_crt_select1_bit comma_crt_select2_bit comma_crt_select3_bit
    comma_crt_select0_bounded comma_crt_select1_bounded
    comma_crt_select2_bounded comma_crt_select3_bounded
    comma_crt_select0_uniform comma_crt_select1_uniform
    comma_crt_select2_uniform comma_crt_select3_uniform
    comma_crt_select4_uniform
    comma_crt_select_exact comma_crt_select_suffix_collapse
    comma_crt_select3_zero_suffix comma_crt_select2_zero_suffix
    comma_crt_select1_zero_suffix comma_crt_select0_zero_suffix};
  Thm.consolidate comma_crt_cofactor_selection_rules;
  Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "CRT-cofactored phase selector" comma_crt_cofactor_selection_rules;
  if null (Thm_Deps.all_oracles comma_crt_cofactor_selection_rules)
  then () else error "CRT-cofactored phase selector depends on an oracle"
\<close>

end
