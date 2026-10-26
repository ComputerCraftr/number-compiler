theory Comma_CRT_Selector_Projection
  imports Comma_CRT_Cofactor_Selection
begin

unbundle bit_operations_syntax

lemma comma_crt_zero_weight_suffix:
  fixes axis period phase :: nat
  assumes axis: "axis<4" and positive: "0<period"
    and weight_zero: "comma_crt_axis_weight axis mod period=0"
  shows "comma_crt_suffix axis phase mod period=
    comma_crt_suffix (Suc axis) phase mod period"
proof -
  have term_zero:
    "(comma_crt_axis_weight axis*(phase mod comma_crt_axis_radix axis))
        mod period=0"
    using comma_crt_weighted_term
      [OF weight_zero, where source_value="phase mod comma_crt_axis_radix axis"]
    by simp
  have step: "comma_crt_suffix axis phase=
      comma_crt_axis_weight axis*(phase mod comma_crt_axis_radix axis)+
        comma_crt_suffix (Suc axis) phase"
    by (rule comma_crt_suffix_step[OF axis])
  have "comma_crt_suffix axis phase mod period=
      ((comma_crt_axis_weight axis*(phase mod comma_crt_axis_radix axis))
        mod period+(comma_crt_suffix (Suc axis) phase mod period)) mod period"
    unfolding step by (rule mod_add_eq[symmetric])
  also have "...=comma_crt_suffix (Suc axis) phase mod period"
    using term_zero by simp
  finally show ?thesis .
qed

lemma comma_crt_zero_weight_index:
  fixes axis period offset phase :: nat
  assumes axis: "axis<4" and positive: "0<period"
    and weight_zero: "comma_crt_axis_weight axis mod period=0"
  shows "(offset+comma_crt_suffix axis phase) mod period=
    (offset+comma_crt_suffix (Suc axis) phase) mod period"
proof -
  have suffix_mod:
    "comma_crt_suffix axis phase mod period=
      comma_crt_suffix (Suc axis) phase mod period"
    by (rule comma_crt_zero_weight_suffix[OF axis positive weight_zero])
  have "(offset+comma_crt_suffix axis phase) mod period=
      ((offset mod period)+(comma_crt_suffix axis phase mod period)) mod period"
    by (rule mod_add_eq[symmetric])
  also have "...=((offset mod period)+
      (comma_crt_suffix (Suc axis) phase mod period)) mod period"
    using suffix_mod by simp
  also have "...=(offset+comma_crt_suffix (Suc axis) phase) mod period"
    by (rule mod_add_eq)
  finally show ?thesis .
qed

lemma comma_crt_modular_translation:
  fixes weight slot period delta receiver :: nat
  assumes delta: "(weight*slot) mod period=delta"
  shows "(receiver+weight*slot) mod period=
    (receiver+delta) mod period"
proof -
  have action:
    "(receiver+weight*slot) mod period=
      (receiver+(weight*slot mod period)) mod period"
    by (rule mod_add_right_eq[symmetric])
  show ?thesis using action delta by simp
qed

lemma comma_crt_cofactor_leaf_rows:
  fixes rows :: "nat list" and axis slot :: nat
  assumes leaves:
    "list_all (\<lambda>word. word=0 \<or> word=(mask 924::nat)) rows"
  shows "map (\<lambda>word. comma_phase_word_cofactor axis slot word) rows=rows"
  using leaves
proof (induction rows)
  case Nil
  then show ?case by simp
next
  case (Cons word rows)
  have head: "word=0 \<or> word=(mask 924::nat)"
    using Cons.prems by simp
  have tail:
    "list_all (\<lambda>word. word=0 \<or> word=(mask 924::nat)) rows"
    using Cons.prems by simp
  have tail_map:
    "map (\<lambda>word. comma_phase_word_cofactor axis slot word) rows=rows"
    by (rule Cons.IH[OF tail])
  show ?case
    using head tail_map
    by (cases "word=0")
      (simp_all add: comma_phase_word_cofactor_zero comma_phase_word_cofactor_full)
qed

definition comma_crt_word_prefix_independent :: "nat \<Rightarrow> nat \<Rightarrow> bool"
where
  "comma_crt_word_prefix_independent upper word \<longleftrightarrow>
    (\<forall>target<upper. \<forall>slot<comma_crt_axis_radix target.
      comma_phase_word_cofactor target slot word=word)"

lemma comma_crt_word_prefix_independent_mono:
  assumes lower_upper: "lower\<le>upper"
    and independent: "comma_crt_word_prefix_independent upper word"
  shows "comma_crt_word_prefix_independent lower word"
  using lower_upper independent
  unfolding comma_crt_word_prefix_independent_def
  by (blast intro: less_le_trans)

lemma comma_crt_word_prefix_independent_at:
  assumes independent: "comma_crt_word_prefix_independent upper word"
    and target_bound: "target<upper"
    and slot_bound: "slot<comma_crt_axis_radix target"
  shows "comma_phase_word_cofactor target slot word=word"
  using independent target_bound slot_bound
  by (auto simp: comma_crt_word_prefix_independent_def)

lemma comma_crt_word_prefix_independent_zero:
  "comma_crt_word_prefix_independent 4 0"
  by (auto simp: comma_crt_word_prefix_independent_def
      comma_phase_word_cofactor_zero)

lemma comma_crt_word_prefix_independent_full:
  "comma_crt_word_prefix_independent 4 (mask 924::nat)"
  by (auto simp: comma_crt_word_prefix_independent_def
      comma_phase_word_cofactor_full)

lemma comma_crt_word_prefix_independent_indexed_union:
  fixes outer :: nat and rows :: "nat list"
  assumes outer: "outer<4"
    and row_length: "length rows=comma_crt_axis_radix outer"
    and children:
      "list_all (comma_crt_word_prefix_independent outer) rows"
  shows "comma_crt_word_prefix_independent outer
    (comma_indexed_phase_union
      (\<lambda>slot phase. phase mod comma_crt_axis_radix outer=slot) rows)"
proof -
  have child_properties:
    "\<forall>row\<in>set rows. comma_crt_word_prefix_independent outer row"
    using children by (simp add: list_all_iff)
  show ?thesis
    unfolding comma_crt_word_prefix_independent_def
  proof (intro allI impI)
    fix target slot
    assume target_bound: "target<outer"
      and slot_bound: "slot<comma_crt_axis_radix target"
    have target_axis: "target<4" using target_bound outer by arith
    have distinct: "target\<noteq>outer" using target_bound by arith
    have mapped_rows:
      "map (comma_phase_word_cofactor target slot) rows=rows"
    proof (rule map_idI)
      fix row
      assume row_member: "row\<in>set rows"
      have row_property:
        "comma_crt_word_prefix_independent outer row"
        using child_properties row_member by blast
      show "comma_phase_word_cofactor target slot row=row"
        using row_property target_bound slot_bound
        by (simp add: comma_crt_word_prefix_independent_def)
    qed
    have commute:
      "comma_phase_word_cofactor target slot
          (comma_indexed_phase_union
            (\<lambda>j phase. phase mod comma_crt_axis_radix outer=j) rows)=
        comma_indexed_phase_union
          (\<lambda>j phase. phase mod comma_crt_axis_radix outer=j)
          (map (comma_phase_word_cofactor target slot) rows)"
    proof (rule comma_phase_word_cofactor_other_axis_q
      [where axis=target and other=outer
        and q="comma_crt_axis_radix outer" and slot=slot and rows=rows])
      show "target<4" by (rule target_axis)
      show "outer<4" by (rule outer)
      show "target\<noteq>outer" by (rule distinct)
      show "comma_crt_axis_radix outer=comma_crt_axis_radix outer" by simp
      show "length rows=comma_crt_axis_radix outer" by (rule row_length)
    qed
    show "comma_phase_word_cofactor target slot
        (comma_indexed_phase_union
          (\<lambda>slot phase. phase mod comma_crt_axis_radix outer=slot) rows)=
      comma_indexed_phase_union
        (\<lambda>slot phase. phase mod comma_crt_axis_radix outer=slot) rows"
      using commute mapped_rows by simp
  qed
qed

lemma comma_crt_word_prefix_independent_indexed_union_q:
  fixes outer q :: nat and rows :: "nat list"
  assumes outer: "outer<4"
    and radix: "q=comma_crt_axis_radix outer"
    and row_length: "length rows=q"
    and children:
      "list_all (comma_crt_word_prefix_independent outer) rows"
  shows "comma_crt_word_prefix_independent outer
    (comma_indexed_phase_union
      (\<lambda>slot phase. phase mod q=slot) rows)"
proof -
  have canonical_row_length:
    "length rows=comma_crt_axis_radix outer"
    using row_length radix by simp
  have canonical:
    "comma_crt_word_prefix_independent outer
      (comma_indexed_phase_union
        (\<lambda>slot phase. phase mod comma_crt_axis_radix outer=slot) rows)"
    by (rule comma_crt_word_prefix_independent_indexed_union
      [OF outer canonical_row_length children])
  show ?thesis using canonical radix by (simp only: radix)
qed

lemma comma_crt_select3_skip:
  fixes period offset :: nat and rows :: "nat list"
  assumes positive: "0<period" and row_length: "length rows=period"
    and weight_zero: "comma_crt_axis_weight 3 mod period=0"
    and next_bounded:
      "take_bit 924 (comma_crt_select4 period offset rows)=
        comma_crt_select4 period offset rows"
  shows "comma_crt_select3 period offset rows=
    comma_crt_select4 period offset rows"
proof (rule comma_crt_bounded_word_ext)
  show "take_bit 924 (comma_crt_select3 period offset rows)=
      comma_crt_select3 period offset rows"
    by (rule comma_crt_select3_bounded)
  show "take_bit 924 (comma_crt_select4 period offset rows)=
      comma_crt_select4 period offset rows" by (rule next_bounded)
  fix phase :: nat
  assume phase: "phase<924"
  have index:
    "(offset+comma_crt_suffix 3 phase) mod period=
      (offset+comma_crt_suffix (Suc 3) phase) mod period"
    using comma_crt_zero_weight_index[where axis=3 and period=period and phase=phase]
      positive weight_zero by simp
  have left:
    "bit (comma_crt_select3 period offset rows) phase=
      bit (rows!((offset+comma_crt_suffix 3 phase) mod period)) phase"
    by (rule comma_crt_select3_bit[OF positive row_length phase])
  have right:
    "bit (comma_crt_select4 period offset rows) phase=
      bit (rows!(offset mod period)) phase"
    by (rule comma_crt_select4_bit[OF positive row_length])
  show "bit (comma_crt_select3 period offset rows) phase=
      bit (comma_crt_select4 period offset rows) phase"
    using left right index by (simp add: comma_crt_suffix_def)
qed

lemma comma_crt_select2_skip:
  fixes period offset :: nat and rows :: "nat list"
  assumes positive: "0<period" and row_length: "length rows=period"
    and weight_zero: "comma_crt_axis_weight 2 mod period=0"
    and next_bounded:
      "take_bit 924 (comma_crt_select3 period offset rows)=
        comma_crt_select3 period offset rows"
  shows "comma_crt_select2 period offset rows=
    comma_crt_select3 period offset rows"
proof (rule comma_crt_bounded_word_ext)
  show "take_bit 924 (comma_crt_select2 period offset rows)=
      comma_crt_select2 period offset rows"
    by (rule comma_crt_select2_bounded)
  show "take_bit 924 (comma_crt_select3 period offset rows)=
      comma_crt_select3 period offset rows" by (rule next_bounded)
  fix phase :: nat
  assume phase: "phase<924"
  have index:
    "(offset+comma_crt_suffix 2 phase) mod period=
      (offset+comma_crt_suffix (Suc 2) phase) mod period"
    using comma_crt_zero_weight_index[where axis=2 and period=period and phase=phase]
      positive weight_zero by simp
  have left:
    "bit (comma_crt_select2 period offset rows) phase=
      bit (rows!((offset+comma_crt_suffix 2 phase) mod period)) phase"
    by (rule comma_crt_select2_bit[OF positive row_length phase])
  have right:
    "bit (comma_crt_select3 period offset rows) phase=
      bit (rows!((offset+comma_crt_suffix 3 phase) mod period)) phase"
    by (rule comma_crt_select3_bit[OF positive row_length phase])
  show "bit (comma_crt_select2 period offset rows) phase=
      bit (comma_crt_select3 period offset rows) phase"
    using left right index by (simp add: numeral_2_eq_2 numeral_3_eq_3)
qed

lemma comma_crt_select1_skip:
  fixes period offset :: nat and rows :: "nat list"
  assumes positive: "0<period" and row_length: "length rows=period"
    and weight_zero: "comma_crt_axis_weight 1 mod period=0"
    and next_bounded:
      "take_bit 924 (comma_crt_select2 period offset rows)=
        comma_crt_select2 period offset rows"
  shows "comma_crt_select1 period offset rows=
    comma_crt_select2 period offset rows"
proof (rule comma_crt_bounded_word_ext)
  show "take_bit 924 (comma_crt_select1 period offset rows)=
      comma_crt_select1 period offset rows"
    by (rule comma_crt_select1_bounded)
  show "take_bit 924 (comma_crt_select2 period offset rows)=
      comma_crt_select2 period offset rows" by (rule next_bounded)
  fix phase :: nat
  assume phase: "phase<924"
  have index:
    "(offset+comma_crt_suffix 1 phase) mod period=
      (offset+comma_crt_suffix (Suc 1) phase) mod period"
    using comma_crt_zero_weight_index[where axis=1 and period=period and phase=phase]
      positive weight_zero by simp
  have left:
    "bit (comma_crt_select1 period offset rows) phase=
      bit (rows!((offset+comma_crt_suffix 1 phase) mod period)) phase"
    by (rule comma_crt_select1_bit[OF positive row_length phase])
  have right:
    "bit (comma_crt_select2 period offset rows) phase=
      bit (rows!((offset+comma_crt_suffix 2 phase) mod period)) phase"
    by (rule comma_crt_select2_bit[OF positive row_length phase])
  show "bit (comma_crt_select1 period offset rows) phase=
      bit (comma_crt_select2 period offset rows) phase"
    using left right index by (simp add: numeral_2_eq_2 numeral_3_eq_3)
qed

lemma comma_crt_select0_skip:
  fixes period offset :: nat and rows :: "nat list"
  assumes positive: "0<period" and row_length: "length rows=period"
    and weight_zero: "comma_crt_axis_weight 0 mod period=0"
    and next_bounded:
      "take_bit 924 (comma_crt_select1 period offset rows)=
        comma_crt_select1 period offset rows"
  shows "comma_crt_select0 period offset rows=
    comma_crt_select1 period offset rows"
proof (rule comma_crt_bounded_word_ext)
  show "take_bit 924 (comma_crt_select0 period offset rows)=
      comma_crt_select0 period offset rows"
    by (rule comma_crt_select0_bounded)
  show "take_bit 924 (comma_crt_select1 period offset rows)=
      comma_crt_select1 period offset rows" by (rule next_bounded)
  fix phase :: nat
  assume phase: "phase<924"
  have index:
    "(offset+comma_crt_suffix 0 phase) mod period=
      (offset+comma_crt_suffix (Suc 0) phase) mod period"
    using comma_crt_zero_weight_index[where axis=0 and period=period and phase=phase]
      positive weight_zero by simp
  have left:
    "bit (comma_crt_select0 period offset rows) phase=
      bit (rows!((offset+comma_crt_suffix 0 phase) mod period)) phase"
    by (rule comma_crt_select0_bit[OF positive row_length phase])
  have right:
    "bit (comma_crt_select1 period offset rows) phase=
      bit (rows!((offset+comma_crt_suffix 1 phase) mod period)) phase"
    by (rule comma_crt_select1_bit[OF positive row_length phase])
  show "bit (comma_crt_select0 period offset rows) phase=
      bit (comma_crt_select1 period offset rows) phase"
    using left right index by (simp add: numeral_2_eq_2 numeral_3_eq_3)
qed

definition comma_crt_terminal_selector_layer ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat"
where
  "comma_crt_terminal_selector_layer axis period offset rows =
    comma_indexed_phase_union
      (\<lambda>slot phase. phase mod comma_crt_axis_radix axis=slot)
      (map (\<lambda>slot. comma_phase_word_cofactor axis slot
        (rows!((offset+comma_crt_axis_weight axis*slot) mod period)))
        [0..<comma_crt_axis_radix axis])"

lemma comma_crt_terminal_suffix_remainder:
  fixes axis period offset phase :: nat
  assumes axis: "axis<4"
    and higher_weights:
      "\<And>index. axis<index \<Longrightarrow> index<4 \<Longrightarrow>
        comma_crt_axis_weight index mod period=0"
  shows "(offset+comma_crt_suffix axis phase) mod period =
    (offset+comma_crt_axis_weight axis *
      (phase mod comma_crt_axis_radix axis)) mod period"
proof -
  have later_zero: "comma_crt_suffix (Suc axis) phase mod period=0"
  proof (cases "axis=3")
    case True
    then show ?thesis by (simp add: comma_crt_suffix_def)
  next
    case False
    have later_axis: "Suc axis<4" using axis False by arith
    have later_weights:
      "\<And>index. Suc axis\<le>index \<Longrightarrow> index<4 \<Longrightarrow>
        comma_crt_axis_weight index mod period=0"
    proof -
      fix index :: nat
      assume lower: "Suc axis\<le>index" and upper: "index<4"
      have axis_less: "axis<index" using lower by arith
      show "comma_crt_axis_weight index mod period=0"
        by (rule higher_weights[OF axis_less upper])
    qed
    show ?thesis
      by (rule comma_crt_suffix_zero_if_weights_divide[OF later_axis later_weights])
  qed
  have suffix_step:
    "comma_crt_suffix axis phase =
      comma_crt_axis_weight axis * (phase mod comma_crt_axis_radix axis) +
        comma_crt_suffix (Suc axis) phase"
    by (rule comma_crt_suffix_step[OF axis])
  have suffix_mod:
    "comma_crt_suffix axis phase mod period =
      (comma_crt_axis_weight axis *
        (phase mod comma_crt_axis_radix axis)) mod period"
  proof -
    have "comma_crt_suffix axis phase mod period =
        ((comma_crt_axis_weight axis *
          (phase mod comma_crt_axis_radix axis)) mod period +
          (comma_crt_suffix (Suc axis) phase mod period)) mod period"
      unfolding suffix_step by (rule mod_add_eq[symmetric])
    also have "... =
        (comma_crt_axis_weight axis *
          (phase mod comma_crt_axis_radix axis)) mod period"
      using later_zero by simp
    finally show ?thesis .
  qed
  have "(offset+comma_crt_suffix axis phase) mod period =
      ((offset mod period)+(comma_crt_suffix axis phase mod period)) mod period"
    by (rule mod_add_eq[symmetric])
  also have "... =
      ((offset mod period) +
        ((comma_crt_axis_weight axis *
          (phase mod comma_crt_axis_radix axis)) mod period)) mod period"
    using suffix_mod by simp
  also have "... =
      (offset+comma_crt_axis_weight axis *
        (phase mod comma_crt_axis_radix axis)) mod period"
    by (rule mod_add_eq)
  finally show ?thesis .
qed

lemma comma_crt_terminal_selector_layer_bit:
  fixes axis period offset phase :: nat and rows :: "nat list"
  assumes axis: "axis<4" and positive: "0<period"
    and row_length: "length rows=period"
    and higher_weights:
      "\<And>index. axis<index \<Longrightarrow> index<4 \<Longrightarrow>
        comma_crt_axis_weight index mod period=0"
    and phase: "phase<924"
  shows "bit (comma_crt_terminal_selector_layer axis period offset rows) phase =
    bit (rows!((offset+comma_crt_suffix axis phase) mod period)) phase"
proof -
  let ?radix = "comma_crt_axis_radix axis"
  let ?children = "map (\<lambda>slot. comma_phase_word_cofactor axis slot
      (rows!((offset+comma_crt_axis_weight axis*slot) mod period)))
      [0..<?radix]"
  have radix_positive: "0<?radix"
    using comma_crt_axis_cases[OF axis]
    by (auto simp: comma_crt_axis_radix_def)
  have children_length: "length ?children=?radix" by simp
  have selected:
    "comma_phase_member (comma_crt_terminal_selector_layer axis period offset rows) phase =
      comma_phase_member (?children!(phase mod ?radix)) phase"
    unfolding comma_crt_terminal_selector_layer_def
    by (rule comma_indexed_phase_union_select[OF radix_positive children_length])
  have slot_bound: "phase mod ?radix<?radix"
    using radix_positive by simp
  have child:
    "?children!(phase mod ?radix) =
      comma_phase_word_cofactor axis (phase mod ?radix)
        (rows!((offset+comma_crt_axis_weight axis*(phase mod ?radix)) mod period))"
    using slot_bound by simp
  have selected_axis:
    "phase mod ?radix=phase mod comma_crt_axis_radix axis" by simp
  have cofactor_bit:
    "bit (comma_phase_word_cofactor axis (phase mod ?radix)
        (rows!((offset+comma_crt_axis_weight axis*(phase mod ?radix)) mod period))) phase =
      bit (rows!((offset+comma_crt_axis_weight axis*(phase mod ?radix)) mod period)) phase"
    by (rule comma_phase_word_cofactor_selected
      [OF axis slot_bound phase selected_axis])
  have index:
    "(offset+comma_crt_axis_weight axis*(phase mod ?radix)) mod period =
      (offset+comma_crt_suffix axis phase) mod period"
    using comma_crt_terminal_suffix_remainder
      [OF axis higher_weights, where phase=phase] by simp
  show ?thesis
    using selected child cofactor_bit index phase
    by (simp add: comma_phase_member_def)
qed

lemma comma_crt_select_terminal_quotient:
  fixes axis period offset :: nat and rows :: "nat list"
    and selector :: "nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat"
  assumes axis: "axis<4" and positive: "0<period"
    and row_length: "length rows=period"
    and higher_weights:
      "\<And>index. axis<index \<Longrightarrow> index<4 \<Longrightarrow>
        comma_crt_axis_weight index mod period=0"
    and selector_bounded:
      "take_bit 924 (selector period offset rows)=selector period offset rows"
    and selector_bit:
      "\<And>phase. phase<924 \<Longrightarrow>
        bit (selector period offset rows) phase =
          bit (rows!((offset+comma_crt_suffix axis phase) mod period)) phase"
  shows "selector period offset rows=
    comma_crt_terminal_selector_layer axis period offset rows"
proof (rule comma_crt_bounded_word_ext)
  show "take_bit 924 (selector period offset rows)=selector period offset rows"
    by (rule selector_bounded)
  show "take_bit 924 (comma_crt_terminal_selector_layer axis period offset rows)=
      comma_crt_terminal_selector_layer axis period offset rows"
    unfolding comma_crt_terminal_selector_layer_def
    by (rule comma_indexed_phase_union_bounded)
  fix phase :: nat
  assume phase: "phase<924"
  show "bit (selector period offset rows) phase =
      bit (comma_crt_terminal_selector_layer axis period offset rows) phase"
    using selector_bit[OF phase]
      comma_crt_terminal_selector_layer_bit[OF axis positive row_length
        higher_weights phase] by simp
qed

lemma comma_crt_select3_terminal_quotient:
  fixes period offset :: nat and rows :: "nat list"
  assumes positive: "0<period" and row_length: "length rows=period"
  shows "comma_crt_select3 period offset rows =
    comma_indexed_phase_union (\<lambda>slot phase. phase mod 11=slot)
      (map (\<lambda>slot. comma_phase_word_cofactor 3 slot
        (rows!((offset+comma_crt_axis_weight 3*slot) mod period))) [0..<11])"
proof -
  have higher:
    "\<And>index. 3<index \<Longrightarrow> index<4 \<Longrightarrow>
      comma_crt_axis_weight index mod period=0"
  proof -
    fix index :: nat
    assume lower: "3<index" and upper: "index<4"
    have impossible: False using lower upper by arith
    from impossible show
      "comma_crt_axis_weight index mod period=0" by simp
  qed
  have quotient:
    "comma_crt_select3 period offset rows=
      comma_crt_terminal_selector_layer 3 period offset rows"
  proof (rule comma_crt_select_terminal_quotient
    [where selector=comma_crt_select3])
    show "(3::nat)<4" by simp
    show "0<period" by (rule positive)
    show "length rows=period" by (rule row_length)
    show "\<And>index. 3<index \<Longrightarrow> index<4 \<Longrightarrow>
        comma_crt_axis_weight index mod period=0" by (rule higher)
    show "take_bit 924 (comma_crt_select3 period offset rows)=
        comma_crt_select3 period offset rows"
      by (rule comma_crt_select3_bounded)
    show "\<And>phase. phase<924 \<Longrightarrow>
        bit (comma_crt_select3 period offset rows) phase =
          bit (rows!((offset+comma_crt_suffix 3 phase) mod period)) phase"
      by (rule comma_crt_select3_bit[OF positive row_length])
  qed
  show ?thesis using quotient
    by (simp add: comma_crt_terminal_selector_layer_def comma_crt_axis_radix_def)
qed

lemma comma_crt_select2_terminal_quotient:
  fixes period offset :: nat and rows :: "nat list"
  assumes positive: "0<period" and row_length: "length rows=period"
    and weight3_zero: "comma_crt_axis_weight 3 mod period=0"
  shows "comma_crt_select2 period offset rows =
    comma_indexed_phase_union (\<lambda>slot phase. phase mod 7=slot)
      (map (\<lambda>slot. comma_phase_word_cofactor 2 slot
        (rows!((offset+comma_crt_axis_weight 2*slot) mod period))) [0..<7])"
proof -
  have higher:
    "\<And>index. 2<index \<Longrightarrow> index<4 \<Longrightarrow>
      comma_crt_axis_weight index mod period=0"
  proof -
    fix index :: nat
    assume lower: "2<index" and upper: "index<4"
    have index: "index=3" using lower upper by arith
    show "comma_crt_axis_weight index mod period=0"
      using weight3_zero index by simp
  qed
  have quotient:
    "comma_crt_select2 period offset rows=
      comma_crt_terminal_selector_layer 2 period offset rows"
  proof (rule comma_crt_select_terminal_quotient
    [where selector=comma_crt_select2])
    show "(2::nat)<4" by simp
    show "0<period" by (rule positive)
    show "length rows=period" by (rule row_length)
    show "\<And>index. 2<index \<Longrightarrow> index<4 \<Longrightarrow>
        comma_crt_axis_weight index mod period=0" by (rule higher)
    show "take_bit 924 (comma_crt_select2 period offset rows)=
        comma_crt_select2 period offset rows"
      by (rule comma_crt_select2_bounded)
    show "\<And>phase. phase<924 \<Longrightarrow>
        bit (comma_crt_select2 period offset rows) phase =
          bit (rows!((offset+comma_crt_suffix 2 phase) mod period)) phase"
      by (rule comma_crt_select2_bit[OF positive row_length])
  qed
  show ?thesis using quotient
    by (simp add: comma_crt_terminal_selector_layer_def comma_crt_axis_radix_def)
qed

lemma comma_crt_select1_terminal_quotient:
  fixes period offset :: nat and rows :: "nat list"
  assumes positive: "0<period" and row_length: "length rows=period"
    and weight2_zero: "comma_crt_axis_weight 2 mod period=0"
    and weight3_zero: "comma_crt_axis_weight 3 mod period=0"
  shows "comma_crt_select1 period offset rows =
    comma_indexed_phase_union (\<lambda>slot phase. phase mod 3=slot)
      (map (\<lambda>slot. comma_phase_word_cofactor 1 slot
        (rows!((offset+comma_crt_axis_weight 1*slot) mod period))) [0..<3])"
proof -
  have higher:
    "\<And>index. 1<index \<Longrightarrow> index<4 \<Longrightarrow>
      comma_crt_axis_weight index mod period=0"
  proof -
    fix index :: nat
    assume lower: "1<index" and upper: "index<4"
    have index: "index=2 \<or> index=3" using lower upper by arith
    show "comma_crt_axis_weight index mod period=0"
      using weight2_zero weight3_zero index by auto
  qed
  have quotient:
    "comma_crt_select1 period offset rows=
      comma_crt_terminal_selector_layer 1 period offset rows"
  proof (rule comma_crt_select_terminal_quotient
    [where selector=comma_crt_select1])
    show "(1::nat)<4" by simp
    show "0<period" by (rule positive)
    show "length rows=period" by (rule row_length)
    show "\<And>index. 1<index \<Longrightarrow> index<4 \<Longrightarrow>
        comma_crt_axis_weight index mod period=0" by (rule higher)
    show "take_bit 924 (comma_crt_select1 period offset rows)=
        comma_crt_select1 period offset rows"
      by (rule comma_crt_select1_bounded)
    show "\<And>phase. phase<924 \<Longrightarrow>
        bit (comma_crt_select1 period offset rows) phase =
          bit (rows!((offset+comma_crt_suffix 1 phase) mod period)) phase"
      by (rule comma_crt_select1_bit[OF positive row_length])
  qed
  show ?thesis using quotient
    by (simp add: comma_crt_terminal_selector_layer_def comma_crt_axis_radix_def)
qed

lemma comma_crt_select0_terminal_quotient:
  fixes period offset :: nat and rows :: "nat list"
  assumes positive: "0<period" and row_length: "length rows=period"
    and weight1_zero: "comma_crt_axis_weight 1 mod period=0"
    and weight2_zero: "comma_crt_axis_weight 2 mod period=0"
    and weight3_zero: "comma_crt_axis_weight 3 mod period=0"
  shows "comma_crt_select0 period offset rows =
    comma_indexed_phase_union (\<lambda>slot phase. phase mod 4=slot)
      (map (\<lambda>slot. comma_phase_word_cofactor 0 slot
        (rows!((offset+comma_crt_axis_weight 0*slot) mod period))) [0..<4])"
proof -
  have higher:
    "\<And>index. 0<index \<Longrightarrow> index<4 \<Longrightarrow>
      comma_crt_axis_weight index mod period=0"
  proof -
    fix index :: nat
    assume lower: "0<index" and upper: "index<4"
    have index: "index=1 \<or> index=2 \<or> index=3" using lower upper by arith
    show "comma_crt_axis_weight index mod period=0"
      using weight1_zero weight2_zero weight3_zero index by auto
  qed
  have quotient:
    "comma_crt_select0 period offset rows=
      comma_crt_terminal_selector_layer 0 period offset rows"
  proof (rule comma_crt_select_terminal_quotient
    [where selector=comma_crt_select0])
    show "(0::nat)<4" by simp
    show "0<period" by (rule positive)
    show "length rows=period" by (rule row_length)
    show "\<And>index. 0<index \<Longrightarrow> index<4 \<Longrightarrow>
        comma_crt_axis_weight index mod period=0" by (rule higher)
    show "take_bit 924 (comma_crt_select0 period offset rows)=
        comma_crt_select0 period offset rows"
      by (rule comma_crt_select0_bounded)
    show "\<And>phase. phase<924 \<Longrightarrow>
        bit (comma_crt_select0 period offset rows) phase =
          bit (rows!((offset+comma_crt_suffix 0 phase) mod period)) phase"
      by (rule comma_crt_select0_bit[OF positive row_length])
  qed
  show ?thesis using quotient
    by (simp add: comma_crt_terminal_selector_layer_def comma_crt_axis_radix_def)
qed

ML \<open>
  val comma_crt_selector_projection_rules = @{thms
    comma_crt_zero_weight_suffix comma_crt_zero_weight_index
    comma_crt_modular_translation
    comma_crt_cofactor_leaf_rows
    comma_crt_word_prefix_independent_mono
    comma_crt_word_prefix_independent_at
    comma_crt_word_prefix_independent_zero
    comma_crt_word_prefix_independent_full
    comma_crt_word_prefix_independent_indexed_union
    comma_crt_word_prefix_independent_indexed_union_q
    comma_crt_select3_skip comma_crt_select2_skip
    comma_crt_select1_skip comma_crt_select0_skip
    comma_crt_terminal_suffix_remainder comma_crt_terminal_selector_layer_bit
    comma_crt_select_terminal_quotient
    comma_crt_select3_terminal_quotient comma_crt_select2_terminal_quotient
    comma_crt_select1_terminal_quotient comma_crt_select0_terminal_quotient};
  Thm.consolidate comma_crt_selector_projection_rules;
  Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "CRT selector projection" comma_crt_selector_projection_rules;
  if null (Thm_Deps.all_oracles comma_crt_selector_projection_rules)
  then () else error "CRT selector projection depends on an oracle"
\<close>

end
