theory Comma_Semantic_B1_CRT_Indexed_Labels
  imports Comma_Semantic_B1_CRT_Labelled_Selector
begin

text \<open>
False columns are removed by stable indexed filtering, never by a set or a
value-based distinct operation.  The position list is occurrence data; the
compact MDD labels are rebased through it when a child selector is joined to
its parent.  This theory supplies the executable compression and the exact
selector/fiber transport needed by the labelled zipper.
\<close>

fun comma_semantic_b1_crt_indexed_nonfalse_from ::
    "nat \<Rightarrow> comma_crt_column list \<Rightarrow>
      (nat \<times> comma_crt_column) list" where
  "comma_semantic_b1_crt_indexed_nonfalse_from offset [] = []"
| "comma_semantic_b1_crt_indexed_nonfalse_from offset (column#columns) =
    (if column=Comma_CRT_Bool False then
       comma_semantic_b1_crt_indexed_nonfalse_from (Suc offset) columns
     else (offset,column)#
       comma_semantic_b1_crt_indexed_nonfalse_from (Suc offset) columns)"

definition comma_semantic_b1_crt_indexed_nonfalse_positions ::
    "comma_crt_column list \<Rightarrow> nat list" where
  "comma_semantic_b1_crt_indexed_nonfalse_positions columns =
    map fst (comma_semantic_b1_crt_indexed_nonfalse_from 0 columns)"

definition comma_semantic_b1_crt_indexed_nonfalse_columns ::
    "comma_crt_column list \<Rightarrow> comma_crt_column list" where
  "comma_semantic_b1_crt_indexed_nonfalse_columns columns =
    map snd (comma_semantic_b1_crt_indexed_nonfalse_from 0 columns)"

lemma comma_semantic_b1_crt_indexed_nonfalse_from_drop_false:
  "map snd (comma_semantic_b1_crt_indexed_nonfalse_from offset columns) =
    comma_semantic_b1_crt_partition_drop_false columns"
  by (induction columns arbitrary: offset)
    (auto simp: comma_semantic_b1_crt_partition_drop_false.simps)

lemma comma_semantic_b1_crt_indexed_nonfalse_columns_drop_false:
  "comma_semantic_b1_crt_indexed_nonfalse_columns columns =
    comma_semantic_b1_crt_partition_drop_false columns"
  by (simp add: comma_semantic_b1_crt_indexed_nonfalse_columns_def
      comma_semantic_b1_crt_indexed_nonfalse_from_drop_false)

lemma comma_semantic_b1_crt_indexed_nonfalse_from_lower:
  "list_all (\<lambda>entry. offset\<le>fst entry)
    (comma_semantic_b1_crt_indexed_nonfalse_from offset columns)"
proof (induction columns arbitrary: offset)
  case Nil
  then show ?case by simp
next
  case (Cons column columns)
  have tail: "list_all (\<lambda>entry. Suc offset\<le>fst entry)
      (comma_semantic_b1_crt_indexed_nonfalse_from (Suc offset) columns)"
    by (rule Cons.IH)
  have lower: "list_all (\<lambda>entry. offset\<le>fst entry)
      (comma_semantic_b1_crt_indexed_nonfalse_from (Suc offset) columns)"
    using tail by (auto simp: list_all_iff dest: Suc_leD)
  show ?case using lower by (cases "column=Comma_CRT_Bool False") simp_all
qed

lemma comma_semantic_b1_crt_indexed_nonfalse_positions_distinct:
  "distinct (comma_semantic_b1_crt_indexed_nonfalse_positions columns)"
proof -
  have distinct_from:
    "distinct (map fst
      (comma_semantic_b1_crt_indexed_nonfalse_from offset columns))"
    for offset
  proof (induction columns arbitrary: offset)
    case Nil
    then show ?case by simp
  next
    case (Cons column columns)
    show ?case
    proof (cases "column=Comma_CRT_Bool False")
      case True
      then show ?thesis using Cons.IH[of "Suc offset"] by simp
    next
      case False
      have tail_distinct:
        "distinct (map fst
          (comma_semantic_b1_crt_indexed_nonfalse_from (Suc offset) columns))"
        by (rule Cons.IH)
      have offset_not_tail:
        "offset \<notin> set (map fst
          (comma_semantic_b1_crt_indexed_nonfalse_from (Suc offset) columns))"
      proof
        assume member:
          "offset \<in> set (map fst
            (comma_semantic_b1_crt_indexed_nonfalse_from (Suc offset) columns))"
        then obtain entry where entry:
          "entry\<in>set (comma_semantic_b1_crt_indexed_nonfalse_from
            (Suc offset) columns)" and fst: "fst entry=offset"
          by auto
        have lower:
          "Suc offset\<le>fst entry"
          using comma_semantic_b1_crt_indexed_nonfalse_from_lower[of
              "Suc offset" columns]
          entry by (auto simp: list_all_iff)
        show False using lower fst by simp
      qed
      show ?thesis using False tail_distinct offset_not_tail by simp
    qed
  qed
  show ?thesis
    unfolding comma_semantic_b1_crt_indexed_nonfalse_positions_def
    by (rule distinct_from)
qed

lemma comma_semantic_b1_crt_indexed_nonfalse_from_entry:
  assumes member:
    "(index,column)\<in>set
      (comma_semantic_b1_crt_indexed_nonfalse_from offset columns)"
  shows "offset\<le>index \<and>
    index<offset+length columns \<and>
    columns!(index-offset)=column"
  using member
proof (induction columns arbitrary: offset)
  case Nil
  then show ?case by simp
next
  case (Cons head tail)
  show ?case
  proof (cases "head=Comma_CRT_Bool False")
    case True
    have tail_member:
      "(index,column)\<in>set
        (comma_semantic_b1_crt_indexed_nonfalse_from (Suc offset) tail)"
      using Cons.prems True by simp
    have ih:
      "Suc offset\<le>index \<and>
       index<Suc offset+length tail \<and>
       tail!(index-Suc offset)=column"
      by (rule Cons.IH[OF tail_member])
    have difference: "index-offset=Suc (index-Suc offset)"
      using ih by arith
    show ?thesis using ih difference by (simp add: nth_Cons')
  next
    case False
    have pair_cases:
      "(index,column)=(offset,head) \<or>
       (index,column)\<in>set
         (comma_semantic_b1_crt_indexed_nonfalse_from (Suc offset) tail)"
      using Cons.prems False by auto
    then show ?thesis
    proof
      assume pair: "(index,column)=(offset,head)"
      then show ?thesis using False by (auto simp: nth_Cons')
    next
      assume tail_member:
        "(index,column)\<in>set
          (comma_semantic_b1_crt_indexed_nonfalse_from (Suc offset) tail)"
      have ih:
        "Suc offset\<le>index \<and>
         index<Suc offset+length tail \<and>
         tail!(index-Suc offset)=column"
        by (rule Cons.IH[OF tail_member])
      have difference: "index-offset=Suc (index-Suc offset)"
        using ih by arith
      show ?thesis using ih difference by (simp add: nth_Cons')
    qed
  qed
qed

lemma comma_semantic_b1_crt_indexed_nonfalse_from_complete:
  assumes bound: "index<length columns"
    and active: "columns!index\<noteq>Comma_CRT_Bool False"
  shows "offset+index\<in>set
    (map fst (comma_semantic_b1_crt_indexed_nonfalse_from offset columns))"
  using bound active
proof (induction columns arbitrary: offset index)
  case Nil
  then show ?case by simp
next
  case (Cons column columns)
  show ?case
  proof (cases index)
    case 0
    then show ?thesis using Cons.prems by simp
  next
    case (Suc j)
    have j_bound: "j<length columns" using Cons.prems(1) Suc by simp
    have j_active: "columns!j\<noteq>Comma_CRT_Bool False"
      using Cons.prems(2) Suc by simp
    have j_member:
      "Suc offset+j\<in>set
        (map fst (comma_semantic_b1_crt_indexed_nonfalse_from (Suc offset) columns))"
      by (rule Cons.IH[OF j_bound j_active])
    show ?thesis using Suc j_member by (cases "column=Comma_CRT_Bool False") auto
  qed
qed

lemma comma_semantic_b1_crt_indexed_nonfalse_embedding:
  fixes columns :: "comma_crt_column list"
  defines "positions \<equiv>
      comma_semantic_b1_crt_indexed_nonfalse_positions columns"
    and "compact \<equiv>
      comma_semantic_b1_crt_indexed_nonfalse_columns columns"
  shows "length positions=length compact"
    "distinct positions"
    "\<forall>j<length compact. positions!j<length columns \<and>
      columns!(positions!j)=compact!j"
    "\<forall>i<length columns. i\<notin>set positions \<longrightarrow>
      columns!i=Comma_CRT_Bool False"
proof -
  show "length positions=length compact"
    by (simp add: positions_def compact_def comma_semantic_b1_crt_indexed_nonfalse_positions_def
      comma_semantic_b1_crt_indexed_nonfalse_columns_def)
  show "distinct positions"
    by (simp add: positions_def
      comma_semantic_b1_crt_indexed_nonfalse_positions_distinct)
  show "\<forall>j<length compact. positions!j<length columns \<and>
      columns!(positions!j)=compact!j"
  proof (intro allI impI)
    fix j
    assume bound: "j<length compact"
    let ?pairs="comma_semantic_b1_crt_indexed_nonfalse_from 0 columns"
    have pair_bound: "j<length ?pairs" using bound by (simp add: compact_def
      comma_semantic_b1_crt_indexed_nonfalse_columns_def)
    have pair: "?pairs!j\<in>set ?pairs" by (rule nth_mem[OF pair_bound])
    have position: "positions!j=fst (?pairs!j)"
      by (simp add: positions_def comma_semantic_b1_crt_indexed_nonfalse_positions_def
        nth_map[OF pair_bound])
    have compact_value: "compact!j=snd (?pairs!j)"
      by (simp add: compact_def comma_semantic_b1_crt_indexed_nonfalse_columns_def
        nth_map[OF pair_bound])
    obtain index column where pair_eq: "?pairs!j=(index,column)"
      by (cases "?pairs!j") auto
    have pair_member: "(index,column)\<in>set ?pairs"
      using pair pair_eq by simp
    have pair_facts:
      "0\<le>index \<and> index<0+length columns \<and>
        columns!(index-0)=column"
      by (rule comma_semantic_b1_crt_indexed_nonfalse_from_entry[OF pair_member])
    have aligned: "index<length columns \<and> columns!index=column"
      using pair_facts by simp
    show "positions!j<length columns \<and> columns!(positions!j)=compact!j"
      using aligned position compact_value pair_eq by simp
  qed
  show "\<forall>i<length columns. i\<notin>set positions \<longrightarrow>
      columns!i=Comma_CRT_Bool False"
  proof (intro allI impI impI)
    fix i
    assume bound: "i<length columns" and absent: "i\<notin>set positions"
    show "columns!i=Comma_CRT_Bool False"
    proof (rule ccontr)
      assume not_false: "columns!i\<noteq>Comma_CRT_Bool False"
      have active:
        "i\<in>set (map fst
          (comma_semantic_b1_crt_indexed_nonfalse_from 0 columns))"
        using comma_semantic_b1_crt_indexed_nonfalse_from_complete[OF bound not_false, of 0]
        by simp
      show False using absent active
        by (simp add: positions_def comma_semantic_b1_crt_indexed_nonfalse_positions_def)
    qed
  qed
qed

definition comma_semantic_b1_crt_indexed_embedding ::
    "nat list \<Rightarrow> comma_crt_column list \<Rightarrow>
      comma_crt_column list \<Rightarrow> bool" where
  "comma_semantic_b1_crt_indexed_embedding positions compact full \<longleftrightarrow>
    length positions=length compact \<and> distinct positions \<and>
    comma_semantic_b1_crt_partition_drop_false compact =
      comma_semantic_b1_crt_partition_drop_false full \<and>
    (\<forall>j<length compact. positions!j<length full \<and>
      full!(positions!j)=compact!j) \<and>
    (\<forall>i<length full. i\<notin>set positions \<longrightarrow>
      full!i=Comma_CRT_Bool False)"

lemma comma_semantic_b1_crt_indexed_compression_embedding:
  "comma_semantic_b1_crt_indexed_embedding
      (comma_semantic_b1_crt_indexed_nonfalse_positions columns)
      (comma_semantic_b1_crt_indexed_nonfalse_columns columns) columns"
  using comma_semantic_b1_crt_indexed_nonfalse_embedding[of columns]
    comma_semantic_b1_crt_indexed_nonfalse_columns_drop_false[of columns]
  by (auto simp: comma_semantic_b1_crt_indexed_embedding_def
      comma_semantic_b1_crt_partition_drop_false_idempotent)

lemma comma_semantic_b1_crt_indexed_embedding_cofactor:
  assumes embed:
    "comma_semantic_b1_crt_indexed_embedding positions compact full"
  shows "comma_semantic_b1_crt_indexed_embedding positions
      (map (comma_crt_cofactor_or_false level digit) compact)
      (map (comma_crt_cofactor_or_false level digit) full)"
proof -
  have parts:
    "length positions=length compact"
    "distinct positions"
    "comma_semantic_b1_crt_partition_drop_false compact =
      comma_semantic_b1_crt_partition_drop_false full"
    "\<forall>j<length compact. positions!j<length full \<and>
      full!(positions!j)=compact!j"
    "\<forall>i<length full. i\<notin>set positions \<longrightarrow>
      full!i=Comma_CRT_Bool False"
    using embed by (auto simp: comma_semantic_b1_crt_indexed_embedding_def)
  have compact_drop:
    "comma_semantic_b1_crt_partition_drop_false
       (map (comma_crt_cofactor_or_false level digit) compact) =
     comma_semantic_b1_crt_partition_drop_false
       (map (comma_crt_cofactor_or_false level digit)
         (comma_semantic_b1_crt_partition_drop_false compact))"
    using comma_semantic_b1_crt_partition_drop_false_cofactor[of level digit compact]
    by simp
  have full_drop:
    "comma_semantic_b1_crt_partition_drop_false
       (map (comma_crt_cofactor_or_false level digit)
         (comma_semantic_b1_crt_partition_drop_false full)) =
     comma_semantic_b1_crt_partition_drop_false
       (map (comma_crt_cofactor_or_false level digit) full)"
    by (rule comma_semantic_b1_crt_partition_drop_false_cofactor)
  have common_drop:
    "comma_semantic_b1_crt_partition_drop_false
       (map (comma_crt_cofactor_or_false level digit) compact) =
     comma_semantic_b1_crt_partition_drop_false
       (map (comma_crt_cofactor_or_false level digit) full)"
    using compact_drop full_drop parts(3) by simp
  show ?thesis
    using parts(1,2,4,5) common_drop
    by (auto simp: comma_semantic_b1_crt_indexed_embedding_def nth_map
        comma_crt_cofactor_or_false_def)
qed

lemma comma_semantic_b1_crt_indexed_checker_preserved:
  "comma_semantic_b1_crt_partition_cofactor_checked levels
      (comma_semantic_b1_crt_indexed_nonfalse_columns columns) =
    comma_semantic_b1_crt_partition_cofactor_checked levels columns"
  by (simp add: comma_semantic_b1_crt_indexed_nonfalse_columns_drop_false
      comma_semantic_b1_crt_partition_checker_drop_false)

lemma comma_semantic_b1_crt_indexed_child_compact_exact:
  "comma_semantic_b1_crt_partition_drop_false
      (map (comma_crt_cofactor_or_false level digit)
        (comma_semantic_b1_crt_indexed_nonfalse_columns columns)) =
    comma_semantic_b1_crt_indexed_nonfalse_columns
      (map (comma_crt_cofactor_or_false level digit) columns)"
  by (simp add: comma_semantic_b1_crt_indexed_nonfalse_columns_drop_false
      comma_semantic_b1_crt_partition_drop_false_cofactor)

primrec comma_semantic_b1_crt_mdd_map_payload ::
    "('a \<Rightarrow> 'b) \<Rightarrow> 'a comma_crt_mdd \<Rightarrow> 'b comma_crt_mdd" where
  "comma_semantic_b1_crt_mdd_map_payload f (Comma_CRT_MDD_Leaf value) =
    Comma_CRT_MDD_Leaf (f value)"
| "comma_semantic_b1_crt_mdd_map_payload f (Comma_CRT_MDD_Node level children) =
    comma_crt_mdd_node level
      (map (comma_semantic_b1_crt_mdd_map_payload f) children)"

lemma comma_semantic_b1_crt_mdd_map_payload_admitted:
  assumes admitted: "comma_crt_mdd_admitted lower selector"
  shows "comma_crt_mdd_admitted lower
    (comma_semantic_b1_crt_mdd_map_payload f selector)"
  using admitted
proof (induction selector arbitrary: lower)
  case (Comma_CRT_MDD_Leaf payload)
  then show ?case by simp
next
  case (Comma_CRT_MDD_Node level children)
  have order: "lower\<le>level"
    and level: "level<4"
    and width: "length children=comma_crt_period level"
    and children_admitted:
      "list_all (comma_crt_mdd_admitted (Suc level)) children"
    using Comma_CRT_MDD_Node.prems by auto
  have mapped_children:
      "list_all (comma_crt_mdd_admitted (Suc level))
        (map (comma_semantic_b1_crt_mdd_map_payload f) children)"
  proof -
    have each:
        "comma_crt_mdd_admitted (Suc level)
          (comma_semantic_b1_crt_mdd_map_payload f child)"
      if member: "child\<in>set children" for child
    proof -
      have child_admitted: "comma_crt_mdd_admitted (Suc level) child"
        using children_admitted member by (simp add: list_all_iff)
      show ?thesis by (rule Comma_CRT_MDD_Node.IH[OF member child_admitted])
    qed
    show ?thesis using each by (simp add: list_all_iff)
  qed
  have mapped_width:
      "length (map (comma_semantic_b1_crt_mdd_map_payload f) children)=
        comma_crt_period level" using width by simp
  show ?case
    unfolding comma_semantic_b1_crt_mdd_map_payload.simps
    by (rule comma_crt_mdd_node_admitted[OF order level mapped_width mapped_children])
qed

lemma comma_semantic_b1_crt_mdd_map_payload_eval:
  assumes admitted: "comma_crt_mdd_admitted lower selector"
  shows "comma_crt_mdd_eval phase
      (comma_semantic_b1_crt_mdd_map_payload f selector) =
    map_option f (comma_crt_mdd_eval phase selector)"
  using admitted
proof (induction selector arbitrary: lower phase)
  case (Comma_CRT_MDD_Leaf payload)
  then show ?case by simp
next
  case (Comma_CRT_MDD_Node level children)
  have level: "level<4"
    and width: "length children=comma_crt_period level"
    and children_admitted:
      "list_all (comma_crt_mdd_admitted (Suc level)) children"
    using Comma_CRT_MDD_Node.prems by auto
  have digit_bound: "phase mod comma_crt_period level<length children"
    using comma_crt_period_positive[OF level] width by simp
  let ?digit="phase mod comma_crt_period level"
  have selected_admitted:
      "comma_crt_mdd_admitted (Suc level) (children!?digit)"
    using children_admitted nth_mem[OF digit_bound] by (auto simp: list_all_iff)
  have selected_member: "children!?digit\<in>set children"
    by (rule nth_mem[OF digit_bound])
  have selected_ih:
      "comma_crt_mdd_eval phase
          (comma_semantic_b1_crt_mdd_map_payload f (children!?digit)) =
        map_option f (comma_crt_mdd_eval phase (children!?digit))"
    by (rule Comma_CRT_MDD_Node.IH[OF selected_member selected_admitted])
  have mapped_node:
      "comma_crt_mdd_eval phase
        (comma_crt_mdd_node level
          (map (comma_semantic_b1_crt_mdd_map_payload f) children)) =
       comma_crt_mdd_eval phase
          (comma_semantic_b1_crt_mdd_map_payload f (children!?digit))"
    by (rule comma_crt_mdd_node_map_projection_eval[OF level width])
  have source_node:
      "comma_crt_mdd_eval phase (Comma_CRT_MDD_Node level children) =
        comma_crt_mdd_eval phase (children!?digit)"
    using level width digit_bound by (simp add: comma_crt_mdd_eval_node_selected)
  show ?case
    using mapped_node selected_ih source_node by simp
qed

definition comma_semantic_b1_crt_indexed_rebase_label ::
    "nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_semantic_b1_crt_indexed_rebase_label positions full_width index =
    (if index<length positions then positions!index else full_width+index)"

definition comma_semantic_b1_crt_indexed_rebase_selector ::
    "nat list \<Rightarrow> nat \<Rightarrow>
      nat option comma_crt_mdd \<Rightarrow> nat option comma_crt_mdd" where
  "comma_semantic_b1_crt_indexed_rebase_selector positions full_width selector =
    comma_semantic_b1_crt_mdd_map_payload
      (map_option (comma_semantic_b1_crt_indexed_rebase_label positions full_width))
      selector"

lemma comma_semantic_b1_crt_indexed_rebase_selector_admitted:
  assumes admitted: "comma_crt_mdd_admitted lower selector"
  shows "comma_crt_mdd_admitted lower
    (comma_semantic_b1_crt_indexed_rebase_selector positions full_width selector)"
  unfolding comma_semantic_b1_crt_indexed_rebase_selector_def
  by (rule comma_semantic_b1_crt_mdd_map_payload_admitted[OF admitted])

lemma comma_semantic_b1_crt_indexed_rebase_selector_eval:
  assumes admitted: "comma_crt_mdd_admitted lower selector"
  shows "comma_crt_mdd_eval phase
      (comma_semantic_b1_crt_indexed_rebase_selector positions full_width selector) =
    map_option
      (map_option (comma_semantic_b1_crt_indexed_rebase_label positions full_width))
      (comma_crt_mdd_eval phase selector)"
  unfolding comma_semantic_b1_crt_indexed_rebase_selector_def
  by (rule comma_semantic_b1_crt_mdd_map_payload_eval[OF admitted])

lemma comma_semantic_b1_crt_indexed_rebase_matches:
  assumes embed:
      "comma_semantic_b1_crt_indexed_embedding positions compact full"
    and i: "i<length full"
  shows "comma_semantic_b1_crt_indexed_rebase_label positions (length full) index=i
    \<longleftrightarrow> index<length positions \<and> positions!index=i"
proof
  assume equal:
    "comma_semantic_b1_crt_indexed_rebase_label positions (length full) index=i"
  have parts:
    "length positions=length compact"
    "distinct positions"
    "comma_semantic_b1_crt_partition_drop_false compact =
      comma_semantic_b1_crt_partition_drop_false full"
    "\<forall>j<length compact. positions!j<length full \<and>
      full!(positions!j)=compact!j"
    "\<forall>j<length full. j\<notin>set positions \<longrightarrow>
      full!j=Comma_CRT_Bool False"
    using embed by (auto simp: comma_semantic_b1_crt_indexed_embedding_def)
  show "index<length positions \<and> positions!index=i"
  proof (cases "index<length positions")
    case True
    then show ?thesis using equal by (simp add:
      comma_semantic_b1_crt_indexed_rebase_label_def)
  next
    case False
    have lower: "length full\<le>
        comma_semantic_b1_crt_indexed_rebase_label positions (length full) index"
      using False by (simp add: comma_semantic_b1_crt_indexed_rebase_label_def)
    have i_lower: "length full\<le>i" using lower equal by simp
    have contradiction: False using i_lower i by arith
    then show ?thesis by blast
  qed
next
  assume selected:
    "index<length positions \<and> positions!index=i"
  then show
    "comma_semantic_b1_crt_indexed_rebase_label positions (length full) index=i"
    by (simp add: comma_semantic_b1_crt_indexed_rebase_label_def)
qed


lemma comma_semantic_b1_crt_indexed_embedding_admitted:
  assumes embed:
    "comma_semantic_b1_crt_indexed_embedding positions compact full"
    and compact_admitted:
      "list_all (comma_crt_admitted level) compact"
  shows "list_all (comma_crt_admitted level) full"
proof (unfold list_all_iff, intro ballI)
  fix column
  assume member: "column\<in>set full"
  then obtain i where bound: "i<length full" and column:
      "column=full!i"
    by (auto simp: in_set_conv_nth)
  have parts:
    "length positions=length compact"
    "distinct positions"
    "comma_semantic_b1_crt_partition_drop_false compact =
      comma_semantic_b1_crt_partition_drop_false full"
    "\<forall>j<length compact. positions!j<length full \<and>
      full!(positions!j)=compact!j"
    "\<forall>i<length full. i\<notin>set positions \<longrightarrow>
      full!i=Comma_CRT_Bool False"
    using embed by (auto simp: comma_semantic_b1_crt_indexed_embedding_def)
  show "comma_crt_admitted level column"
  proof (cases "i\<in>set positions")
    case True
    then obtain j where j_bound: "j<length positions"
      and j_value: "positions!j=i"
      by (auto simp: in_set_conv_nth)
    have compact_bound: "j<length compact" using j_bound parts(1) by simp
    have aligned: "full!i=compact!j"
      using parts(4)[rule_format, OF compact_bound] j_value by simp
    have admitted: "comma_crt_admitted level (compact!j)"
      using compact_admitted compact_bound by (simp add: list_all_iff)
    show ?thesis using column aligned admitted by simp
  next
    case False
    have false_column: "full!i=Comma_CRT_Bool False"
      using parts(5)[rule_format, OF bound] False by blast
    show ?thesis using column false_column by simp
  qed
qed

lemma comma_semantic_b1_crt_indexed_embedding_has_node:
  assumes embed:
    "comma_semantic_b1_crt_indexed_embedding positions compact full"
  shows "comma_semantic_b1_crt_partition_has_node_at level compact =
    comma_semantic_b1_crt_partition_has_node_at level full"
proof -
  have parts:
    "comma_semantic_b1_crt_partition_drop_false compact =
      comma_semantic_b1_crt_partition_drop_false full"
    using embed by (simp add: comma_semantic_b1_crt_indexed_embedding_def)
  have compact_drop:
    "comma_semantic_b1_crt_partition_has_node_at level compact =
      comma_semantic_b1_crt_partition_has_node_at level
        (comma_semantic_b1_crt_partition_drop_false compact)"
    by (rule comma_semantic_b1_crt_partition_has_node_drop_false[symmetric])
  have full_drop:
    "comma_semantic_b1_crt_partition_has_node_at level full =
      comma_semantic_b1_crt_partition_has_node_at level
        (comma_semantic_b1_crt_partition_drop_false full)"
    by (rule comma_semantic_b1_crt_partition_has_node_drop_false[symmetric])
  show ?thesis using compact_drop full_drop parts by simp
qed

lemma comma_semantic_b1_crt_mdd_map_payload_node:
  "comma_semantic_b1_crt_mdd_map_payload f (comma_crt_mdd_node level children) =
   comma_crt_mdd_node level
     (map (comma_semantic_b1_crt_mdd_map_payload f) children)"
proof (cases children)
  case Nil
  then show ?thesis by (simp add: comma_crt_mdd_node_def)
next
  case (Cons head tail)
  show ?thesis
  proof (cases "list_all (\<lambda>child. child=head) (head#tail)")
    case True
    have mapped_uniform:
      "list_all (\<lambda>child.
        comma_semantic_b1_crt_mdd_map_payload f child =
          comma_semantic_b1_crt_mdd_map_payload f head) (head#tail)"
      using True by (auto simp: list_all_iff)
    have mapped_tail:
      "list_all (\<lambda>child.
        comma_semantic_b1_crt_mdd_map_payload f child =
          comma_semantic_b1_crt_mdd_map_payload f head) tail"
      using mapped_uniform by (simp add: list_all_iff)
    have mapped_all:
      "list_all (\<lambda>child.
        child=comma_semantic_b1_crt_mdd_map_payload f head)
        (map (comma_semantic_b1_crt_mdd_map_payload f) (head#tail))"
      using mapped_tail by (simp add: list_all_iff)
    show ?thesis using Cons True mapped_all
      by (simp add: comma_crt_mdd_node_def)
  next
    case False
    then show ?thesis using Cons
      by (simp add: comma_crt_mdd_node_def)
  qed
qed

lemma comma_semantic_b1_crt_indexed_labelled_zip_witness_lift:
  assumes witness:
    "comma_semantic_b1_crt_labelled_zip_witness level columns selector"
  shows "\<forall>positions full.
    comma_semantic_b1_crt_indexed_embedding positions columns full \<longrightarrow>
    comma_semantic_b1_crt_labelled_zip_witness level full
      (comma_semantic_b1_crt_indexed_rebase_selector positions (length full) selector)"
  using witness
proof (induction rule: comma_semantic_b1_crt_labelled_zip_witness.induct)
  case (labelled_zip_terminal index columns level)
  show ?case
  proof (intro allI impI)
    fix positions full
    assume embed:
      "comma_semantic_b1_crt_indexed_embedding positions columns full"
    have parts:
      "length positions=length columns"
      "distinct positions"
      "comma_semantic_b1_crt_partition_drop_false columns =
        comma_semantic_b1_crt_partition_drop_false full"
      "\<forall>j<length columns. positions!j<length full \<and>
        full!(positions!j)=columns!j"
      "\<forall>i<length full. i\<notin>set positions \<longrightarrow>
        full!i=Comma_CRT_Bool False"
      using embed by (auto simp: comma_semantic_b1_crt_indexed_embedding_def)
    have index_bound: "index<length positions"
      using labelled_zip_terminal.hyps(1) parts(1) by simp
    have label_value:
      "comma_semantic_b1_crt_indexed_rebase_label positions (length full) index =
        positions!index"
      using index_bound
      by (simp add: comma_semantic_b1_crt_indexed_rebase_label_def)
    have target_index_bound:
        "comma_semantic_b1_crt_indexed_rebase_label positions (length full) index <
          length full"
      using parts(4)[rule_format, OF labelled_zip_terminal.hyps(1)]
        label_value by simp
    have one_hot:
      "full!i = Comma_CRT_Bool
        (i=comma_semantic_b1_crt_indexed_rebase_label positions (length full) index)"
      if i_bound: "i<length full" for i
    proof (cases "i\<in>set positions")
      case True
      then obtain j where j_bound: "j<length positions"
        and j_value: "positions!j=i"
        by (auto simp: in_set_conv_nth)
      have compact_bound: "j<length columns"
        using j_bound parts(1) by simp
      have aligned: "full!i=columns!j"
        using parts(4)[rule_format, OF compact_bound] j_value by simp
      have position_eq:
          "positions!j=positions!index \<longleftrightarrow> j=index"
        using parts(2) j_bound index_bound
        by (auto simp: distinct_conv_nth)
      have "columns!j=Comma_CRT_Bool (j=index)"
        using labelled_zip_terminal.hyps(2)[OF compact_bound] .
      then show ?thesis
        using aligned j_value label_value position_eq by simp
    next
      case False
      have full_false:
          "full!i=Comma_CRT_Bool False"
        using parts(5)[rule_format, OF i_bound] False by blast
      have selected: "positions!index\<in>set positions"
        using index_bound by (auto simp: in_set_conv_nth)
      have i_neq: "i\<noteq>positions!index"
        using False selected by blast
      show ?thesis using full_false label_value i_neq by simp
    qed
    have source_selector:
      "comma_semantic_b1_crt_indexed_rebase_selector positions (length full)
          (Comma_CRT_MDD_Leaf (Some index)) =
       Comma_CRT_MDD_Leaf (Some
          (comma_semantic_b1_crt_indexed_rebase_label positions (length full) index))"
      by (simp add: comma_semantic_b1_crt_indexed_rebase_selector_def)
    show "comma_semantic_b1_crt_labelled_zip_witness level full
        (comma_semantic_b1_crt_indexed_rebase_selector positions (length full)
          (Comma_CRT_MDD_Leaf (Some index)))"
      unfolding source_selector
      by (rule comma_semantic_b1_crt_labelled_zip_witness.intros(1)
          [OF target_index_bound one_hot])
  qed
next
  case (labelled_zip_skip level columns selector)
  show ?case
  proof (intro allI impI)
    fix positions full
    assume embed:
      "comma_semantic_b1_crt_indexed_embedding positions columns full"
    have full_admitted:
      "list_all (comma_crt_admitted level) full"
      by (rule comma_semantic_b1_crt_indexed_embedding_admitted
          [OF embed labelled_zip_skip.hyps(2)])
    have full_no_node:
      "\<not> comma_semantic_b1_crt_partition_has_node_at level full"
      using comma_semantic_b1_crt_indexed_embedding_has_node[OF embed]
        labelled_zip_skip.hyps(3) by simp
    have child:
      "comma_semantic_b1_crt_labelled_zip_witness (Suc level) full
        (comma_semantic_b1_crt_indexed_rebase_selector positions (length full) selector)"
      using labelled_zip_skip.IH[rule_format, OF embed] .
    show "comma_semantic_b1_crt_labelled_zip_witness level full
        (comma_semantic_b1_crt_indexed_rebase_selector positions (length full) selector)"
      by (rule comma_semantic_b1_crt_labelled_zip_witness.intros(2)
          [OF labelled_zip_skip.hyps(1) full_admitted full_no_node child])
  qed
next
  case (labelled_zip_node level columns children)
  show ?case
  proof (intro allI impI)
    fix positions full
    assume embed:
      "comma_semantic_b1_crt_indexed_embedding positions columns full"
    have full_admitted:
      "list_all (comma_crt_admitted level) full"
      by (rule comma_semantic_b1_crt_indexed_embedding_admitted
          [OF embed labelled_zip_node.hyps(2)])
    have full_node:
      "comma_semantic_b1_crt_partition_has_node_at level full"
      using comma_semantic_b1_crt_indexed_embedding_has_node[OF embed]
        labelled_zip_node.hyps(3) by simp
    have child_witness:
      "comma_semantic_b1_crt_labelled_zip_witness (Suc level)
        (map (comma_crt_cofactor_or_false level digit) full)
        (comma_semantic_b1_crt_indexed_rebase_selector positions
          (length (map (comma_crt_cofactor_or_false level digit) full))
          (children!digit))"
      if digit: "digit<comma_crt_period level" for digit
    proof -
      have child_embed:
        "comma_semantic_b1_crt_indexed_embedding positions
          (map (comma_crt_cofactor_or_false level digit) columns)
          (map (comma_crt_cofactor_or_false level digit) full)"
        by (rule comma_semantic_b1_crt_indexed_embedding_cofactor[OF embed])
      have ih:
        "\<forall>positions full.
          comma_semantic_b1_crt_indexed_embedding positions
            (map (comma_crt_cofactor_or_false level digit) columns) full \<longrightarrow>
          comma_semantic_b1_crt_labelled_zip_witness (Suc level) full
            (comma_semantic_b1_crt_indexed_rebase_selector positions (length full)
              (children!digit))"
        by (rule labelled_zip_node.IH[OF digit])
      show ?thesis
        by (rule ih[rule_format, OF child_embed])
    qed
    have children_witness:
      "\<And>digit. digit<comma_crt_period level \<Longrightarrow>
        comma_semantic_b1_crt_labelled_zip_witness (Suc level)
          (map (comma_crt_cofactor_or_false level digit) full)
          (comma_semantic_b1_crt_indexed_rebase_selector positions (length full)
            (children!digit))"
      using child_witness by (simp add: length_map)
    have result_witness:
      "comma_semantic_b1_crt_labelled_zip_witness level full
        (comma_crt_mdd_node level
          (map (comma_semantic_b1_crt_indexed_rebase_selector positions (length full))
            children))"
    proof (rule comma_semantic_b1_crt_labelled_zip_witness.intros(3)
        [OF labelled_zip_node.hyps(1) full_admitted full_node])
      show "length (map
          (comma_semantic_b1_crt_indexed_rebase_selector positions (length full)) children) =
        comma_crt_period level"
        using labelled_zip_node.hyps(4) by simp
      fix digit
      assume digit: "digit<comma_crt_period level"
      show "comma_semantic_b1_crt_labelled_zip_witness (Suc level)
          (map (comma_crt_cofactor_or_false level digit) full)
          ((map (comma_semantic_b1_crt_indexed_rebase_selector positions (length full))
            children) ! digit)"
        using children_witness[OF digit]
          labelled_zip_node.hyps(4) digit by (simp add: nth_map)
    qed
    have map_node:
      "comma_semantic_b1_crt_indexed_rebase_selector positions (length full)
          (comma_crt_mdd_node level children) =
       comma_crt_mdd_node level
          (map (comma_semantic_b1_crt_indexed_rebase_selector positions (length full)) children)"
      by (simp add: comma_semantic_b1_crt_indexed_rebase_selector_def[abs_def]
          comma_semantic_b1_crt_mdd_map_payload_node)
    show "comma_semantic_b1_crt_labelled_zip_witness level full
        (comma_semantic_b1_crt_indexed_rebase_selector positions (length full)
          (comma_crt_mdd_node level children))"
      using result_witness map_node by simp
  qed
qed

definition comma_semantic_b1_crt_partition_witness ::
    "nat \<Rightarrow> comma_crt_column list \<Rightarrow> bool" where
  "comma_semantic_b1_crt_partition_witness level columns \<longleftrightarrow>
    (\<exists>selector.
      comma_semantic_b1_crt_labelled_zip_witness level columns selector)"

lemma comma_semantic_b1_crt_partition_witness_terminal:
  assumes index: "index<length columns"
    and code:
      "columns=map (\<lambda>i. Comma_CRT_Bool (i=index)) [0..<length columns]"
  shows "comma_semantic_b1_crt_partition_witness level columns"
  unfolding comma_semantic_b1_crt_partition_witness_def
  by (rule exI[where x="Comma_CRT_MDD_Leaf (Some index)"])
    (rule comma_semantic_b1_crt_labelled_zip_terminal_from_columns
      [OF index code])

lemma comma_semantic_b1_crt_partition_witness_skip:
  assumes level: "level<4"
    and admitted: "list_all (comma_crt_admitted level) columns"
    and no_node:
      "\<not> comma_semantic_b1_crt_partition_has_node_at level columns"
    and child:
      "comma_semantic_b1_crt_partition_witness (Suc level) columns"
  shows "comma_semantic_b1_crt_partition_witness level columns"
proof -
  obtain selector where child_witness:
    "comma_semantic_b1_crt_labelled_zip_witness (Suc level) columns selector"
    using child unfolding comma_semantic_b1_crt_partition_witness_def by blast
  have current:
    "comma_semantic_b1_crt_labelled_zip_witness level columns selector"
    by (rule comma_semantic_b1_crt_labelled_zip_witness.intros(2)
      [OF level admitted no_node child_witness])
  show ?thesis
    unfolding comma_semantic_b1_crt_partition_witness_def
    by (rule exI[where x=selector]; rule current)
qed

lemma comma_semantic_b1_crt_partition_witness_node:
  assumes level: "level<4"
    and admitted: "list_all (comma_crt_admitted level) columns"
    and node: "comma_semantic_b1_crt_partition_has_node_at level columns"
    and children:
      "list_all (\<lambda>digit.
        comma_semantic_b1_crt_partition_witness (Suc level)
          (map (comma_crt_cofactor_or_false level digit) columns))
        [0..<comma_crt_period level]"
  shows "comma_semantic_b1_crt_partition_witness level columns"
proof -
  let ?branches = "\<lambda>digit child.
    comma_semantic_b1_crt_labelled_zip_witness (Suc level)
      (map (comma_crt_cofactor_or_false level digit) columns) child"
  have child_witnesses:
    "list_all (\<lambda>digit. \<exists>child. ?branches digit child)
      [0..<comma_crt_period level]"
    using children by (simp add: comma_semantic_b1_crt_partition_witness_def)
  have choose_children:
    "list_all (\<lambda>digit. \<exists>child. ?branches digit child) digits \<Longrightarrow>
      \<exists>children. list_all2 ?branches digits children" for digits
    by (induction digits) auto
  obtain children where paired: "list_all2 ?branches
      [0..<comma_crt_period level] children"
    using choose_children[OF child_witnesses] by blast
  have node_witness:
    "comma_semantic_b1_crt_labelled_zip_witness level columns
      (comma_crt_mdd_node level children)"
    by (rule comma_semantic_b1_crt_labelled_zip_node_from_pairs
      [OF level admitted node paired])
  show ?thesis
    unfolding comma_semantic_b1_crt_partition_witness_def
    by (rule exI[where x="comma_crt_mdd_node level children"]; rule node_witness)
qed

lemma comma_semantic_b1_crt_partition_witness_lift:
  assumes witness: "comma_semantic_b1_crt_partition_witness level columns"
    and embedding:
      "comma_semantic_b1_crt_indexed_embedding positions columns full"
  shows "comma_semantic_b1_crt_partition_witness level full"
proof -
  obtain selector where selector_witness:
    "comma_semantic_b1_crt_labelled_zip_witness level columns selector"
    using witness unfolding comma_semantic_b1_crt_partition_witness_def by blast
  have lifted:
    "comma_semantic_b1_crt_labelled_zip_witness level full
      (comma_semantic_b1_crt_indexed_rebase_selector positions (length full) selector)"
    using comma_semantic_b1_crt_indexed_labelled_zip_witness_lift
      [OF selector_witness] embedding by blast
  show ?thesis
    unfolding comma_semantic_b1_crt_partition_witness_def
    by (rule exI[where x=
      "comma_semantic_b1_crt_indexed_rebase_selector positions (length full) selector"];
      rule lifted)
qed

lemma comma_semantic_b1_crt_partition_witness_checker_true:
  assumes witness: "comma_semantic_b1_crt_partition_witness level columns"
  shows "comma_semantic_b1_crt_partition_cofactor_checked [level..<4] columns=True"
proof -
  obtain selector where selector_witness:
    "comma_semantic_b1_crt_labelled_zip_witness level columns selector"
    using witness unfolding comma_semantic_b1_crt_partition_witness_def by blast
  show ?thesis
    by (rule comma_semantic_b1_crt_labelled_zip_witness_checker_true
      [OF selector_witness])
qed

ML \<open>
  val checked = @{thms comma_semantic_b1_crt_indexed_nonfalse_from_drop_false
    comma_semantic_b1_crt_indexed_nonfalse_columns_drop_false
    comma_semantic_b1_crt_indexed_nonfalse_embedding
    comma_semantic_b1_crt_indexed_compression_embedding
    comma_semantic_b1_crt_indexed_embedding_cofactor
    comma_semantic_b1_crt_indexed_checker_preserved
    comma_semantic_b1_crt_indexed_child_compact_exact
    comma_semantic_b1_crt_mdd_map_payload_admitted
    comma_semantic_b1_crt_mdd_map_payload_eval
    comma_semantic_b1_crt_indexed_rebase_selector_admitted
    comma_semantic_b1_crt_indexed_rebase_selector_eval
    comma_semantic_b1_crt_indexed_rebase_matches
    comma_semantic_b1_crt_indexed_embedding_admitted
    comma_semantic_b1_crt_indexed_embedding_has_node
    comma_semantic_b1_crt_mdd_map_payload_node
    comma_semantic_b1_crt_indexed_labelled_zip_witness_lift
    comma_semantic_b1_crt_partition_witness_terminal
    comma_semantic_b1_crt_partition_witness_skip
    comma_semantic_b1_crt_partition_witness_node
    comma_semantic_b1_crt_partition_witness_lift
    comma_semantic_b1_crt_partition_witness_checker_true};
  val _ = Thm.consolidate checked;
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Indexed B1 label compression depends on a theorem oracle";
\<close>

end
