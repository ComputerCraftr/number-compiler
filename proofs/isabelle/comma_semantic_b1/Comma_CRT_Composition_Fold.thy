theory Comma_CRT_Composition_Fold
  imports Comma_CRT_Power
begin

text \<open>
Fused, support-aware CRT composition.  This is an alternate executable
composition path: it walks the left and right rows recursively and inserts a
supported intersection into the label-grouped accumulator immediately.  It
does not construct the Cartesian list returned by
@{const comma_crt_compose_raw_rows}.  Stop and Invalid left labels are
absorbing and are inserted directly.  The result label remains occurrence
payload; no minimality or output-label-erasure claim is made here.
\<close>

definition comma_crt_supported_insert ::
    "comma_crt_return_row \<Rightarrow> comma_crt_return_row list \<Rightarrow>
      comma_crt_return_row list" where
  "comma_crt_supported_insert row grouped =
    (if comma_crt_supported (fst row)
     then comma_crt_group_insert row grouped else grouped)"

fun comma_crt_fold_supported_rows ::
    "comma_crt_return_row list \<Rightarrow> comma_crt_return_row list \<Rightarrow>
      comma_crt_return_row list" where
  "comma_crt_fold_supported_rows [] grouped = grouped"
| "comma_crt_fold_supported_rows (row#rows) grouped =
    comma_crt_supported_insert row
      (comma_crt_fold_supported_rows rows grouped)"

fun comma_crt_fold_supported_map ::
    "('a \<Rightarrow> comma_crt_return_row) \<Rightarrow> 'a list \<Rightarrow>
      comma_crt_return_row list \<Rightarrow> comma_crt_return_row list" where
  "comma_crt_fold_supported_map make_row [] grouped = grouped"
| "comma_crt_fold_supported_map make_row (item#items) grouped =
    comma_crt_supported_insert (make_row item)
      (comma_crt_fold_supported_map make_row items grouped)"

definition comma_crt_fused_right_row ::
    "nat \<Rightarrow> comma_crt_return_row \<Rightarrow>
      comma_crt_return_row \<Rightarrow> comma_crt_return_row" where
  "comma_crt_fused_right_row span left right =
    (comma_crt_apply_shifted Comma_CRT_And span (fst left) (fst right),
      comma_semantic_b1_weight_after span (snd right))"

fun comma_crt_fused_rights ::
    "nat \<Rightarrow> comma_crt_return_row \<Rightarrow>
      comma_crt_return_row list \<Rightarrow> comma_crt_return_row list \<Rightarrow>
      comma_crt_return_row list" where
  "comma_crt_fused_rights span left [] grouped = grouped"
| "comma_crt_fused_rights span left (right#rights) grouped =
    comma_crt_supported_insert (comma_crt_fused_right_row span left right)
      (comma_crt_fused_rights span left rights grouped)"

lemma comma_crt_fold_supported_map_spec:
  "comma_crt_fold_supported_map make_row items grouped =
    comma_crt_fold_supported_rows (map make_row items) grouped"
  by (induction items arbitrary: grouped) simp_all

fun comma_crt_fused_left ::
    "nat \<Rightarrow> (nat \<Rightarrow> comma_crt_return_row list) \<Rightarrow>
      comma_crt_return_row \<Rightarrow> comma_crt_return_row list \<Rightarrow>
      comma_crt_return_row list" where
  "comma_crt_fused_left span right_tables left grouped =
    (case snd left of
       Comma_Semantic_B1_Live root \<Rightarrow>
         comma_crt_fused_rights span left (right_tables root) grouped
     | Comma_Semantic_B1_Stop D \<Rightarrow>
         comma_crt_supported_insert left grouped
     | Comma_Semantic_B1_Invalid \<Rightarrow>
         comma_crt_supported_insert left grouped)"

fun comma_crt_fused_left_rows ::
    "nat \<Rightarrow> (nat \<Rightarrow> comma_crt_return_row list) \<Rightarrow>
      comma_crt_return_row list \<Rightarrow> comma_crt_return_row list \<Rightarrow>
      comma_crt_return_row list" where
  "comma_crt_fused_left_rows span right_tables [] grouped = grouped"
| "comma_crt_fused_left_rows span right_tables (left#lefts) grouped =
    comma_crt_fused_left span right_tables left
      (comma_crt_fused_left_rows span right_tables lefts grouped)"

definition comma_crt_fused_power_table ::
    "nat \<Rightarrow> comma_crt_return_row list \<Rightarrow>
      (nat \<Rightarrow> comma_crt_return_row list) \<Rightarrow>
      comma_crt_return_row list" where
  "comma_crt_fused_power_table span left_rows right_tables =
    comma_crt_fused_left_rows span right_tables left_rows []"

lemma comma_crt_supported_insert_admitted:
  assumes row: "comma_crt_admitted 0 (fst row)"
    and grouped: "comma_crt_rows_admitted grouped"
  shows "comma_crt_rows_admitted (comma_crt_supported_insert row grouped)"
proof (cases "comma_crt_supported (fst row)")
  case True
  have inserted: "comma_crt_rows_admitted (comma_crt_group_insert row grouped)"
    by (rule comma_crt_group_insert_admitted[OF row grouped])
  show ?thesis using True inserted
    by (simp add: comma_crt_supported_insert_def)
next
  case False
  then show ?thesis using grouped
    by (simp add: comma_crt_supported_insert_def)
qed

lemma comma_crt_fold_supported_rows_admitted:
  assumes rows: "comma_crt_rows_admitted rows"
    and grouped: "comma_crt_rows_admitted initial"
  shows "comma_crt_rows_admitted
    (comma_crt_fold_supported_rows rows initial)"
  using rows grouped
proof (induction rows arbitrary: initial)
  case Nil
  then show ?case by simp
next
  case (Cons row rows)
  have row_admitted: "comma_crt_admitted 0 (fst row)"
    and tail_admitted: "comma_crt_rows_admitted rows"
    using Cons.prems(1) by (auto simp: comma_crt_rows_admitted_def)
  have inserted:
    "comma_crt_rows_admitted
      (comma_crt_fold_supported_rows rows initial)"
    by (rule Cons.IH[OF tail_admitted Cons.prems(2)])
  show ?case
    unfolding comma_crt_fold_supported_rows.simps
    by (rule comma_crt_supported_insert_admitted[OF row_admitted inserted])
qed

lemma comma_crt_fused_right_row_admitted:
  assumes left: "comma_crt_admitted 0 (fst left)"
    and right: "comma_crt_admitted 0 (fst right)"
  shows "comma_crt_admitted 0 (fst (comma_crt_fused_right_row span left right))"
  using comma_crt_apply_shifted_admitted[OF left right]
  by (simp add: comma_crt_fused_right_row_def)

lemma comma_crt_fused_rights_admitted:
  assumes left: "comma_crt_admitted 0 (fst left)"
    and rights: "comma_crt_rows_admitted rights"
    and grouped: "comma_crt_rows_admitted initial"
  shows "comma_crt_rows_admitted (comma_crt_fused_rights span left rights initial)"
  using left rights grouped
proof (induction rights arbitrary: initial)
  case Nil
  then show ?case by simp
next
  case (Cons right rights)
  have right_admitted: "comma_crt_admitted 0 (fst right)"
    and tail_admitted: "comma_crt_rows_admitted rights"
    using Cons.prems(2) by (auto simp: comma_crt_rows_admitted_def)
  have tail:
    "comma_crt_rows_admitted (comma_crt_fused_rights span left rights initial)"
    by (rule Cons.IH[OF Cons.prems(1) tail_admitted Cons.prems(3)])
  have combined:
    "comma_crt_admitted 0 (fst (comma_crt_fused_right_row span left right))"
    by (rule comma_crt_fused_right_row_admitted[OF Cons.prems(1) right_admitted])
  have step:
    "comma_crt_rows_admitted
      (comma_crt_supported_insert (comma_crt_fused_right_row span left right)
        (comma_crt_fused_rights span left rights initial))"
    by (rule comma_crt_supported_insert_admitted[OF combined tail])
  show ?case using step by (simp add: comma_crt_fused_rights.simps)
qed

lemma comma_crt_fused_left_rows_admitted:
  assumes lefts: "comma_crt_rows_admitted lefts"
    and rights: "\<And>root. comma_crt_rows_admitted (right_tables root)"
    and initial: "comma_crt_rows_admitted grouped"
  shows "comma_crt_rows_admitted
    (comma_crt_fused_left_rows span right_tables lefts grouped)"
  using lefts initial
proof (induction lefts arbitrary: grouped)
  case Nil
  then show ?case by simp
next
  case (Cons left lefts)
  have left_admitted: "comma_crt_admitted 0 (fst left)"
    and tail_admitted: "comma_crt_rows_admitted lefts"
    using Cons.prems(1) by (auto simp: comma_crt_rows_admitted_def)
  have tail:
    "comma_crt_rows_admitted
      (comma_crt_fused_left_rows span right_tables lefts grouped)"
    by (rule Cons.IH[OF tail_admitted Cons.prems(2)])
  have step:
    "comma_crt_rows_admitted
      (comma_crt_fused_left span right_tables left
        (comma_crt_fused_left_rows span right_tables lefts grouped))"
  proof (cases "snd left")
    case (Comma_Semantic_B1_Live root)
    have live:
      "comma_crt_rows_admitted
        (comma_crt_fused_rights span left (right_tables root)
          (comma_crt_fused_left_rows span right_tables lefts grouped))"
      by (rule comma_crt_fused_rights_admitted[OF left_admitted rights[of root] tail])
    show ?thesis using Comma_Semantic_B1_Live live
      by (simp add: comma_crt_fused_left.simps)
  next
    case (Comma_Semantic_B1_Stop D)
    have stopped:
      "comma_crt_rows_admitted
        (comma_crt_supported_insert left
          (comma_crt_fused_left_rows span right_tables lefts grouped))"
      by (rule comma_crt_supported_insert_admitted[OF left_admitted tail])
    show ?thesis using Comma_Semantic_B1_Stop stopped
      by (simp add: comma_crt_fused_left.simps)
  next
    case Comma_Semantic_B1_Invalid
    have invalid:
      "comma_crt_rows_admitted
        (comma_crt_supported_insert left
          (comma_crt_fused_left_rows span right_tables lefts grouped))"
      by (rule comma_crt_supported_insert_admitted[OF left_admitted tail])
    show ?thesis using Comma_Semantic_B1_Invalid invalid
      by (simp add: comma_crt_fused_left.simps)
  qed
  show ?case using step by (simp add: comma_crt_fused_left_rows.simps)
qed

theorem comma_crt_fused_power_table_admitted:
  assumes left: "comma_crt_rows_admitted left_rows"
    and right: "\<And>root. comma_crt_rows_admitted (right_tables root)"
  shows "comma_crt_rows_admitted
    (comma_crt_fused_power_table span left_rows right_tables)"
proof -
  have empty: "comma_crt_rows_admitted ([] :: comma_crt_return_row list)"
    by (simp add: comma_crt_rows_admitted_def)
  show ?thesis
    unfolding comma_crt_fused_power_table_def
    by (rule comma_crt_fused_left_rows_admitted[OF left right empty])
qed

lemma comma_crt_group_insert_supported:
  assumes row_admitted: "comma_crt_admitted 0 (fst row)"
    and grouped_admitted: "comma_crt_rows_admitted grouped"
    and row_supported: "comma_crt_supported (fst row)"
    and grouped_supported:
      "\<forall>entry\<in>set grouped. comma_crt_supported (fst entry)"
  shows "\<forall>entry\<in>set (comma_crt_group_insert row grouped).
      comma_crt_supported (fst entry)"
  using row_admitted grouped_admitted row_supported grouped_supported
proof (induction grouped)
  case Nil
  then show ?case by (simp add: comma_crt_group_insert.simps)
next
  case (Cons head tail)
  have head_admitted: "comma_crt_admitted 0 (fst head)"
    and tail_admitted: "comma_crt_rows_admitted tail"
    using Cons.prems(2) by (auto simp: comma_crt_rows_admitted_def)
  have head_supported: "comma_crt_supported (fst head)"
    using Cons.prems(4) by simp
  have tail_supported:
    "\<forall>entry\<in>set tail. comma_crt_supported (fst entry)"
    using Cons.prems(4) by simp
  show ?case
  proof (cases "snd row=snd head")
    case True
    have merged_admitted:
      "comma_crt_admitted 0
        (comma_crt_apply Comma_CRT_Or (fst head) (fst row))"
      by (rule comma_crt_apply_admitted[OF head_admitted Cons.prems(1)])
    have head_nonempty: "comma_crt_set (fst head)\<noteq>{}"
      using comma_crt_supported_nonempty[OF head_admitted] head_supported by blast
    have merged_set:
      "comma_crt_set (comma_crt_apply Comma_CRT_Or (fst head) (fst row)) =
        comma_crt_set (fst head) \<union> comma_crt_set (fst row)"
      by (rule comma_crt_apply_or_set[OF head_admitted Cons.prems(1)])
    have merged_nonempty:
      "comma_crt_set (comma_crt_apply Comma_CRT_Or (fst head) (fst row))\<noteq>{}"
      using merged_set head_nonempty by auto
    have merged_supported:
      "comma_crt_supported
        (comma_crt_apply Comma_CRT_Or (fst head) (fst row))"
      using comma_crt_supported_nonempty[OF merged_admitted] merged_nonempty by blast
    show ?thesis using True merged_supported tail_supported
      by (simp add: comma_crt_group_insert.simps)
  next
    case False
    have tail_result:
      "\<forall>entry\<in>set (comma_crt_group_insert row tail).
        comma_crt_supported (fst entry)"
      by (rule Cons.IH[OF Cons.prems(1) tail_admitted
          Cons.prems(3) tail_supported])
    show ?thesis using False head_supported tail_result
      by (simp add: comma_crt_group_insert.simps)
  qed
qed

lemma comma_crt_supported_insert_preserves_support:
  assumes row_admitted: "comma_crt_admitted 0 (fst row)"
    and grouped_admitted: "comma_crt_rows_admitted grouped"
    and grouped_supported:
      "\<forall>entry\<in>set grouped. comma_crt_supported (fst entry)"
  shows "\<forall>entry\<in>set (comma_crt_supported_insert row grouped).
      comma_crt_supported (fst entry)"
proof (cases "comma_crt_supported (fst row)")
  case True
  have inserted:
    "\<forall>entry\<in>set (comma_crt_group_insert row grouped).
      comma_crt_supported (fst entry)"
    by (rule comma_crt_group_insert_supported[OF row_admitted
      grouped_admitted True grouped_supported])
  show ?thesis using True inserted
    by (simp add: comma_crt_supported_insert_def)
next
  case False
  then show ?thesis using grouped_supported
    by (simp add: comma_crt_supported_insert_def)
qed

lemma comma_crt_fold_supported_rows_supported:
  assumes rows: "comma_crt_rows_admitted rows"
    and grouped: "comma_crt_rows_admitted initial"
    and supported: "\<forall>entry\<in>set initial. comma_crt_supported (fst entry)"
  shows "\<forall>entry\<in>set (comma_crt_fold_supported_rows rows initial).
      comma_crt_supported (fst entry)"
  using rows grouped supported
proof (induction rows arbitrary: initial)
  case Nil
  then show ?case by simp
next
  case (Cons row rows)
  have row_admitted: "comma_crt_admitted 0 (fst row)"
    and tail_admitted: "comma_crt_rows_admitted rows"
    using Cons.prems(1) by (auto simp: comma_crt_rows_admitted_def)
  have tail_admitted_result:
    "comma_crt_rows_admitted (comma_crt_fold_supported_rows rows initial)"
    by (rule comma_crt_fold_supported_rows_admitted[OF tail_admitted Cons.prems(2)])
  have tail_supported:
    "\<forall>entry\<in>set (comma_crt_fold_supported_rows rows initial).
      comma_crt_supported (fst entry)"
    by (rule Cons.IH[OF tail_admitted Cons.prems(2) Cons.prems(3)])
  show ?case unfolding comma_crt_fold_supported_rows.simps
    by (rule comma_crt_supported_insert_preserves_support
      [OF row_admitted tail_admitted_result tail_supported])
qed

lemma comma_crt_fused_rights_supported:
  assumes left: "comma_crt_admitted 0 (fst left)"
    and rights: "comma_crt_rows_admitted rights"
    and grouped: "comma_crt_rows_admitted initial"
    and supported: "\<forall>entry\<in>set initial. comma_crt_supported (fst entry)"
  shows "\<forall>entry\<in>set (comma_crt_fused_rights span left rights initial).
      comma_crt_supported (fst entry)"
  using left rights grouped supported
proof (induction rights arbitrary: initial)
  case Nil
  then show ?case by simp
next
  case (Cons right rights)
  have right_admitted: "comma_crt_admitted 0 (fst right)"
    and tail_admitted: "comma_crt_rows_admitted rights"
    using Cons.prems(2) by (auto simp: comma_crt_rows_admitted_def)
  have tail:
    "\<forall>entry\<in>set (comma_crt_fused_rights span left rights initial).
      comma_crt_supported (fst entry)"
    by (rule Cons.IH[OF Cons.prems(1) tail_admitted Cons.prems(3) Cons.prems(4)])
  have tail_admitted_result:
    "comma_crt_rows_admitted (comma_crt_fused_rights span left rights initial)"
    by (rule comma_crt_fused_rights_admitted
      [OF Cons.prems(1) tail_admitted Cons.prems(3)])
  have combined_admitted:
    "comma_crt_admitted 0 (fst (comma_crt_fused_right_row span left right))"
    by (rule comma_crt_fused_right_row_admitted[OF Cons.prems(1) right_admitted])
  show ?case unfolding comma_crt_fused_rights.simps
    by (rule comma_crt_supported_insert_preserves_support
      [OF combined_admitted tail_admitted_result tail])
qed

lemma comma_crt_fused_left_rows_supported:
  assumes lefts: "comma_crt_rows_admitted lefts"
    and rights: "\<And>root. comma_crt_rows_admitted (right_tables root)"
    and initial: "comma_crt_rows_admitted grouped"
    and supported: "\<forall>entry\<in>set grouped. comma_crt_supported (fst entry)"
  shows "\<forall>entry\<in>set (comma_crt_fused_left_rows span right_tables lefts grouped).
      comma_crt_supported (fst entry)"
  using lefts initial supported
proof (induction lefts arbitrary: grouped)
  case Nil
  then show ?case by simp
next
  case (Cons left lefts)
  have left_admitted: "comma_crt_admitted 0 (fst left)"
    and tail_admitted: "comma_crt_rows_admitted lefts"
    using Cons.prems(1) by (auto simp: comma_crt_rows_admitted_def)
  have tail:
    "\<forall>entry\<in>set (comma_crt_fused_left_rows span right_tables lefts grouped).
      comma_crt_supported (fst entry)"
    by (rule Cons.IH[OF tail_admitted Cons.prems(2) Cons.prems(3)])
  have tail_admitted_result:
    "comma_crt_rows_admitted (comma_crt_fused_left_rows span right_tables lefts grouped)"
    by (rule comma_crt_fused_left_rows_admitted
      [OF tail_admitted rights Cons.prems(2)])
  show ?case
  proof (cases "snd left")
    case (Comma_Semantic_B1_Live root)
    have live:
      "\<forall>entry\<in>set (comma_crt_fused_rights span left (right_tables root)
        (comma_crt_fused_left_rows span right_tables lefts grouped)).
        comma_crt_supported (fst entry)"
      by (rule comma_crt_fused_rights_supported[OF left_admitted
        rights[of root] tail_admitted_result tail])
    show ?thesis using Comma_Semantic_B1_Live live
      by (simp add: comma_crt_fused_left.simps)
  next
    case (Comma_Semantic_B1_Stop D)
    have stopped:
      "\<forall>entry\<in>set (comma_crt_supported_insert left
        (comma_crt_fused_left_rows span right_tables lefts grouped)).
        comma_crt_supported (fst entry)"
      by (rule comma_crt_supported_insert_preserves_support
        [OF left_admitted tail_admitted_result tail])
    show ?thesis using Comma_Semantic_B1_Stop stopped
      by (simp add: comma_crt_fused_left.simps)
  next
    case Comma_Semantic_B1_Invalid
    have invalid:
      "\<forall>entry\<in>set (comma_crt_supported_insert left
        (comma_crt_fused_left_rows span right_tables lefts grouped)).
        comma_crt_supported (fst entry)"
      by (rule comma_crt_supported_insert_preserves_support
        [OF left_admitted tail_admitted_result tail])
    show ?thesis using Comma_Semantic_B1_Invalid invalid
      by (simp add: comma_crt_fused_left.simps)
  qed
qed

theorem comma_crt_fused_power_table_supported:
  assumes left: "comma_crt_rows_admitted left_rows"
    and right: "\<And>root. comma_crt_rows_admitted (right_tables root)"
  shows "\<forall>row\<in>set (comma_crt_fused_power_table span left_rows right_tables).
      comma_crt_supported (fst row)"
proof -
  have empty_admitted:
    "comma_crt_rows_admitted ([] :: comma_crt_return_row list)"
    by (simp add: comma_crt_rows_admitted_def)
  have empty_supported:
    "\<forall>row\<in>set ([] :: comma_crt_return_row list).
      comma_crt_supported (fst row)" by simp
  show ?thesis unfolding comma_crt_fused_power_table_def
    by (rule comma_crt_fused_left_rows_supported
      [OF left right empty_admitted empty_supported])
qed

lemma comma_crt_supported_insert_labels_distinct:
  assumes "distinct (map snd grouped)"
  shows "distinct (map snd (comma_crt_supported_insert row grouped))"
  using assms
  by (cases "comma_crt_supported (fst row)";
      simp add: comma_crt_supported_insert_def
        comma_crt_group_insert_labels_distinct)

lemma comma_crt_fused_rights_labels_distinct:
  assumes "distinct (map snd initial)"
  shows "distinct (map snd (comma_crt_fused_rights span left rights initial))"
  using assms
proof (induction rights arbitrary: initial)
  case Nil
  then show ?case by simp
next
  case (Cons right rights)
  have tail:
    "distinct (map snd (comma_crt_fused_rights span left rights initial))"
    by (rule Cons.IH[OF Cons.prems])
  show ?case unfolding comma_crt_fused_rights.simps
    by (rule comma_crt_supported_insert_labels_distinct[OF tail])
qed

lemma comma_crt_fused_left_rows_labels_distinct:
  assumes "distinct (map snd grouped)"
  shows "distinct (map snd
    (comma_crt_fused_left_rows span right_tables lefts grouped))"
  using assms
proof (induction lefts arbitrary: grouped)
  case Nil
  then show ?case by simp
next
  case (Cons left lefts)
  have tail:
    "distinct (map snd
      (comma_crt_fused_left_rows span right_tables lefts grouped))"
    by (rule Cons.IH[OF Cons.prems])
  show ?case
  proof (cases "snd left")
    case (Comma_Semantic_B1_Live root)
    have live:
      "distinct (map snd (comma_crt_fused_rights span left (right_tables root)
        (comma_crt_fused_left_rows span right_tables lefts grouped)))"
      by (rule comma_crt_fused_rights_labels_distinct[OF tail])
    show ?thesis using Comma_Semantic_B1_Live live
      by (simp add: comma_crt_fused_left.simps)
  next
    case (Comma_Semantic_B1_Stop D)
    show ?thesis using Comma_Semantic_B1_Stop tail
      by (simp add: comma_crt_fused_left.simps
          comma_crt_supported_insert_labels_distinct)
  next
    case Comma_Semantic_B1_Invalid
    show ?thesis using Comma_Semantic_B1_Invalid tail
      by (simp add: comma_crt_fused_left.simps
          comma_crt_supported_insert_labels_distinct)
  qed
qed

theorem comma_crt_fused_power_table_labels_distinct:
  "distinct (map snd
    (comma_crt_fused_power_table span left_rows right_tables))"
proof -
  have empty: "distinct (map snd ([] :: comma_crt_return_row list))"
    by simp
  show ?thesis unfolding comma_crt_fused_power_table_def
    by (rule comma_crt_fused_left_rows_labels_distinct[OF empty])
qed

theorem comma_crt_power_table_admitted:
  assumes left: "comma_crt_rows_admitted left_rows"
    and right: "\<And>root. comma_crt_rows_admitted (right_tables root)"
  shows "comma_crt_rows_admitted
    (comma_crt_power_table span left_rows right_tables)"
proof -
  have raw: "comma_crt_rows_admitted
      (comma_crt_compose_raw_rows span left_rows right_tables)"
    by (rule comma_crt_compose_raw_rows_admitted[OF left right])
  have grouped: "comma_crt_rows_admitted
      (comma_crt_group_rows
        (comma_crt_compose_raw_rows span left_rows right_tables))"
    by (rule comma_crt_group_rows_admitted[OF raw])
  have filtered:
    "comma_crt_rows_admitted
      (filter (\<lambda>row. comma_crt_supported (fst row))
        (comma_crt_group_rows
          (comma_crt_compose_raw_rows span left_rows right_tables)))"
  proof (unfold comma_crt_rows_admitted_def, intro ballI)
    fix row
    assume row: "row \<in> set (filter (\<lambda>row. comma_crt_supported (fst row))
      (comma_crt_group_rows
        (comma_crt_compose_raw_rows span left_rows right_tables)))"
    have in_group:
      "row \<in> set (comma_crt_group_rows
        (comma_crt_compose_raw_rows span left_rows right_tables))"
      using row by (auto simp: set_filter)
    show "comma_crt_admitted 0 (fst row)"
      using grouped in_group by (auto simp: comma_crt_rows_admitted_def)
  qed
  show ?thesis
    using filtered by (simp only: comma_crt_power_table_def)
qed

lemma comma_crt_fold_supported_rows_append:
  "comma_crt_fold_supported_rows (lefts@rights) grouped =
    comma_crt_fold_supported_rows lefts
      (comma_crt_fold_supported_rows rights grouped)"
  by (induction lefts arbitrary: grouped) simp_all

lemma comma_crt_fused_rights_fold_spec:
  "comma_crt_fused_rights span left rights grouped =
    comma_crt_fold_supported_rows
      (map (comma_crt_fused_right_row span left) rights) grouped"
  by (induction rights arbitrary: grouped) simp_all

lemma comma_crt_fused_left_fold_spec:
  "comma_crt_fused_left span right_tables left grouped =
    comma_crt_fold_supported_rows
      (comma_crt_compose_left_row span right_tables left) grouped"
proof (cases "snd left")
  case (Comma_Semantic_B1_Live root)
  have maps:
    "map (comma_crt_fused_right_row span left) (right_tables root) =
      map (\<lambda>right.
        (comma_crt_apply_shifted Comma_CRT_And span (fst left) (fst right),
          comma_semantic_b1_weight_after span (snd right))) (right_tables root)"
    by (rule map_cong) (simp_all add: comma_crt_fused_right_row_def)
  have fused:
    "comma_crt_fused_rights span left (right_tables root) grouped =
      comma_crt_fold_supported_rows
        (map (comma_crt_fused_right_row span left) (right_tables root)) grouped"
    by (rule comma_crt_fused_rights_fold_spec)
  have fused_left:
    "comma_crt_fused_left span right_tables left grouped =
      comma_crt_fused_rights span left (right_tables root) grouped"
    using Comma_Semantic_B1_Live by (simp add: comma_crt_fused_left.simps)
  have compose_left:
    "comma_crt_compose_left_row span right_tables left =
      map (\<lambda>right.
        (comma_crt_apply_shifted Comma_CRT_And span (fst left) (fst right),
          comma_semantic_b1_weight_after span (snd right))) (right_tables root)"
    using Comma_Semantic_B1_Live
    by (simp add: comma_crt_compose_left_row_def)
  show ?thesis using fused_left fused maps compose_left by simp
next
  case (Comma_Semantic_B1_Stop D)
  have fused_left:
    "comma_crt_fused_left span right_tables left grouped =
      comma_crt_supported_insert left grouped"
    using Comma_Semantic_B1_Stop by (simp add: comma_crt_fused_left.simps)
  have compose_left:
    "comma_crt_compose_left_row span right_tables left = [left]"
    using Comma_Semantic_B1_Stop by (simp add: comma_crt_compose_left_row_def)
  show ?thesis using fused_left compose_left
    by (simp add: comma_crt_fold_supported_rows.simps)
next
  case Comma_Semantic_B1_Invalid
  have fused_left:
    "comma_crt_fused_left span right_tables left grouped =
      comma_crt_supported_insert left grouped"
    using Comma_Semantic_B1_Invalid by (simp add: comma_crt_fused_left.simps)
  have compose_left:
    "comma_crt_compose_left_row span right_tables left = [left]"
    using Comma_Semantic_B1_Invalid by (simp add: comma_crt_compose_left_row_def)
  show ?thesis using fused_left compose_left
    by (simp add: comma_crt_fold_supported_rows.simps)
qed

lemma comma_crt_fused_left_rows_fold_spec:
  "comma_crt_fused_left_rows span right_tables lefts grouped =
    comma_crt_fold_supported_rows
      (comma_crt_compose_raw_rows span lefts right_tables) grouped"
  unfolding comma_crt_compose_raw_rows_def
proof (induction lefts arbitrary: grouped)
  case Nil
  then show ?case by simp
next
  case (Cons left lefts)
  show ?case
    by (simp only: list.map concat.simps
      comma_crt_fused_left_rows.simps comma_crt_fused_left_fold_spec
      comma_crt_fold_supported_rows_append Cons.IH)
qed

lemma comma_crt_fused_power_table_fold_spec:
  "comma_crt_fused_power_table span left_rows right_tables =
    comma_crt_fold_supported_rows
      (comma_crt_compose_raw_rows span left_rows right_tables) []"
  by (simp add: comma_crt_fused_power_table_def
      comma_crt_fused_left_rows_fold_spec)

lemma comma_crt_fold_supported_rows_column_set:
  assumes rows: "comma_crt_rows_admitted rows"
  shows "comma_crt_set
      (comma_crt_group_column outcome (comma_crt_fold_supported_rows rows [])) =
    comma_crt_set (comma_crt_collect_output outcome rows)"
  using rows
proof (induction rows)
  case Nil
  then show ?case by (simp add: comma_crt_set_def)
next
  case (Cons row rows)
  have row_admitted: "comma_crt_admitted 0 (fst row)"
    and tail_admitted: "comma_crt_rows_admitted rows"
    using Cons.prems by (auto simp: comma_crt_rows_admitted_def)
  have tail_grouped:
    "comma_crt_rows_admitted (comma_crt_fold_supported_rows rows [])"
    by (rule comma_crt_fold_supported_rows_admitted[OF tail_admitted])
      (simp add: comma_crt_rows_admitted_def)
  have collected_admitted:
    "comma_crt_admitted 0 (comma_crt_collect_output outcome rows)"
    by (rule comma_crt_collect_output_admitted[OF tail_admitted])
  have union:
    "comma_crt_set (comma_crt_apply Comma_CRT_Or (fst row)
        (comma_crt_collect_output outcome rows)) =
      comma_crt_set (fst row) \<union>
        comma_crt_set (comma_crt_collect_output outcome rows)"
    by (rule comma_crt_apply_or_set[OF row_admitted collected_admitted])
  show ?case
  proof (cases "comma_crt_supported (fst row)")
    case True
    have inserted:
      "comma_crt_set (comma_crt_group_column outcome
        (comma_crt_group_insert row (comma_crt_fold_supported_rows rows []))) =
       (if snd row=outcome then
          comma_crt_set (comma_crt_group_column outcome
            (comma_crt_fold_supported_rows rows [])) \<union>
          comma_crt_set (fst row)
        else comma_crt_set (comma_crt_group_column outcome
          (comma_crt_fold_supported_rows rows [])))"
      by (rule comma_crt_group_column_insert_set[OF row_admitted tail_grouped])
    show ?thesis
      using inserted Cons.IH[OF tail_admitted] True union
      by (simp add: comma_crt_fold_supported_rows.simps
          comma_crt_supported_insert_def comma_crt_collect_output.simps
          Un_commute)
  next
    case False
    have empty: "comma_crt_set (fst row)={}"
      using comma_crt_supported_nonempty[OF row_admitted] False by blast
    show ?thesis
      using Cons.IH[OF tail_admitted] empty False union
      by (simp add: comma_crt_fold_supported_rows.simps
          comma_crt_supported_insert_def comma_crt_collect_output.simps
          Un_commute)
  qed
qed

lemma comma_crt_fold_supported_map_output_set:
  assumes admitted:
    "comma_crt_rows_admitted (map make_row items)"
  shows "comma_crt_set (comma_crt_group_column outcome
      (comma_crt_fold_supported_map make_row items [])) =
    comma_crt_set (comma_crt_collect_output outcome (map make_row items))"
proof -
  have rows_set:
    "comma_crt_set (comma_crt_group_column outcome
      (comma_crt_fold_supported_rows (map make_row items) [])) =
     comma_crt_set (comma_crt_collect_output outcome (map make_row items))"
    by (rule comma_crt_fold_supported_rows_column_set[OF admitted])
  show ?thesis
    using rows_set comma_crt_fold_supported_map_spec[of make_row items "[]"] by simp
qed

lemma comma_crt_group_column_filter_supported_set:
  assumes admitted: "comma_crt_rows_admitted rows"
    and labels: "distinct (map snd rows)"
  shows "comma_crt_set (comma_crt_group_column outcome
      (filter (\<lambda>row. comma_crt_supported (fst row)) rows)) =
    comma_crt_set (comma_crt_group_column outcome rows)"
  using admitted labels
proof (induction rows)
  case Nil
  then show ?case by simp
next
  case (Cons row rows)
  have row_admitted: "comma_crt_admitted 0 (fst row)"
    and tail_admitted: "comma_crt_rows_admitted rows"
    using Cons.prems(1) by (auto simp: comma_crt_rows_admitted_def)
  have tail_labels: "distinct (map snd rows)"
    using Cons.prems(2) by simp
  have head_absent: "snd row\<notin>set (map snd rows)"
    using Cons.prems(2) by simp
  show ?case
  proof (cases "snd row=outcome")
    case True
    have label_eq: "snd row=outcome" by fact
    show ?thesis
    proof (cases "comma_crt_supported (fst row)")
      case True
      then show ?thesis
        using label_eq head_absent
        by (simp add: comma_crt_group_column.simps filter.simps)
    next
      case False
      have empty: "comma_crt_set (fst row)={}"
        using comma_crt_supported_nonempty[OF row_admitted] False by blast
      have no_tail_label: "outcome\<notin>set (map snd rows)"
        using label_eq head_absent by simp
      have tail_empty:
        "comma_crt_set (comma_crt_group_column outcome rows)={}"
      proof (rule ccontr)
        assume nonempty: "comma_crt_set
            (comma_crt_group_column outcome rows)\<noteq>{}"
        obtain witness where witness: "witness\<in>set rows"
          "snd witness=outcome"
          using comma_crt_group_column_nonempty_member[OF nonempty] by blast
        show False using no_tail_label witness by auto
      qed
      show ?thesis using empty label_eq False
          tail_empty Cons.IH[OF tail_admitted tail_labels]
        by (simp add: comma_crt_group_column.simps filter.simps)
    qed
  next
    case False
    have tail_eq:
      "comma_crt_set (comma_crt_group_column outcome
          (filter (\<lambda>row. comma_crt_supported (fst row)) rows)) =
        comma_crt_set (comma_crt_group_column outcome rows)"
      by (rule Cons.IH[OF tail_admitted tail_labels])
    show ?thesis using False tail_eq
      by (simp add: comma_crt_group_column.simps filter.simps)
  qed
qed

theorem comma_crt_fused_power_table_outcome_set:
  assumes left: "comma_crt_rows_admitted left_rows"
    and right: "\<And>root. comma_crt_rows_admitted (right_tables root)"
  shows "comma_crt_set (comma_crt_group_column outcome
      (comma_crt_fused_power_table span left_rows right_tables)) =
    comma_crt_set (comma_crt_group_column outcome
      (comma_crt_power_table span left_rows right_tables))"
proof -
  let ?raw = "comma_crt_compose_raw_rows span left_rows right_tables"
  have raw_admitted: "comma_crt_rows_admitted ?raw"
    by (rule comma_crt_compose_raw_rows_admitted[OF left right])
  have grouped_admitted: "comma_crt_rows_admitted (comma_crt_group_rows ?raw)"
    by (rule comma_crt_group_rows_admitted[OF raw_admitted])
  have grouped_labels:
    "distinct (map snd (comma_crt_group_rows ?raw))"
    by (rule comma_crt_group_rows_labels_distinct)
  have fused_set:
    "comma_crt_set (comma_crt_group_column outcome
      (comma_crt_fused_power_table span left_rows right_tables)) =
      comma_crt_set (comma_crt_collect_output outcome ?raw)"
    using comma_crt_fused_power_table_fold_spec raw_admitted
      comma_crt_fold_supported_rows_column_set[of ?raw outcome]
    by simp
  have old_filter:
    "comma_crt_set (comma_crt_group_column outcome
      (comma_crt_power_table span left_rows right_tables)) =
      comma_crt_set (comma_crt_group_column outcome (comma_crt_group_rows ?raw))"
    unfolding comma_crt_power_table_def
    by (rule comma_crt_group_column_filter_supported_set
      [OF grouped_admitted grouped_labels])
  have grouped_collect:
    "comma_crt_set (comma_crt_group_column outcome (comma_crt_group_rows ?raw)) =
      comma_crt_set (comma_crt_collect_output outcome ?raw)"
    by (rule comma_crt_group_rows_column_set[OF raw_admitted])
  show ?thesis using fused_set old_filter grouped_collect by simp
qed

end
