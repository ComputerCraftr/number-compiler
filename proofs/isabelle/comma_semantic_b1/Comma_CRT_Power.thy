theory Comma_CRT_Power
  imports Comma_CRT_Support
begin

text \<open>
Executable composition of completed CRT return columns.  Stop and Invalid
rows do not inspect the right action.  Live rows combine matching columns
with fused shifted apply; no translated right tree is constructed first.
The set projection below is a refinement statement, not an executable step.
\<close>

type_synonym comma_crt_return_row =
  "comma_crt_column \<times> comma_semantic_b1_result"

definition comma_crt_project_row ::
    "comma_crt_return_row \<Rightarrow> comma_semantic_b1_binding_row" where
  "comma_crt_project_row row = (comma_crt_set (fst row), snd row)"

definition comma_crt_rows_admitted :: "comma_crt_return_row list \<Rightarrow> bool" where
  "comma_crt_rows_admitted rows \<longleftrightarrow>
    (\<forall>row\<in>set rows. comma_crt_admitted 0 (fst row))"


definition comma_crt_compose_left_row ::
    "nat \<Rightarrow> (nat \<Rightarrow> comma_crt_return_row list) \<Rightarrow>
      comma_crt_return_row \<Rightarrow> comma_crt_return_row list" where
  "comma_crt_compose_left_row span right_tables left =
    (case snd left of
       Comma_Semantic_B1_Live root \<Rightarrow>
         map (\<lambda>right.
           (comma_crt_apply_shifted Comma_CRT_And span (fst left) (fst right),
            comma_semantic_b1_weight_after span (snd right))) (right_tables root)
     | result \<Rightarrow> [left])"

definition comma_crt_compose_raw_rows ::
    "nat \<Rightarrow> comma_crt_return_row list \<Rightarrow>
      (nat \<Rightarrow> comma_crt_return_row list) \<Rightarrow>
      comma_crt_return_row list" where
  "comma_crt_compose_raw_rows span left_rows right_tables =
    concat (map (comma_crt_compose_left_row span right_tables) left_rows)"

lemma comma_crt_compose_left_row_projects:
  assumes left: "comma_crt_admitted 0 (fst row)"
    and right: "\<And>root. comma_crt_rows_admitted (right_tables root)"
  shows "map comma_crt_project_row (comma_crt_compose_left_row span right_tables row) =
    comma_semantic_b1_compose_left_row span
      (\<lambda>root. map comma_crt_project_row (right_tables root))
      (comma_crt_project_row row)"
proof (cases "snd row")
  case (Comma_Semantic_B1_Live root)
  have cell: "\<And>entry. entry\<in>set (right_tables root) \<Longrightarrow>
      comma_crt_set
        (comma_crt_apply_shifted Comma_CRT_And span (fst row) (fst entry)) =
      comma_crt_set (fst row) \<inter>
        comma_semantic_b1_column_advance span (comma_crt_set (fst entry))"
  proof -
    fix entry
    assume entry: "entry\<in>set (right_tables root)"
    have entry_admitted: "comma_crt_admitted 0 (fst entry)"
      using right[of root] entry by (auto simp: comma_crt_rows_admitted_def)
    show "comma_crt_set
        (comma_crt_apply_shifted Comma_CRT_And span (fst row) (fst entry)) =
      comma_crt_set (fst row) \<inter>
        comma_semantic_b1_column_advance span (comma_crt_set (fst entry))"
      by (rule comma_crt_fused_power_intersection_refines[OF left entry_admitted])
  qed
  show ?thesis
    using Comma_Semantic_B1_Live cell
    by (simp add: comma_crt_compose_left_row_def comma_crt_project_row_def
        comma_semantic_b1_compose_left_row_def map_map cong: map_cong)
qed (simp_all add: comma_crt_compose_left_row_def comma_crt_project_row_def
    comma_semantic_b1_compose_left_row_def)

lemma comma_crt_compose_raw_rows_projects:
  assumes left: "comma_crt_rows_admitted left_rows"
    and right: "\<And>root. comma_crt_rows_admitted (right_tables root)"
  shows "map comma_crt_project_row
      (comma_crt_compose_raw_rows span left_rows right_tables) =
    comma_semantic_b1_compose_raw_rows span (map comma_crt_project_row left_rows)
      (\<lambda>root. map comma_crt_project_row (right_tables root))"
  using comma_crt_compose_left_row_projects right left
  by (simp add: comma_crt_compose_raw_rows_def
      comma_semantic_b1_compose_raw_rows_def comma_crt_rows_admitted_def
      map_concat map_map cong: map_cong)

lemma comma_crt_compose_raw_rows_admitted:
  assumes left: "comma_crt_rows_admitted left_rows"
    and right: "\<And>root. comma_crt_rows_admitted (right_tables root)"
  shows "comma_crt_rows_admitted (comma_crt_compose_raw_rows span left_rows right_tables)"
  using left right
  by (auto simp: comma_crt_rows_admitted_def comma_crt_compose_raw_rows_def
      comma_crt_compose_left_row_def split: comma_semantic_b1_result.splits
      intro: comma_crt_apply_shifted_admitted)

fun comma_crt_collect_output ::
    "comma_semantic_b1_result \<Rightarrow> comma_crt_return_row list \<Rightarrow>
      comma_crt_column" where
  "comma_crt_collect_output outcome [] = Comma_CRT_Bool False"
| "comma_crt_collect_output outcome (row#rows) =
    (if snd row=outcome then
      comma_crt_apply Comma_CRT_Or (fst row) (comma_crt_collect_output outcome rows)
     else comma_crt_collect_output outcome rows)"

lemma comma_crt_collect_output_admitted:
  assumes "comma_crt_rows_admitted rows"
  shows "comma_crt_admitted 0 (comma_crt_collect_output outcome rows)"
  using assms
  by (induction rows) (auto simp: comma_crt_rows_admitted_def
      intro: comma_crt_apply_admitted)

lemma comma_crt_collect_output_set:
  assumes "comma_crt_rows_admitted rows"
  shows "comma_crt_set (comma_crt_collect_output outcome rows) =
    (\<Union>row\<in>{row\<in>set rows. snd row=outcome}. comma_crt_set (fst row))"
  using assms
proof (induction rows)
  case Nil
  then show ?case by (simp add: comma_crt_set_def)
next
  case (Cons row rows)
  have row: "comma_crt_admitted 0 (fst row)"
    and rows: "comma_crt_rows_admitted rows"
    using Cons.prems by (auto simp: comma_crt_rows_admitted_def)
  have tail: "comma_crt_admitted 0 (comma_crt_collect_output outcome rows)"
    by (rule comma_crt_collect_output_admitted[OF rows])
  show ?case using Cons.IH[OF rows] comma_crt_apply_or_set[OF row tail]
    by (auto split: if_splits)
qed

fun comma_crt_group_insert ::
    "comma_crt_return_row \<Rightarrow> comma_crt_return_row list \<Rightarrow>
      comma_crt_return_row list" where
  "comma_crt_group_insert row [] = [row]"
| "comma_crt_group_insert row (head#tail) =
    (if snd row=snd head then
       (comma_crt_apply Comma_CRT_Or (fst head) (fst row),snd head)#tail
     else head#comma_crt_group_insert row tail)"

text \<open>
The result labels are grouped in one right fold over the raw composition.
This is the executable table publisher: raw transition rows are constructed
once, then each label's Boolean column is accumulated as rows are visited.
The support filter drops precisely empty columns; it is structural CRT support,
not a 924-phase probe and not a syntactic-false test.
\<close>

fun comma_crt_group_rows ::
    "comma_crt_return_row list \<Rightarrow> comma_crt_return_row list" where
  "comma_crt_group_rows [] = []"
| "comma_crt_group_rows (row#rows) =
    comma_crt_group_insert row (comma_crt_group_rows rows)"

fun comma_crt_group_column ::
    "comma_semantic_b1_result \<Rightarrow> comma_crt_return_row list \<Rightarrow>
      comma_crt_column" where
  "comma_crt_group_column outcome [] = Comma_CRT_Bool False"
| "comma_crt_group_column outcome (row#rows) =
    (if snd row=outcome then fst row else comma_crt_group_column outcome rows)"

definition comma_crt_power_table ::
    "nat \<Rightarrow> comma_crt_return_row list \<Rightarrow>
      (nat \<Rightarrow> comma_crt_return_row list) \<Rightarrow>
      comma_crt_return_row list" where
  "comma_crt_power_table span left_rows right_tables =
    filter (\<lambda>row. comma_crt_supported (fst row))
      (comma_crt_group_rows
        (comma_crt_compose_raw_rows span left_rows right_tables))"

text \<open>
Runtime lookup tests the published CRT predicates at the requested phase.
The option records absence explicitly; a stored Invalid label remains
distinguishable from a missing row.
\<close>

definition comma_crt_result_at ::
    "comma_crt_return_row list \<Rightarrow> nat \<Rightarrow>
      comma_semantic_b1_result option" where
  "comma_crt_result_at rows phase =
    map_option snd (List.find (\<lambda>row. comma_crt_eval phase (fst row)) rows)"

definition comma_crt_rows_stop242 :: "comma_crt_return_row list \<Rightarrow> bool" where
  "comma_crt_rows_stop242 rows \<longleftrightarrow>
    list_all (\<lambda>row. case snd row of
      Comma_Semantic_B1_Stop D \<Rightarrow> D\<le>242
    | _ \<Rightarrow> False) rows"

lemma comma_crt_group_insert_admitted:
  assumes row: "comma_crt_admitted 0 (fst row)"
    and groups: "comma_crt_rows_admitted grouped"
  shows "comma_crt_rows_admitted (comma_crt_group_insert row grouped)"
  using row groups
  by (induction grouped) (auto simp: comma_crt_rows_admitted_def
      comma_crt_group_insert.simps split: if_splits
      intro: comma_crt_apply_admitted)

lemma comma_crt_group_rows_admitted:
  assumes "comma_crt_rows_admitted rows"
  shows "comma_crt_rows_admitted (comma_crt_group_rows rows)"
  using assms
proof (induction rows)
  case Nil
  then show ?case by (simp add: comma_crt_rows_admitted_def)
next
  case (Cons row rows)
  have row: "comma_crt_admitted 0 (fst row)"
    and rest: "comma_crt_rows_admitted rows"
    using Cons.prems by (auto simp: comma_crt_rows_admitted_def)
  show ?case
    using comma_crt_group_insert_admitted[OF row Cons.IH[OF rest]] by simp
qed

lemma comma_crt_group_insert_label_set:
  "set (map snd (comma_crt_group_insert row grouped)) =
    insert (snd row) (set (map snd grouped))"
  by (induction grouped) (auto simp: comma_crt_group_insert.simps split: if_splits)

lemma comma_crt_group_rows_label_set:
  "set (map snd (comma_crt_group_rows rows)) = set (map snd rows)"
  by (induction rows)
    (simp_all only: comma_crt_group_rows.simps comma_crt_group_insert_label_set
      list.map list.set)

lemma comma_crt_group_insert_labels_distinct:
  assumes "distinct (map snd grouped)"
  shows "distinct (map snd (comma_crt_group_insert row grouped))"
  using assms
proof (induction grouped)
  case Nil
  then show ?case by (simp add: comma_crt_group_insert.simps)
next
  case (Cons head tail)
  have tail_distinct: "distinct (map snd tail)"
    using Cons.prems by simp
  have label_absent: "snd head \<notin> set (map snd tail)"
    using Cons.prems by simp
  show ?case
  proof (cases "snd row=snd head")
    case True
    then show ?thesis using Cons.prems by (simp add: comma_crt_group_insert.simps)
  next
    case False
    have tail_labels:
      "set (map snd (comma_crt_group_insert row tail)) =
        insert (snd row) (set (map snd tail))"
      by (rule comma_crt_group_insert_label_set)
    have head_absent:
      "snd head \<notin> set (map snd (comma_crt_group_insert row tail))"
      using label_absent False tail_labels by auto
    have tail_distinct':
      "distinct (map snd (comma_crt_group_insert row tail))"
      by (rule Cons.IH[OF tail_distinct])
    show ?thesis using False head_absent tail_distinct'
      by (simp add: comma_crt_group_insert.simps)
  qed
qed

lemma comma_crt_group_rows_labels_distinct:
  "distinct (map snd (comma_crt_group_rows rows))"
  by (induction rows) (auto intro: comma_crt_group_insert_labels_distinct)

lemma comma_crt_group_column_insert_set:
  assumes row: "comma_crt_admitted 0 (fst row)"
    and groups: "comma_crt_rows_admitted grouped"
  shows "comma_crt_set
      (comma_crt_group_column outcome (comma_crt_group_insert row grouped)) =
    (if snd row=outcome then
       comma_crt_set (comma_crt_group_column outcome grouped) \<union>
         comma_crt_set (fst row)
     else comma_crt_set (comma_crt_group_column outcome grouped))"
  using row groups
proof (induction grouped)
  case Nil
  then show ?case by (cases row) (auto simp: comma_crt_set_def)
next
  case (Cons head tail)
  have head_admitted: "comma_crt_admitted 0 (fst head)"
    using Cons.prems(2) by (auto simp: comma_crt_rows_admitted_def)
  have tail_admitted: "comma_crt_rows_admitted tail"
    using Cons.prems(2) by (auto simp: comma_crt_rows_admitted_def)
  show ?case
    using Cons.IH[OF Cons.prems(1) tail_admitted] head_admitted Cons.prems(1)
    by (cases row; cases head)
      (auto simp: comma_crt_group_insert.simps comma_crt_group_column.simps
        comma_crt_apply_or_set split: if_splits)
qed

lemma comma_crt_group_rows_column_set:
  assumes admitted: "comma_crt_rows_admitted rows"
  shows "comma_crt_set (comma_crt_group_column outcome (comma_crt_group_rows rows)) =
    comma_crt_set (comma_crt_collect_output outcome rows)"
  using admitted
proof (induction rows)
  case Nil
  then show ?case by (simp add: comma_crt_set_def)
next
  case (Cons row rows)
  have row_admitted: "comma_crt_admitted 0 (fst row)"
    and rows_admitted: "comma_crt_rows_admitted rows"
    using Cons.prems by (auto simp: comma_crt_rows_admitted_def)
  have grouped_admitted: "comma_crt_rows_admitted (comma_crt_group_rows rows)"
    by (rule comma_crt_group_rows_admitted[OF rows_admitted])
  have collect_admitted:
    "comma_crt_admitted 0 (comma_crt_collect_output outcome rows)"
    by (rule comma_crt_collect_output_admitted[OF rows_admitted])
  have insert_set:
    "comma_crt_set (comma_crt_group_column outcome
        (comma_crt_group_insert row (comma_crt_group_rows rows))) =
      (if snd row=outcome then
        comma_crt_set (comma_crt_group_column outcome (comma_crt_group_rows rows)) \<union>
          comma_crt_set (fst row)
       else comma_crt_set (comma_crt_group_column outcome (comma_crt_group_rows rows)))"
    by (rule comma_crt_group_column_insert_set[OF row_admitted grouped_admitted])
  show ?case
    using insert_set Cons.IH[OF rows_admitted] row_admitted
    by (cases "snd row=outcome")
      (simp_all add: comma_crt_group_rows.simps comma_crt_collect_output.simps
        comma_crt_apply_or_set collect_admitted Un_commute)
qed

lemma comma_crt_group_column_member:
  assumes distinct: "distinct (map snd grouped)"
    and row: "row\<in>set grouped"
  shows "comma_crt_group_column (snd row) grouped=fst row"
  using distinct row
proof (induction grouped arbitrary: row)
  case Nil
  then show ?case by simp
next
  case (Cons head tail)
  have parts: "snd head\<notin>set (map snd tail) \<and> distinct (map snd tail)"
    using Cons.prems(1) by (simp only: list.map distinct.simps; blast)
  have tail_distinct: "distinct (map snd tail)" by (rule conjunct2[OF parts])
  show ?case
  proof (cases "row=head")
    case True
    show ?thesis by (simp only: True comma_crt_group_column.simps if_P[OF refl])
  next
    case False
    have row_tail: "row\<in>set tail"
      using Cons.prems(2) False by (simp only: list.set insert_iff; blast)
    have row_label: "snd row\<in>set (map snd tail)"
      unfolding set_map by (rule imageI[OF row_tail])
    have labels_differ: "snd head\<noteq>snd row"
    proof
      assume equal: "snd head=snd row"
      have member: "snd head\<in>set (map snd tail)"
        using row_label by (simp only: equal)
      show False by (rule notE[OF conjunct1[OF parts] member])
    qed
    have tail_result:
      "comma_crt_group_column (snd row) tail=fst row"
      by (rule Cons.IH[OF tail_distinct row_tail])
    show ?thesis
      by (simp only: comma_crt_group_column.simps labels_differ if_False tail_result)
  qed
qed

lemma comma_crt_group_column_nonempty_member:
  assumes nonempty:
    "comma_crt_set (comma_crt_group_column outcome grouped)\<noteq>{}"
  shows "\<exists>row\<in>set grouped. snd row=outcome"
  using nonempty
proof (induction grouped arbitrary: outcome)
  case Nil
  then show ?case by (simp add: comma_crt_set_def)
next
  case (Cons head tail)
  show ?case
  proof (cases "snd head=outcome")
    case True
    then show ?thesis by auto
  next
    case False
    have tail_nonempty:
      "comma_crt_set (comma_crt_group_column outcome tail)\<noteq>{}"
      using Cons.prems False by simp
    obtain row where row: "row\<in>set tail" "snd row=outcome"
      using Cons.IH[OF tail_nonempty] by blast
    then show ?thesis by auto
  qed
qed

lemma comma_crt_grouped_rows_fiber:
  assumes admitted: "comma_crt_rows_admitted rows"
    and sound: "\<And>row phase. row\<in>set rows \<Longrightarrow> phase<924 \<Longrightarrow>
      phase\<in>comma_crt_set (fst row) \<Longrightarrow> snd row=action phase"
    and cover: "\<And>phase. phase<924 \<Longrightarrow>
      \<exists>row\<in>set rows. phase\<in>comma_crt_set (fst row) \<and>
        snd row=action phase"
  shows "comma_crt_set (comma_crt_group_column outcome (comma_crt_group_rows rows)) =
    {phase. phase<924 \<and> action phase=outcome}"
proof (rule set_eqI)
  fix phase :: nat
  show "phase\<in>comma_crt_set
      (comma_crt_group_column outcome (comma_crt_group_rows rows)) \<longleftrightarrow>
      phase\<in>{phase. phase<924 \<and> action phase=outcome}"
  proof
    assume member: "phase\<in>comma_crt_set
      (comma_crt_group_column outcome (comma_crt_group_rows rows))"
    have grouped_set:
      "comma_crt_set (comma_crt_group_column outcome (comma_crt_group_rows rows)) =
        comma_crt_set (comma_crt_collect_output outcome rows)"
      by (rule comma_crt_group_rows_column_set[OF admitted])
    have collected:
      "phase\<in>(\<Union>row\<in>{row\<in>set rows. snd row=outcome}.
        comma_crt_set (fst row))"
      using member grouped_set comma_crt_collect_output_set[OF admitted, of outcome]
      by simp
    then obtain row where row: "row\<in>set rows" "snd row=outcome"
      "phase\<in>comma_crt_set (fst row)" by auto
    have bound: "phase<924" using row(3) by (auto simp: comma_crt_set_def)
    have "snd row=action phase" using sound[OF row(1) bound row(3)] .
    with row(2) bound show "phase\<in>{phase. phase<924 \<and> action phase=outcome}"
      by simp
  next
    assume member: "phase\<in>{phase. phase<924 \<and> action phase=outcome}"
    then have bound: "phase<924" and action: "action phase=outcome" by auto
    obtain row where row: "row\<in>set rows"
      "phase\<in>comma_crt_set (fst row)" "snd row=action phase"
      using cover[OF bound] by blast
    have row_label: "snd row=outcome" using row(3) action by simp
    have row_in_filter: "row\<in>{row\<in>set rows. snd row=outcome}"
      using row(1) row_label by simp
    have collected:
      "phase\<in>(\<Union>row\<in>{row\<in>set rows. snd row=outcome}.
        comma_crt_set (fst row))"
      by (rule UN_I[
          where A="{row\<in>set rows. snd row=outcome}" and a=row
            and B="\<lambda>row. comma_crt_set (fst row)" and b=phase,
          OF row_in_filter row(2)])
    have grouped_set:
      "comma_crt_set (comma_crt_group_column outcome (comma_crt_group_rows rows)) =
        comma_crt_set (comma_crt_collect_output outcome rows)"
      by (rule comma_crt_group_rows_column_set[OF admitted])
    show "phase\<in>comma_crt_set
      (comma_crt_group_column outcome (comma_crt_group_rows rows))"
      using collected grouped_set comma_crt_collect_output_set[OF admitted, of outcome]
      by simp
  qed
qed

theorem comma_crt_grouped_table_exact:
  assumes admitted: "comma_crt_rows_admitted rows"
    and sound: "\<And>row phase. row\<in>set rows \<Longrightarrow> phase<924 \<Longrightarrow>
      phase\<in>comma_crt_set (fst row) \<Longrightarrow> snd row=action phase"
    and cover: "\<And>phase. phase<924 \<Longrightarrow>
      \<exists>row\<in>set rows. phase\<in>comma_crt_set (fst row) \<and>
        snd row=action phase"
  shows "comma_semantic_b1_binding_table_exact action 0
      (map comma_crt_project_row
        (filter (\<lambda>row. comma_crt_supported (fst row))
          (comma_crt_group_rows rows)))"
proof -
  let ?grouped = "comma_crt_group_rows rows"
  let ?table = "filter (\<lambda>row. comma_crt_supported (fst row)) ?grouped"
  have grouped_admitted: "comma_crt_rows_admitted ?grouped"
    by (rule comma_crt_group_rows_admitted[OF admitted])
  have labels_distinct: "distinct (map snd ?grouped)"
    by (rule comma_crt_group_rows_labels_distinct)
  have table_admitted: "comma_crt_rows_admitted ?table"
    using grouped_admitted by (auto simp: comma_crt_rows_admitted_def)
  have exact_rows:
    "\<forall>row\<in>set ?table. comma_semantic_b1_binding_row_exact action 0
      (comma_crt_project_row row)"
  proof (intro ballI)
    fix row
    assume row: "row\<in>set ?table"
    have grouped_row: "row\<in>set ?grouped" and supported: "comma_crt_supported (fst row)"
      using row by auto
    have selected:
      "comma_crt_group_column (snd row) ?grouped=fst row"
      by (rule comma_crt_group_column_member[OF labels_distinct grouped_row])
    have fiber:
      "comma_crt_set (fst row)={phase. phase<924 \<and> action phase=snd row}"
      using comma_crt_grouped_rows_fiber[OF admitted sound cover, of "snd row"]
        selected by simp
    have row_admitted: "comma_crt_admitted 0 (fst row)"
      using table_admitted row by (cases row) (auto simp: comma_crt_rows_admitted_def)
    have nonempty: "comma_crt_set (fst row)\<noteq>{}"
      using comma_crt_supported_nonempty[OF row_admitted] supported by blast
    show "comma_semantic_b1_binding_row_exact action 0 (comma_crt_project_row row)"
      by (simp only: comma_semantic_b1_binding_row_exact_zero_iff
          comma_crt_project_row_def fst_conv snd_conv;
          rule conjI[OF nonempty fiber])
  qed
  have key_injective: "inj_on (\<lambda>row. comma_crt_set (fst row)) (set ?table)"
  proof (rule inj_onI)
    fix left right
    assume left: "left\<in>set ?table" and right: "right\<in>set ?table"
      and keys: "comma_crt_set (fst left)=comma_crt_set (fst right)"
    have left_group: "left\<in>set ?grouped" and right_group: "right\<in>set ?grouped"
      using left right by auto
    have left_exact:
      "comma_semantic_b1_binding_row_exact action 0 (comma_crt_project_row left)"
      using exact_rows left by blast
    have lfiber:
      "comma_crt_set (fst left)={phase. phase<924 \<and> action phase=snd left}"
      using comma_crt_grouped_rows_fiber[OF admitted sound cover, of "snd left"]
        comma_crt_group_column_member[OF labels_distinct left_group]
      by simp
    have rfiber:
      "comma_crt_set (fst right)={phase. phase<924 \<and> action phase=snd right}"
      using comma_crt_grouped_rows_fiber[OF admitted sound cover, of "snd right"]
        comma_crt_group_column_member[OF labels_distinct right_group]
      by simp
    have support: "comma_crt_set (fst left)\<noteq>{}"
      using left_exact
      by (simp only: comma_semantic_b1_binding_row_exact_def
        comma_crt_project_row_def fst_conv snd_conv; blast)
    obtain phase where member: "phase\<in>comma_crt_set (fst left)"
      using support by blast
    have other_member: "phase\<in>comma_crt_set (fst right)"
      using member by (simp only: keys)
    have left_value: "action phase=snd left"
      using member by (simp only: lfiber mem_Collect_eq; blast)
    have right_value: "action phase=snd right"
      using other_member by (simp only: rfiber mem_Collect_eq; blast)
    have same_snd: "snd left=snd right"
      by (rule trans[OF sym[OF left_value] right_value])
    have labels_injective: "inj_on snd (set ?grouped)"
      using labels_distinct by (simp add: distinct_map)
    show "left=right"
      by (rule inj_onD[OF labels_injective same_snd left_group right_group])
  qed
  have grouped_distinct: "distinct ?grouped"
    using labels_distinct by (simp only: distinct_map; blast)
  have table_distinct: "distinct ?table"
    by (rule distinct_filter[OF grouped_distinct])
  have keys_distinct:
    "distinct (map fst (map comma_crt_project_row ?table))"
    using table_distinct key_injective
    by (simp add: distinct_map comma_crt_project_row_def comp_def)
  have covered: "(\<Union> (fst ` set (map comma_crt_project_row ?table)))={..<924}"
  proof (rule set_eqI)
    fix phase :: nat
    show "phase\<in>(\<Union> (fst ` set (map comma_crt_project_row ?table)))
        \<longleftrightarrow> phase\<in>{..<924}"
    proof
      assume member: "phase\<in>(\<Union> (fst ` set (map comma_crt_project_row ?table)))"
      then show "phase\<in>{..<924}"
        using exact_rows by (auto simp: comma_semantic_b1_binding_row_exact_def
          comma_crt_project_row_def)
    next
      assume phase: "phase\<in>{..<924}"
      let ?out="action phase"
      have fiber:
        "phase\<in>comma_crt_set (comma_crt_group_column ?out ?grouped)"
        using comma_crt_grouped_rows_fiber[OF admitted sound cover, of ?out] phase by simp
      have group_nonempty:
        "comma_crt_set (comma_crt_group_column ?out ?grouped)\<noteq>{}"
        using fiber by auto
      obtain row where row: "row\<in>set ?grouped" "snd row=?out"
        using comma_crt_group_column_nonempty_member[OF group_nonempty] by blast
      have row_support: "comma_crt_supported (fst row)"
      proof -
        have row_admitted: "comma_crt_admitted 0 (fst row)"
          using grouped_admitted row by (auto simp: comma_crt_rows_admitted_def)
        have row_col: "comma_crt_group_column ?out ?grouped=fst row"
          using comma_crt_group_column_member[OF labels_distinct row(1)] row(2)
          by simp
        have row_nonempty: "comma_crt_set (fst row)\<noteq>{}"
          using fiber row_col by auto
        show ?thesis
          using comma_crt_supported_nonempty[OF row_admitted] row_nonempty by blast
      qed
      have retained: "row\<in>set ?table" using row row_support by auto
      have row_col: "comma_crt_group_column ?out ?grouped=fst row"
        using comma_crt_group_column_member[OF labels_distinct row(1)] row(2)
        by simp
      have "phase\<in>comma_crt_set (fst row)"
        using fiber row_col by simp
      then show "phase\<in>(\<Union> (fst ` set (map comma_crt_project_row ?table)))"
        using retained by (cases row) (auto simp: comma_crt_project_row_def)
    qed
  qed
  have disjoint:
    "\<forall>left\<in>set (map comma_crt_project_row ?table).
       \<forall>right\<in>set (map comma_crt_project_row ?table).
         left\<noteq>right \<longrightarrow> fst left\<inter>fst right={}"
  proof (intro ballI impI)
    fix left right
    assume left: "left\<in>set (map comma_crt_project_row ?table)"
      and right: "right\<in>set (map comma_crt_project_row ?table)"
      and different: "left\<noteq>right"
    then obtain lrow rrow where lrow: "lrow\<in>set ?table"
      and rrow: "rrow\<in>set ?table"
      and left_eq: "left=comma_crt_project_row lrow"
      and right_eq: "right=comma_crt_project_row rrow" by auto
    obtain lcol lresult where lp: "lrow=(lcol,lresult)" by (cases lrow) auto
    obtain rcol rresult where rp: "rrow=(rcol,rresult)" by (cases rrow) auto
    have lrow_group: "lrow\<in>set ?grouped" using lrow by auto
    have rrow_group: "rrow\<in>set ?grouped" using rrow by auto
    have lexact:
      "comma_crt_set lcol={phase. phase<924 \<and> action phase=lresult}"
      using comma_crt_grouped_rows_fiber[OF admitted sound cover, of lresult]
        comma_crt_group_column_member[OF labels_distinct lrow_group] lp
      by simp
    have rexact:
      "comma_crt_set rcol={phase. phase<924 \<and> action phase=rresult}"
      using comma_crt_grouped_rows_fiber[OF admitted sound cover, of rresult]
        comma_crt_group_column_member[OF labels_distinct rrow_group] rp
      by simp
    have labels_differ: "lresult\<noteq>rresult"
    proof
      assume same: "lresult=rresult"
      have lcol_group: "comma_crt_group_column lresult ?grouped=lcol"
      proof -
        have lrow_group: "lrow\<in>set ?grouped" using lrow by auto
        show ?thesis
          using comma_crt_group_column_member[OF labels_distinct lrow_group] lp by simp
      qed
      have rcol_group: "comma_crt_group_column rresult ?grouped=rcol"
      proof -
        have rrow_group: "rrow\<in>set ?grouped" using rrow by auto
        show ?thesis
          using comma_crt_group_column_member[OF labels_distinct rrow_group] rp by simp
      qed
      have columns: "lcol=rcol"
      proof -
        have "lcol=comma_crt_group_column lresult ?grouped"
          by (rule sym[OF lcol_group])
        also have "...=comma_crt_group_column rresult ?grouped"
          by (simp only: same)
        also have "...=rcol" by (rule rcol_group)
        finally show ?thesis .
      qed
      have "lrow=rrow" by (simp only: lp rp columns same)
      with left_eq right_eq different show False by simp
    qed
    have left_fiber: "phase\<in>fst left \<Longrightarrow> action phase=lresult" for phase
      using left_eq lp lexact by (auto simp: comma_crt_project_row_def)
    have right_fiber: "phase\<in>fst right \<Longrightarrow> action phase=rresult" for phase
      using right_eq rp rexact by (auto simp: comma_crt_project_row_def)
    show "fst left\<inter>fst right={}"
    proof (rule set_eqI)
      fix phase
      show "phase\<in>fst left\<inter>fst right \<longleftrightarrow> phase\<in>{}"
      proof
        assume member: "phase\<in>fst left\<inter>fst right"
        have left_value: "action phase=lresult"
          using left_fiber member by auto
        have right_value: "action phase=rresult"
          using right_fiber member by auto
        have labels_equal: "lresult=rresult"
          by (rule trans[OF sym[OF left_value] right_value])
        have False by (rule notE[OF labels_differ labels_equal])
        then show "phase\<in>{}" by (rule FalseE)
      next
        show "phase\<in>{} \<Longrightarrow> phase\<in>fst left\<inter>fst right" by simp
      qed
    qed
  qed
  show ?thesis
    using keys_distinct covered exact_rows disjoint
    by (simp add: comma_semantic_b1_binding_table_exact_def)
qed

theorem comma_crt_power_table_refines_for_targets:
  fixes span :: nat
    and left_action :: "nat \<Rightarrow> nat \<Rightarrow> comma_semantic_b1_result"
    and right_action :: "nat \<Rightarrow> nat \<Rightarrow> comma_semantic_b1_result"
    and root :: nat
    and target :: "nat \<Rightarrow> bool"
  assumes left_admitted: "comma_crt_rows_admitted left_rows"
    and right_admitted: "\<And>next_root. comma_crt_rows_admitted (right_rows next_root)"
    and left_exact:
      "comma_semantic_b1_binding_table_exact (\<lambda>phase. left_action phase root) 0
        (map comma_crt_project_row left_rows)"
    and right_exact:
      "\<And>next_root. target next_root \<Longrightarrow> comma_semantic_b1_binding_table_exact
        (\<lambda>phase. right_action phase next_root) 0
        (map comma_crt_project_row (right_rows next_root))"
    and live_targets:
      "\<And>phase next_root. phase<924 \<Longrightarrow>
        left_action phase root=Comma_Semantic_B1_Live next_root \<Longrightarrow>
        target next_root"
  shows "comma_semantic_b1_binding_table_exact
      (\<lambda>phase. comma_semantic_word_then span left_action right_action phase root) 0
      (map comma_crt_project_row
        (comma_crt_power_table span left_rows right_rows))"
proof -
  let ?raw = "comma_crt_compose_raw_rows span left_rows right_rows"
  let ?semantic_raw =
    "comma_semantic_b1_compose_raw_rows span (map comma_crt_project_row left_rows)
      (\<lambda>next_root. map comma_crt_project_row (right_rows next_root))"
  have raw_admitted: "comma_crt_rows_admitted ?raw"
    by (rule comma_crt_compose_raw_rows_admitted[OF left_admitted right_admitted])
  have projected: "map comma_crt_project_row ?raw=?semantic_raw"
    by (rule comma_crt_compose_raw_rows_projects[OF left_admitted right_admitted])
  have sound:
    "\<And>row phase. row\<in>set ?raw \<Longrightarrow> phase<924 \<Longrightarrow>
      phase\<in>comma_crt_set (fst row) \<Longrightarrow>
      snd row=comma_semantic_word_then span left_action right_action phase root"
  proof -
    fix row phase
    assume row: "row\<in>set ?raw" and phase: "phase<924"
      and member: "phase\<in>comma_crt_set (fst row)"
    have semantic_row: "comma_crt_project_row row\<in>set ?semantic_raw"
    proof -
      have projected_member:
        "comma_crt_project_row row\<in>set (map comma_crt_project_row ?raw)"
        using row by simp
      show ?thesis using projected_member projected by simp
    qed
    have semantic_member: "phase\<in>fst (comma_crt_project_row row)"
      using member by (simp add: comma_crt_project_row_def)
    have "snd (comma_crt_project_row row)=
        comma_semantic_word_then span left_action right_action phase root"
      by (rule comma_semantic_b1_compose_raw_rows_sound_for_targets[
        where left_action=left_action and right_action=right_action and root=root
          and n=span and target=target
          and right_rows="\<lambda>next_root. map comma_crt_project_row (right_rows next_root)",
        OF left_exact _ _ semantic_row phase semantic_member])
        (erule right_exact, erule (1) live_targets)
    then show "snd row=comma_semantic_word_then span left_action right_action phase root"
      by (simp add: comma_crt_project_row_def)
  qed
  have cover:
    "\<And>phase. phase<924 \<Longrightarrow>
      \<exists>row\<in>set ?raw. phase\<in>comma_crt_set (fst row) \<and>
        snd row=comma_semantic_word_then span left_action right_action phase root"
  proof -
    fix phase :: nat
    assume phase: "phase<924"
    obtain semantic_row where semantic_row:
      "semantic_row\<in>set ?semantic_raw"
      "phase\<in>fst semantic_row"
      "snd semantic_row=comma_semantic_word_then span left_action right_action phase root"
      by (rule comma_semantic_b1_compose_raw_rows_cover_for_targets[
        where left_action=left_action and right_action=right_action and root=root
          and n=span and target=target
          and right_rows="\<lambda>next_root. map comma_crt_project_row (right_rows next_root)",
        OF left_exact _ _ phase])
        (erule right_exact, erule (1) live_targets, blast)
    have projected_member: "semantic_row\<in>set (map comma_crt_project_row ?raw)"
      using projected semantic_row(1) by simp
    then obtain row where row: "row\<in>set ?raw"
      and projection: "comma_crt_project_row row=semantic_row" by auto
    have projection_eq:
      "semantic_row=(comma_crt_set (fst row),snd row)"
      using projection by (simp add: comma_crt_project_row_def)
    have phase_member: "phase\<in>comma_crt_set (fst row)"
      using semantic_row(2) projection_eq by simp
    have result_value: "snd row=comma_semantic_word_then span left_action right_action phase root"
      using semantic_row(3) projection_eq by (simp only: projection_eq snd_conv)
    show "\<exists>row\<in>set ?raw. phase\<in>comma_crt_set (fst row) \<and>
        snd row=comma_semantic_word_then span left_action right_action phase root"
      using row phase_member result_value by blast
  qed
  show ?thesis
    unfolding comma_crt_power_table_def
    by (rule comma_crt_grouped_table_exact[OF raw_admitted sound cover])
qed

lemma comma_crt_result_at_exact:
  fixes action :: "nat \<Rightarrow> comma_semantic_b1_result"
  assumes table:
      "comma_semantic_b1_binding_table_exact action 0
        (map comma_crt_project_row rows)"
    and phase: "phase<924"
  shows "comma_crt_result_at rows phase=Some (action phase)"
proof -
  let ?matches = "\<lambda>row. comma_crt_eval phase (fst row)"
  have projected_cover:
      "(\<Union> (fst ` set (map comma_crt_project_row rows)))={..<924}"
    using table by (simp add: comma_semantic_b1_binding_table_exact_def)
  have phase_covered:
      "phase\<in>(\<Union> (fst ` set (map comma_crt_project_row rows)))"
    using phase projected_cover by simp
  then obtain column where column_image:
      "column\<in>fst ` set (map comma_crt_project_row rows)"
    and phase_column: "phase\<in>column"
    by blast
  then obtain witness where witness: "witness\<in>set rows"
    and column_eq: "column=comma_crt_set (fst witness)"
    by (auto simp: comma_crt_project_row_def)
  have witness_matches: "?matches witness"
    using phase phase_column column_eq
    by (auto simp: comma_crt_set_def)
  obtain witness_column witness_label where
      witness_pair: "witness=(witness_column,witness_label)"
    by (cases witness) auto
  have witness_pair_member: "(witness_column,witness_label)\<in>set rows"
    using witness witness_pair by simp
  have witness_pair_matches: "?matches (witness_column,witness_label)"
    using witness_matches witness_pair by simp
  have match_exists:
      "\<exists>candidate. candidate\<in>set rows \<and> ?matches candidate"
    by (rule exI[of _ "(witness_column,witness_label)"])
      (rule conjI[OF witness_pair_member witness_pair_matches])
  have find_present: "List.find ?matches rows\<noteq>None"
  proof
    assume none: "List.find ?matches rows=None"
    have no_match: "\<not> (\<exists>candidate. candidate\<in>set rows \<and> ?matches candidate)"
      using none unfolding find_None_iff by blast
    show False using no_match match_exists by blast
  qed
  then obtain selected where found: "List.find ?matches rows=Some selected"
    by (cases "List.find ?matches rows") auto
  obtain index where index_bound: "index<length rows"
    and index_matches: "?matches (rows!index)"
    and selected_eq: "selected=rows!index"
    using found by (auto simp: find_Some_iff)
  have selected_member: "selected\<in>set rows"
    using nth_mem[OF index_bound] selected_eq by simp
  have selected_matches: "?matches selected"
    using index_matches selected_eq by simp
  have selected_projected: "comma_crt_project_row selected\<in>
      set (map comma_crt_project_row rows)"
    using selected_member by simp
  have selected_exact:
      "comma_semantic_b1_binding_row_exact action 0
        (comma_crt_project_row selected)"
    using table selected_projected
    by (auto simp: comma_semantic_b1_binding_table_exact_def)
  have selected_phase: "phase\<in>fst (comma_crt_project_row selected)"
    using phase selected_matches
    by (auto simp: comma_crt_project_row_def comma_crt_set_def)
  have selected_label: "snd selected=action phase"
    using selected_exact selected_phase
    by (auto simp: comma_semantic_b1_binding_row_exact_zero_iff
      comma_crt_project_row_def)
  show ?thesis
    unfolding comma_crt_result_at_def
    using found selected_label by simp
qed

lemma comma_crt_result_at_preserves_invalid:
  "comma_crt_result_at
      [(Comma_CRT_Bool True,Comma_Semantic_B1_Invalid)] 0 =
    Some Comma_Semantic_B1_Invalid"
  by (simp add: comma_crt_result_at_def)

lemma comma_crt_result_at_rejects_malformed_width:
  "comma_crt_result_at
      [(Comma_CRT_Node 0 [],Comma_Semantic_B1_Invalid)] 0 = None"
  by (simp add: comma_crt_result_at_def comma_crt_period_def)

lemma comma_crt_result_at_stop242:
  assumes rows: "comma_crt_rows_stop242 rows"
    and lookup: "comma_crt_result_at rows phase=Some result"
  obtains D where "result=Comma_Semantic_B1_Stop D" "D\<le>242"
proof -
  have find_some:
      "\<exists>selected. List.find (\<lambda>row. comma_crt_eval phase (fst row)) rows=
        Some selected"
    using lookup by (cases
      "List.find (\<lambda>row. comma_crt_eval phase (fst row)) rows")
      (auto simp: comma_crt_result_at_def)
  then obtain selected where found:
      "List.find (\<lambda>row. comma_crt_eval phase (fst row)) rows=Some selected"
    by blast
  obtain index where index_bound: "index<length rows"
    and selected_eq: "selected=rows!index"
    using found by (auto simp: find_Some_iff)
  have selected_member: "selected\<in>set rows"
    using nth_mem[OF index_bound] selected_eq by simp
  have selected_control:
      "case snd selected of
        Comma_Semantic_B1_Stop D \<Rightarrow> D\<le>242
      | _ \<Rightarrow> False"
    using rows selected_member
    by (simp add: comma_crt_rows_stop242_def list_all_iff)
  obtain D where selected_stop: "snd selected=Comma_Semantic_B1_Stop D"
    and height: "D\<le>242"
    using selected_control by (cases "snd selected") auto
  have result_eq: "result=Comma_Semantic_B1_Stop D"
    using lookup found selected_stop
    by (simp add: comma_crt_result_at_def)
  show thesis by (rule that[OF result_eq height])
qed

theorem comma_crt_square_table_refines:
  fixes k root :: nat
  assumes left_admitted: "comma_crt_rows_admitted left_rows"
    and right_admitted: "\<And>next_root. comma_crt_rows_admitted (right_rows next_root)"
    and left_exact:
      "comma_semantic_b1_binding_table_exact
        (\<lambda>phase. comma_semantic_b1_of_word (comma_orbit_word k phase root)) 0
        (map comma_crt_project_row left_rows)"
    and right_exact:
      "\<And>next_root. next_root<46 \<Longrightarrow> comma_semantic_b1_binding_table_exact
        (\<lambda>phase. comma_semantic_b1_of_word
          (comma_orbit_word k phase next_root)) 0
        (map comma_crt_project_row (right_rows next_root))"
    and root: "root<46"
  shows "comma_semantic_b1_binding_table_exact
      (\<lambda>phase. comma_semantic_b1_of_word (comma_orbit_word (Suc k) phase root)) 0
      (map comma_crt_project_row
        (comma_crt_power_table (2^k) left_rows right_rows))"
proof -
  let ?action = "\<lambda>phase index.
    comma_semantic_b1_of_word (comma_orbit_word k phase index)"
  have left_targets:
      "\<And>phase next_root. phase<924 \<Longrightarrow>
        ?action phase root=Comma_Semantic_B1_Live next_root \<Longrightarrow>
        next_root<46"
  proof -
    fix phase next_root
    assume phase: "phase<924"
      and live: "?action phase root=Comma_Semantic_B1_Live next_root"
    have word_live: "comma_orbit_word k phase root=Comma_Word_Live next_root"
      using live by (cases "comma_orbit_word k phase root") auto
    show "next_root<46"
      by (rule comma_orbit_word_live_bound[OF word_live])
  qed
  have composed:
    "comma_semantic_b1_binding_table_exact
      (\<lambda>phase. comma_semantic_word_then (2^k) ?action ?action phase root) 0
      (map comma_crt_project_row
        (comma_crt_power_table (2^k) left_rows right_rows))"
    by (rule comma_crt_power_table_refines_for_targets[
        where span="2^k" and left_action="?action" and right_action="?action"
          and root=root and target="(\<lambda>next_root. next_root<46)"])
       (fact left_admitted, fact right_admitted, fact left_exact,
        fact right_exact, fact left_targets)
  have square:
    "\<And>phase. phase<924 \<Longrightarrow>
      comma_semantic_word_then (2^k) ?action ?action phase root=
        comma_semantic_b1_of_word (comma_orbit_word (Suc k) phase root)"
  proof -
    fix phase :: nat
    assume phase: "phase<924"
    show "comma_semantic_word_then (2^k) ?action ?action phase root=
        comma_semantic_b1_of_word (comma_orbit_word (Suc k) phase root)"
      by (rule sym[OF comma_semantic_b1_square[OF phase root]])
  qed
  have target_exact:
    "comma_semantic_b1_binding_table_exact
      (\<lambda>phase. comma_semantic_b1_of_word (comma_orbit_word (Suc k) phase root)) 0
      (map comma_crt_project_row
        (comma_crt_power_table (2^k) left_rows right_rows))"
    by (rule comma_semantic_b1_binding_table_exact_action_congruent
        [OF composed square])
  show ?thesis using target_exact .
qed


ML \<open>
  val audit_timer = Comma_Proof_Profile.timer "CRT power dependency audit";
  val checked = @{thms comma_crt_compose_raw_rows_projects
    comma_crt_compose_raw_rows_admitted comma_crt_collect_output_set
    comma_crt_grouped_table_exact comma_crt_result_at_exact
    comma_crt_result_at_preserves_invalid
    comma_crt_result_at_rejects_malformed_width
    comma_crt_result_at_stop242
    comma_crt_power_table_refines_for_targets comma_crt_square_table_refines};
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Executable CRT return-row power" checked;
  val _ = audit_timer "native-finished";
  val _ = Comma_Proof_Dependency_Audit.require_expected_paths @{context}
    "CRT B1 square table refinement"
    ["comma_semantic_b1_square", "comma_orbit_word_live_bound"]
    @{thms comma_crt_square_table_refines};
  val _ = audit_timer "expected-finished";
\<close>

end
