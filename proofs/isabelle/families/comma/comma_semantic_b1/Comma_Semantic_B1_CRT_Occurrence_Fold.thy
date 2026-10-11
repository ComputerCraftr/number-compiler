theory Comma_Semantic_B1_CRT_Occurrence_Fold
  imports Comma_Semantic_B1_CRT_Source_Binding
begin

text \<open>
An occurrence keeps a label-free list of admitted CRT columns, one external
clock rebase, and a separate output binding indexed by the same list.  The
list is the template geometry; result labels are not part of its identity.
Its semantic wellformedness contract records admission, support, disjointness,
and clock coverage. Concrete publication proves that contract from grouped
source rows; this theory does not materialize child return rows or enumerate
clock phases.
\<close>

record comma_semantic_b1_crt_occurrence =
  comma_semantic_b1_crt_occurrence_columns :: "comma_crt_column list"
  comma_semantic_b1_crt_occurrence_rebase :: nat
  comma_semantic_b1_crt_occurrence_beta :: "comma_semantic_b1_result list"

definition comma_semantic_b1_crt_cells_partition ::
    "nat set \<Rightarrow> nat set list \<Rightarrow> bool" where
  "comma_semantic_b1_crt_cells_partition universe cells \<longleftrightarrow>
    (\<forall>i<length cells. cells!i \<subseteq> universe) \<and>
    (\<forall>phase\<in>universe. \<exists>i<length cells. phase\<in>cells!i) \<and>
    (\<forall>i<length cells. \<forall>j<length cells.
       i\<noteq>j \<longrightarrow> cells!i \<inter> cells!j = {})"

lemma comma_semantic_b1_crt_partition_subset_cells_eq:
  assumes source_partition:
      "comma_semantic_b1_crt_cells_partition universe source_cells"
    and target_partition:
      "comma_semantic_b1_crt_cells_partition universe target_cells"
    and same_width: "length source_cells=length target_cells"
    and covered: "\<forall>i<length source_cells. source_cells!i\<subseteq>target_cells!i"
  shows "source_cells=target_cells"
proof (rule nth_equalityI)
  show width: "length source_cells=length target_cells"
    by (rule same_width)
  fix i
  assume i: "i<length source_cells"
  show "source_cells!i=target_cells!i"
  proof (rule set_eqI)
    fix phase
    show "phase\<in>source_cells!i \<longleftrightarrow> phase\<in>target_cells!i"
    proof
      assume phase: "phase\<in>source_cells!i"
      have cell_subset: "source_cells!i\<subseteq>target_cells!i"
        using covered i by blast
      show "phase\<in>target_cells!i" using cell_subset phase by blast
    next
      assume phase: "phase\<in>target_cells!i"
      have target_bounded:
        "target_cells!i\<subseteq>universe"
        using target_partition i width
        by (auto simp: comma_semantic_b1_crt_cells_partition_def)
      have phase_universe: "phase\<in>universe"
        using target_bounded phase by blast
      obtain j where j: "j<length source_cells"
        and phase_source: "phase\<in>source_cells!j"
        using source_partition phase_universe
        by (auto simp: comma_semantic_b1_crt_cells_partition_def)
      have source_subset: "source_cells!j\<subseteq>target_cells!j"
        using covered j by blast
      have phase_target_j: "phase\<in>target_cells!j"
        using source_subset phase_source by blast
      have same_index: "j=i"
      proof (rule ccontr)
        assume different: "j\<noteq>i"
        have disjoint: "target_cells!i\<inter>target_cells!j={}"
          using target_partition i j different width
          by (auto simp: comma_semantic_b1_crt_cells_partition_def)
        show False using disjoint phase phase_target_j by blast
      qed
      show "phase\<in>source_cells!i"
        using phase_source same_index by simp
    qed
  qed
qed

text \<open>
The checked representation stores template geometry once.  Occurrence
handles contain only a template index, a clock rebase and an exact binding.
Resolution is total: a foreign index is rejected rather than using HOL's
unspecified out-of-range list value.  Resolution alone is not admission;
the wellformedness and local refinement checks remain separate obligations.
\<close>

type_synonym comma_semantic_b1_crt_descriptor =
  "nat \<times> (nat \<times> comma_semantic_b1_result list)"

definition comma_semantic_b1_crt_resolve_descriptor ::
    "comma_crt_column list list \<Rightarrow>
      comma_semantic_b1_crt_descriptor \<Rightarrow>
      comma_semantic_b1_crt_occurrence option" where
  "comma_semantic_b1_crt_resolve_descriptor templates descriptor =
    (case descriptor of (cid,(rebase,beta)) \<Rightarrow>
      if cid < length templates then
        Some \<lparr>comma_semantic_b1_crt_occurrence_columns=templates!cid,
          comma_semantic_b1_crt_occurrence_rebase=rebase,
          comma_semantic_b1_crt_occurrence_beta=beta\<rparr>
      else None)"

lemma comma_semantic_b1_crt_resolve_descriptor_exact:
  assumes "cid < length templates"
  shows "comma_semantic_b1_crt_resolve_descriptor templates (cid,(rebase,beta)) =
    Some \<lparr>comma_semantic_b1_crt_occurrence_columns=templates!cid,
      comma_semantic_b1_crt_occurrence_rebase=rebase,
      comma_semantic_b1_crt_occurrence_beta=beta\<rparr>"
  using assms by (simp add: comma_semantic_b1_crt_resolve_descriptor_def)

lemma comma_semantic_b1_crt_resolve_descriptor_rejects_foreign:
  assumes "length templates \<le> cid"
  shows "comma_semantic_b1_crt_resolve_descriptor templates (cid,(rebase,beta)) = None"
  using assms by (simp add: comma_semantic_b1_crt_resolve_descriptor_def)

definition comma_semantic_b1_crt_occurrence_indexed_columns ::
    "comma_crt_column list \<Rightarrow> (nat \<times> comma_crt_column) list" where
  "comma_semantic_b1_crt_occurrence_indexed_columns columns =
    zip [0..<length columns] columns"

definition comma_semantic_b1_crt_occurrence_find_index ::
    "nat \<Rightarrow> comma_crt_column list \<Rightarrow> nat option" where
  "comma_semantic_b1_crt_occurrence_find_index phase columns =
    map_option fst (List.find (\<lambda>entry. comma_crt_eval phase (snd entry))
      (comma_semantic_b1_crt_occurrence_indexed_columns columns))"

definition comma_semantic_b1_crt_occurrence_lookup ::
    "comma_semantic_b1_crt_occurrence \<Rightarrow> nat \<Rightarrow>
      comma_semantic_b1_result option" where
  "comma_semantic_b1_crt_occurrence_lookup occurrence clock =
    (case comma_semantic_b1_crt_occurrence_find_index
        ((clock + comma_semantic_b1_crt_occurrence_rebase occurrence) mod 924)
        (comma_semantic_b1_crt_occurrence_columns occurrence) of
       None \<Rightarrow> None
     | Some index \<Rightarrow>
         if index < length (comma_semantic_b1_crt_occurrence_beta occurrence)
         then Some (comma_semantic_b1_crt_occurrence_beta occurrence ! index)
         else None)"

definition comma_semantic_b1_crt_occurrence_covered ::
    "comma_crt_column list \<Rightarrow> bool" where
  "comma_semantic_b1_crt_occurrence_covered columns \<longleftrightarrow>
    (\<forall>phase<924. \<exists>entry\<in>set
       (comma_semantic_b1_crt_occurrence_indexed_columns columns).
       phase \<in> comma_crt_set (snd entry))"

definition comma_semantic_b1_crt_occurrence_disjoint ::
    "comma_crt_column list \<Rightarrow> bool" where
  "comma_semantic_b1_crt_occurrence_disjoint columns \<longleftrightarrow>
    (\<forall>left\<in>set (comma_semantic_b1_crt_occurrence_indexed_columns columns).
       \<forall>right\<in>set (comma_semantic_b1_crt_occurrence_indexed_columns columns).
         fst left \<noteq> fst right \<longrightarrow>
           comma_crt_set (snd left) \<inter> comma_crt_set (snd right) = {})"

definition comma_semantic_b1_crt_occurrence_wellformed ::
    "comma_semantic_b1_crt_occurrence \<Rightarrow> bool" where
  "comma_semantic_b1_crt_occurrence_wellformed occurrence \<longleftrightarrow>
    comma_semantic_b1_crt_occurrence_rebase occurrence < 924 \<and>
    length (comma_semantic_b1_crt_occurrence_columns occurrence) =
      length (comma_semantic_b1_crt_occurrence_beta occurrence) \<and>
    comma_semantic_b1_crt_occurrence_columns occurrence \<noteq> [] \<and>
    list_all (comma_crt_admitted 0)
      (comma_semantic_b1_crt_occurrence_columns occurrence) \<and>
    list_all comma_crt_supported
      (comma_semantic_b1_crt_occurrence_columns occurrence) \<and>
    comma_semantic_b1_crt_occurrence_disjoint
      (comma_semantic_b1_crt_occurrence_columns occurrence) \<and>
    comma_semantic_b1_crt_occurrence_covered
      (comma_semantic_b1_crt_occurrence_columns occurrence)"

lemma comma_semantic_b1_crt_occurrence_wellformed_rejects_empty:
  "\<not> comma_semantic_b1_crt_occurrence_wellformed
    \<lparr>comma_semantic_b1_crt_occurrence_columns=[],
      comma_semantic_b1_crt_occurrence_rebase=0,
      comma_semantic_b1_crt_occurrence_beta=[]\<rparr>"
  by (simp add: comma_semantic_b1_crt_occurrence_wellformed_def)

lemma comma_semantic_b1_crt_occurrence_wellformed_rejects_overlap:
  "\<not> comma_semantic_b1_crt_occurrence_wellformed
    \<lparr>comma_semantic_b1_crt_occurrence_columns=
      [Comma_CRT_Node 0
         [Comma_CRT_Bool True, Comma_CRT_Bool False,
          Comma_CRT_Bool False, Comma_CRT_Bool False],
       Comma_CRT_Node 0
         [Comma_CRT_Bool False, Comma_CRT_Bool True,
          Comma_CRT_Bool False, Comma_CRT_Bool False],
       Comma_CRT_Node 0
         [Comma_CRT_Bool True, Comma_CRT_Bool False,
          Comma_CRT_Bool False, Comma_CRT_Bool False]],
      comma_semantic_b1_crt_occurrence_rebase=0,
      comma_semantic_b1_crt_occurrence_beta=
        [Comma_Semantic_B1_Invalid, Comma_Semantic_B1_Invalid,
         Comma_Semantic_B1_Invalid]\<rparr>"
proof (rule notI)
  let ?column = "Comma_CRT_Node 0
    [Comma_CRT_Bool True, Comma_CRT_Bool False,
     Comma_CRT_Bool False, Comma_CRT_Bool False]"
  have zero: "0 \<in> comma_crt_set ?column"
    by (simp add: comma_crt_set_def comma_crt_period_def)
  assume wellformed:
    "comma_semantic_b1_crt_occurrence_wellformed
      \<lparr>comma_semantic_b1_crt_occurrence_columns=[?column,
        Comma_CRT_Node 0
          [Comma_CRT_Bool False, Comma_CRT_Bool True,
           Comma_CRT_Bool False, Comma_CRT_Bool False], ?column],
        comma_semantic_b1_crt_occurrence_rebase=0,
        comma_semantic_b1_crt_occurrence_beta=
          [Comma_Semantic_B1_Invalid, Comma_Semantic_B1_Invalid,
           Comma_Semantic_B1_Invalid]\<rparr>"
  have disjoint:
    "comma_semantic_b1_crt_occurrence_disjoint [?column,
      Comma_CRT_Node 0
        [Comma_CRT_Bool False, Comma_CRT_Bool True,
         Comma_CRT_Bool False, Comma_CRT_Bool False], ?column]"
    using wellformed
    by (simp add: comma_semantic_b1_crt_occurrence_wellformed_def)
  have indexed_zero:
    "(0, ?column) \<in> set
        (comma_semantic_b1_crt_occurrence_indexed_columns
          [?column, Comma_CRT_Node 0
            [Comma_CRT_Bool False, Comma_CRT_Bool True,
             Comma_CRT_Bool False, Comma_CRT_Bool False], ?column])"
    and indexed_two: "(2, ?column) \<in> set
        (comma_semantic_b1_crt_occurrence_indexed_columns
          [?column, Comma_CRT_Node 0
            [Comma_CRT_Bool False, Comma_CRT_Bool True,
             Comma_CRT_Bool False, Comma_CRT_Bool False], ?column])"
    by (simp_all add: comma_semantic_b1_crt_occurrence_indexed_columns_def)
  have empty:
    "comma_crt_set ?column \<inter> comma_crt_set ?column = {}"
  proof -
    let ?indexed_columns =
      "comma_semantic_b1_crt_occurrence_indexed_columns
        [?column, Comma_CRT_Node 0
          [Comma_CRT_Bool False, Comma_CRT_Bool True,
           Comma_CRT_Bool False, Comma_CRT_Bool False], ?column]"
    have pairwise:
      "\<forall>left\<in>set ?indexed_columns. \<forall>right\<in>set ?indexed_columns.
        fst left \<noteq> fst right \<longrightarrow>
        comma_crt_set (snd left) \<inter> comma_crt_set (snd right) = {}"
      using disjoint by (simp add: comma_semantic_b1_crt_occurrence_disjoint_def)
    have left_pair:
      "\<forall>right\<in>set ?indexed_columns.
        fst (0, ?column) \<noteq> fst right \<longrightarrow>
        comma_crt_set ?column \<inter> comma_crt_set (snd right) = {}"
      using bspec[OF pairwise indexed_zero] by simp
    have pair:
      "fst ((0::nat), ?column) \<noteq> fst (2, ?column) \<longrightarrow>
        comma_crt_set ?column \<inter> comma_crt_set ?column = {}"
      using bspec[OF left_pair indexed_two] by simp
    have different: "fst ((0::nat), ?column) \<noteq> fst (2, ?column)" by simp
    show ?thesis using pair different by blast
  qed
  show False using empty zero by auto
qed

lemma comma_semantic_b1_crt_occurrence_wellformed_rejects_missing_coverage:
  "\<not> comma_semantic_b1_crt_occurrence_wellformed
    \<lparr>comma_semantic_b1_crt_occurrence_columns=
      [Comma_CRT_Node 0
        [Comma_CRT_Bool True, Comma_CRT_Bool False,
         Comma_CRT_Bool False, Comma_CRT_Bool False]],
      comma_semantic_b1_crt_occurrence_rebase=0,
      comma_semantic_b1_crt_occurrence_beta=[Comma_Semantic_B1_Invalid]\<rparr>"
proof (rule notI)
  let ?column = "Comma_CRT_Node 0
    [Comma_CRT_Bool True, Comma_CRT_Bool False,
     Comma_CRT_Bool False, Comma_CRT_Bool False]"
  have absent: "1 \<notin> comma_crt_set ?column"
    by (simp add: comma_crt_set_def comma_crt_period_def)
  assume wellformed:
    "comma_semantic_b1_crt_occurrence_wellformed
      \<lparr>comma_semantic_b1_crt_occurrence_columns=[?column],
        comma_semantic_b1_crt_occurrence_rebase=0,
        comma_semantic_b1_crt_occurrence_beta=[Comma_Semantic_B1_Invalid]\<rparr>"
  have covered: "comma_semantic_b1_crt_occurrence_covered [?column]"
    using wellformed
    by (simp add: comma_semantic_b1_crt_occurrence_wellformed_def)
  have one: "(1::nat) < 924" by simp
  have "\<exists>entry\<in>set
      (comma_semantic_b1_crt_occurrence_indexed_columns [?column]).
      1 \<in> comma_crt_set (snd entry)"
    using covered one by (auto simp: comma_semantic_b1_crt_occurrence_covered_def)
  then show False using absent
    by (auto simp: comma_semantic_b1_crt_occurrence_indexed_columns_def)
qed

lemma comma_semantic_b1_crt_occurrence_wellformed_rejects_bad_column:
  "\<not> comma_semantic_b1_crt_occurrence_wellformed
    \<lparr>comma_semantic_b1_crt_occurrence_columns=[Comma_CRT_Node 0 []],
      comma_semantic_b1_crt_occurrence_rebase=0,
      comma_semantic_b1_crt_occurrence_beta=[Comma_Semantic_B1_Invalid]\<rparr>"
  by (simp add: comma_semantic_b1_crt_occurrence_wellformed_def)


definition comma_semantic_b1_crt_occurrence_binding_check ::
    "comma_semantic_b1_crt_occurrence \<Rightarrow> bool" where
  "comma_semantic_b1_crt_occurrence_binding_check occurrence \<longleftrightarrow>
    comma_semantic_b1_crt_occurrence_rebase occurrence < 924 \<and>
    length (comma_semantic_b1_crt_occurrence_columns occurrence) =
      length (comma_semantic_b1_crt_occurrence_beta occurrence) \<and>
    comma_semantic_b1_crt_occurrence_columns occurrence \<noteq> []"

lemma comma_semantic_b1_crt_occurrence_find_index_total:
  assumes phase: "phase < 924"
    and covered:
      "comma_semantic_b1_crt_occurrence_covered columns"
  shows "\<exists>index<length columns.
    comma_semantic_b1_crt_occurrence_find_index phase columns = Some index"
proof -
  let ?entries = "comma_semantic_b1_crt_occurrence_indexed_columns columns"
  let ?matches = "\<lambda>entry. comma_crt_eval phase (snd entry)"
  have covered_entry:
      "\<exists>entry\<in>set ?entries. ?matches entry"
    using covered phase
    by (auto simp: comma_semantic_b1_crt_occurrence_covered_def
      comma_crt_set_def)
  have found: "List.find ?matches ?entries \<noteq> None"
    using covered_entry unfolding find_None_iff by blast
  then obtain entry where found_entry:
      "List.find ?matches ?entries = Some entry"
    by (cases "List.find ?matches ?entries") auto
  have selected:
      "\<exists>n<length ?entries. ?matches (?entries ! n) \<and>
        entry = ?entries ! n"
    using find_Some_iff[of ?matches ?entries entry] found_entry by blast
  then have entry_member: "entry \<in> set ?entries"
    by (auto dest: nth_mem)
  have entry_member_zip:
      "entry\<in>set (zip [0..<length columns] columns)"
    using entry_member
    by (simp add: comma_semantic_b1_crt_occurrence_indexed_columns_def)
  obtain index column where entry_pair: "entry=(index,column)"
    by (cases entry) auto
  have index_member: "index\<in>set [0..<length columns]"
    using entry_member_zip entry_pair
    by (auto dest: set_zip_leftD)
  have index_bound: "index < length columns"
    using index_member by simp
  show ?thesis
    using found_entry entry_pair index_bound
    by (auto simp: comma_semantic_b1_crt_occurrence_find_index_def
      comma_semantic_b1_crt_occurrence_indexed_columns_def)
qed

lemma comma_semantic_b1_crt_occurrence_lookup_total:
  assumes wellformed:
      "comma_semantic_b1_crt_occurrence_wellformed occurrence"
  shows "\<exists>result. comma_semantic_b1_crt_occurrence_lookup occurrence clock =
    Some result"
proof -
  let ?columns = "comma_semantic_b1_crt_occurrence_columns occurrence"
  let ?beta = "comma_semantic_b1_crt_occurrence_beta occurrence"
  let ?phase =
    "(clock + comma_semantic_b1_crt_occurrence_rebase occurrence) mod 924"
  have phase: "?phase<924" by simp
  have covered: "comma_semantic_b1_crt_occurrence_covered ?columns"
    using wellformed by (simp add: comma_semantic_b1_crt_occurrence_wellformed_def)
  obtain index where index_bound: "index<length ?columns"
    and found: "comma_semantic_b1_crt_occurrence_find_index ?phase ?columns =
      Some index"
    using comma_semantic_b1_crt_occurrence_find_index_total[OF phase covered]
    by blast
  have width: "length ?columns=length ?beta"
    using wellformed by (simp add: comma_semantic_b1_crt_occurrence_wellformed_def)
  have beta_bound: "index<length ?beta" using index_bound width by simp
  show ?thesis
    using found beta_bound
    by (auto simp: comma_semantic_b1_crt_occurrence_lookup_def)
qed

definition comma_semantic_b1_crt_occurrence_exact ::
    "comma_finite_position \<Rightarrow> comma_semantic_b1_crt_occurrence \<Rightarrow> bool" where
  "comma_semantic_b1_crt_occurrence_exact source occurrence \<longleftrightarrow>
    comma_semantic_b1_crt_occurrence_wellformed occurrence \<and>
    (\<forall>clock<924. comma_semantic_b1_crt_occurrence_lookup occurrence clock =
      Some (comma_semantic_b1_round_output clock source))"

definition comma_semantic_b1_crt_occurrence_local_step ::
    "(comma_finite_position \<Rightarrow> comma_semantic_b1_crt_occurrence option) \<Rightarrow>
      comma_finite_position \<Rightarrow> nat \<Rightarrow>
      comma_semantic_b1_result option" where
  "comma_semantic_b1_crt_occurrence_local_step children source clock =
    (if clock < 924 then
       (case comma_semantic_b1_source_slot_action source
          (clock mod comma_decisive_sector_period source) of
          Comma_Continuation_Goto child shift \<Rightarrow>
            (case children child of None \<Rightarrow> None
             | Some occurrence \<Rightarrow>
                 comma_semantic_b1_crt_occurrence_lookup occurrence
                   ((clock+shift) mod 924))
        | action \<Rightarrow> comma_semantic_b1_terminal_action_result action)
     else None)"

definition comma_semantic_b1_crt_occurrence_candidate_matches ::
    "(comma_finite_position \<Rightarrow> comma_semantic_b1_crt_occurrence option) \<Rightarrow>
      comma_finite_position \<Rightarrow> comma_semantic_b1_crt_occurrence \<Rightarrow> bool" where
  "comma_semantic_b1_crt_occurrence_candidate_matches children source occurrence
    \<longleftrightarrow> (\<forall>clock<924.
      comma_semantic_b1_crt_occurrence_lookup occurrence clock =
        comma_semantic_b1_crt_occurrence_local_step children source clock)"

lemma comma_semantic_b1_crt_occurrence_local_step_exact:
  assumes normalized: "source=comma_source_continuation_base source"
    and admitted: "comma_round_admitted source"
    and phase: "clock<924"
    and child_present:
      "\<And>slot child shift.
        slot<comma_decisive_sector_period source \<Longrightarrow>
        comma_semantic_b1_source_slot_action source slot=
          Comma_Continuation_Goto child shift \<Longrightarrow>
        \<exists>occurrence. children child=Some occurrence"
    and child_exact:
      "\<And>slot child shift occurrence.
        slot<comma_decisive_sector_period source \<Longrightarrow>
        comma_semantic_b1_source_slot_action source slot=
          Comma_Continuation_Goto child shift \<Longrightarrow>
        children child=Some occurrence \<Longrightarrow>
        comma_semantic_b1_crt_occurrence_exact child occurrence"
  shows "comma_semantic_b1_crt_occurrence_local_step children source clock =
    Some (comma_semantic_b1_round_output clock source)"
proof -
  have period_positive:
      "0<comma_decisive_sector_period source"
    by (rule comma_decisive_sector_period_admitted(1)[OF admitted])
  let ?slot = "clock mod comma_decisive_sector_period source"
  let ?action = "comma_semantic_b1_source_slot_action source ?slot"
  have slot_bound: "?slot<comma_decisive_sector_period source"
    using period_positive by simp
  have phase_selected:
      "clock mod comma_decisive_sector_period source=?slot"
    by simp
  have slot_output:
      "comma_semantic_b1_source_slot_output clock ?action =
        comma_semantic_b1_round_output clock source"
    by (rule comma_semantic_b1_source_slot_round_output
      [OF normalized admitted slot_bound phase phase_selected])
  have action_shape: "comma_semantic_b1_local_action_shape ?action"
    by (rule comma_semantic_b1_source_slot_action_shape[OF admitted normalized])
  have local_case:
      "comma_semantic_b1_crt_occurrence_local_step children source clock =
        (case ?action of
           Comma_Continuation_Goto child shift \<Rightarrow>
             (case children child of None \<Rightarrow> None
              | Some occurrence \<Rightarrow>
                  comma_semantic_b1_crt_occurrence_lookup occurrence
                    ((clock+shift) mod 924))
         | action \<Rightarrow> comma_semantic_b1_terminal_action_result action)"
    using phase by (simp add: comma_semantic_b1_crt_occurrence_local_step_def)
  show ?thesis
  proof (cases "\<exists>child shift. ?action=Comma_Continuation_Goto child shift")
    case True
    then obtain child shift where goto:
        "?action=Comma_Continuation_Goto child shift" by blast
    have shift_zero: "shift=0"
      using action_shape goto
      by (simp add: comma_semantic_b1_local_action_shape.simps)
    obtain occurrence where child_lookup:
        "children child=Some occurrence"
      using child_present[OF slot_bound goto] by blast
    have child_is_exact:
        "comma_semantic_b1_crt_occurrence_exact child occurrence"
      by (rule child_exact[OF slot_bound goto child_lookup])
    have child_output:
        "comma_semantic_b1_crt_occurrence_lookup occurrence clock =
          Some (comma_semantic_b1_round_output clock child)"
      using child_is_exact phase
      by (auto simp: comma_semantic_b1_crt_occurrence_exact_def)
    have child_clock: "(clock+shift) mod 924=clock"
      using phase shift_zero by simp
    have child_value:
        "comma_semantic_b1_crt_occurrence_lookup occurrence
          ((clock+shift) mod 924) =
          Some (comma_semantic_b1_round_output clock child)"
      using child_output child_clock by simp
    show ?thesis
      using local_case goto child_lookup child_value slot_output
      by (simp add: comma_semantic_b1_source_slot_output_def)
  next
    case False
    obtain result_label where terminal:
        "comma_semantic_b1_terminal_action_result ?action=Some result_label"
      using comma_semantic_b1_terminal_action_result_present[OF False] by blast
    have slot_value:
        "comma_semantic_b1_source_slot_output clock ?action=result_label"
      by (rule comma_semantic_b1_terminal_action_output[OF terminal])
    show ?thesis using local_case False terminal slot_output slot_value
      by (cases ?action) auto
  qed
qed

theorem comma_semantic_b1_crt_occurrence_candidate_exact:
  assumes normalized: "source=comma_source_continuation_base source"
    and admitted: "comma_round_admitted source"
    and wellformed:
      "comma_semantic_b1_crt_occurrence_wellformed occurrence"
    and candidate:
      "comma_semantic_b1_crt_occurrence_candidate_matches
        children source occurrence"
    and child_present:
      "\<And>slot child shift.
        slot<comma_decisive_sector_period source \<Longrightarrow>
        comma_semantic_b1_source_slot_action source slot=
          Comma_Continuation_Goto child shift \<Longrightarrow>
        \<exists>child_occurrence. children child=Some child_occurrence"
    and child_exact:
      "\<And>slot child shift child_occurrence.
        slot<comma_decisive_sector_period source \<Longrightarrow>
        comma_semantic_b1_source_slot_action source slot=
          Comma_Continuation_Goto child shift \<Longrightarrow>
        children child=Some child_occurrence \<Longrightarrow>
        comma_semantic_b1_crt_occurrence_exact child child_occurrence"
  shows "comma_semantic_b1_crt_occurrence_exact source occurrence"
proof -
  show ?thesis
    unfolding comma_semantic_b1_crt_occurrence_exact_def
  proof (intro conjI)
    show "comma_semantic_b1_crt_occurrence_wellformed occurrence"
      by (rule wellformed)
  next
    show "\<forall>clock<924. comma_semantic_b1_crt_occurrence_lookup occurrence clock =
        Some (comma_semantic_b1_round_output clock source)"
    proof (intro allI impI)
    fix clock :: nat
    assume clock: "clock<924"
    have matches:
        "comma_semantic_b1_crt_occurrence_lookup occurrence clock =
          comma_semantic_b1_crt_occurrence_local_step children source clock"
      using candidate clock
      by (simp add: comma_semantic_b1_crt_occurrence_candidate_matches_def)
    have local_exact:
        "comma_semantic_b1_crt_occurrence_local_step children source clock =
          Some (comma_semantic_b1_round_output clock source)"
      by (rule comma_semantic_b1_crt_occurrence_local_step_exact
        [OF normalized admitted clock child_present child_exact])
    show "comma_semantic_b1_crt_occurrence_lookup occurrence clock =
        Some (comma_semantic_b1_round_output clock source)"
      by (rule trans[OF matches local_exact])
    qed
  qed
qed

lemma comma_semantic_b1_crt_occurrence_goto_decreases:
  assumes normalized: "source=comma_source_continuation_base source"
    and admitted: "comma_round_admitted source"
    and slot: "slot<comma_decisive_sector_period source"
    and action:
      "comma_semantic_b1_source_slot_action source slot=
        Comma_Continuation_Goto child shift"
  shows "shift=0 \<and> child=comma_source_continuation_base child \<and>
    comma_round_admitted child \<and>
    9-comma_sector_number child < 9-comma_sector_number source"
proof -
  have base_eq: "comma_source_continuation_base source=source"
    by (rule sym[OF normalized])
  have action_packet:
      "comma_source_continuation_action_of_packet
        (comma_decisive_endpoint_packet slot source) =
        Comma_Continuation_Goto child shift"
    using action base_eq
    by (simp only: comma_semantic_b1_source_slot_action_def base_eq)
  have decrease:
      "comma_round_admitted child \<and>
        9-comma_sector_number child < 9-comma_sector_number source"
    by (rule comma_source_continuation_goto_decreases[OF admitted action_packet])
  have shape:
      "comma_semantic_b1_local_action_shape
        (comma_semantic_b1_source_slot_action source slot)"
    by (rule comma_semantic_b1_source_slot_action_shape[OF admitted normalized])
  have shift: "shift=0"
    using shape action by (simp add: comma_semantic_b1_local_action_shape.simps)
  obtain target move where packet:
      "comma_decisive_endpoint_packet slot source=(target,move)"
    by (cases "comma_decisive_endpoint_packet slot source") auto
  have selected_packet:
      "comma_source_continuation_action_of_packet (target,move) =
        Comma_Continuation_Goto child shift"
    using action_packet packet by simp
  have normalized_child:
      "child=comma_source_continuation_base child"
    using selected_packet
    by (cases move) (auto split: if_splits)
  show ?thesis using shift normalized_child decrease by blast
qed


text \<open>
One induction discharges the exact-child premises for the whole published
occurrence map.  Physical source addresses select occurrences only; the
proof never constructs a return table at those addresses.  The local
candidate and closure premises are checked separately by the publisher.
\<close>

theorem comma_semantic_b1_crt_occurrence_map_exact:
  assumes local_valid:
    "\<And>source occurrence.
      source=comma_source_continuation_base source \<Longrightarrow>
      comma_round_admitted source \<Longrightarrow>
      published source=Some occurrence \<Longrightarrow>
      comma_semantic_b1_crt_occurrence_wellformed occurrence \<and>
      comma_semantic_b1_crt_occurrence_candidate_matches published source occurrence"
    and closed:
    "\<And>source occurrence slot child shift.
      source=comma_source_continuation_base source \<Longrightarrow>
      comma_round_admitted source \<Longrightarrow>
      published source=Some occurrence \<Longrightarrow>
      slot<comma_decisive_sector_period source \<Longrightarrow>
      comma_semantic_b1_source_slot_action source slot=
        Comma_Continuation_Goto child shift \<Longrightarrow>
      \<exists>child_occurrence. published child=Some child_occurrence"
    and normalized: "source=comma_source_continuation_base source"
    and admitted: "comma_round_admitted source"
    and present: "published source=Some occurrence"
  shows "comma_semantic_b1_crt_occurrence_exact source occurrence"
  using normalized admitted present
proof (induction "9-comma_sector_number source" arbitrary: source occurrence
    rule: less_induct)
  case less
  have local:
    "comma_semantic_b1_crt_occurrence_wellformed occurrence \<and>
      comma_semantic_b1_crt_occurrence_candidate_matches published source occurrence"
    by (rule local_valid[OF less.prems])
  have child_present:
    "\<And>slot child shift.
      slot<comma_decisive_sector_period source \<Longrightarrow>
      comma_semantic_b1_source_slot_action source slot=
        Comma_Continuation_Goto child shift \<Longrightarrow>
      \<exists>child_occurrence. published child=Some child_occurrence"
    by (rule closed[OF less.prems])
  have child_exact:
    "\<And>slot child shift child_occurrence.
      slot<comma_decisive_sector_period source \<Longrightarrow>
      comma_semantic_b1_source_slot_action source slot=
        Comma_Continuation_Goto child shift \<Longrightarrow>
      published child=Some child_occurrence \<Longrightarrow>
      comma_semantic_b1_crt_occurrence_exact child child_occurrence"
  proof -
    fix slot child shift child_occurrence
    assume slot: "slot<comma_decisive_sector_period source"
      and action: "comma_semantic_b1_source_slot_action source slot=
        Comma_Continuation_Goto child shift"
      and lookup: "published child=Some child_occurrence"
    have child_facts:
      "shift=0 \<and> child=comma_source_continuation_base child \<and>
        comma_round_admitted child \<and>
        9-comma_sector_number child < 9-comma_sector_number source"
      by (rule comma_semantic_b1_crt_occurrence_goto_decreases
        [OF less.prems(1,2) slot action])
    have child_normalized: "child=comma_source_continuation_base child"
      and child_admitted: "comma_round_admitted child"
      and decrease: "9-comma_sector_number child < 9-comma_sector_number source"
      using child_facts by blast+
    show "comma_semantic_b1_crt_occurrence_exact child child_occurrence"
      by (rule less.hyps[OF decrease child_normalized child_admitted lookup])
  qed
  show ?case
    by (rule comma_semantic_b1_crt_occurrence_candidate_exact
      [OF less.prems(1,2) conjunct1[OF local] conjunct2[OF local]
        child_present child_exact])
qed

lemma comma_semantic_b1_crt_occurrence_find_index_entry:
  assumes found:
    "comma_semantic_b1_crt_occurrence_find_index phase columns = Some index"
  shows "index < length columns \<and>
    comma_crt_eval phase (columns ! index)"
proof -
  let ?entries = "comma_semantic_b1_crt_occurrence_indexed_columns columns"
  let ?matches = "(\<lambda>entry. comma_crt_eval phase (snd entry))"
  have selected:
    "\<exists>entry. List.find ?matches ?entries = Some entry \<and> fst entry=index"
    using found
    by (auto simp: comma_semantic_b1_crt_occurrence_find_index_def
      split: option.splits)
  then obtain entry where entry:
    "List.find ?matches ?entries = Some entry" "fst entry=index"
    by blast
  have witness:
    "\<exists>n<length ?entries. ?matches (?entries ! n) \<and> entry=?entries ! n"
    using find_Some_iff[of ?matches ?entries entry] entry(1) by blast
  then obtain n where n_bound: "n<length ?entries"
    and n_matches: "?matches (?entries ! n)"
    and entry_n: "entry=?entries ! n" by blast
  have n_columns: "n<length columns"
    using n_bound by (simp add: comma_semantic_b1_crt_occurrence_indexed_columns_def)
  have index_eq: "index=n"
    using entry(2) entry_n n_bound
    by (simp add: comma_semantic_b1_crt_occurrence_indexed_columns_def)
  show ?thesis
    using n_columns n_matches index_eq n_bound
    by (simp add: comma_semantic_b1_crt_occurrence_indexed_columns_def)
qed


ML \<open>
val _ =
  if null (Thm_Deps.all_oracles @{thms
    comma_semantic_b1_crt_resolve_descriptor_exact
    comma_semantic_b1_crt_resolve_descriptor_rejects_foreign
    comma_semantic_b1_crt_occurrence_wellformed_rejects_empty
    comma_semantic_b1_crt_occurrence_wellformed_rejects_overlap
    comma_semantic_b1_crt_occurrence_wellformed_rejects_missing_coverage
    comma_semantic_b1_crt_occurrence_wellformed_rejects_bad_column
    comma_semantic_b1_crt_occurrence_find_index_total
    comma_semantic_b1_crt_occurrence_lookup_total
    comma_semantic_b1_crt_occurrence_local_step_exact
    comma_semantic_b1_crt_occurrence_candidate_exact
    comma_semantic_b1_crt_occurrence_goto_decreases
    comma_semantic_b1_crt_occurrence_map_exact
    comma_semantic_b1_crt_occurrence_find_index_entry
  }) then ()
  else error "Comma_Semantic_B1_CRT_Occurrence_Fold local oracle audit failed"
\<close>
end
