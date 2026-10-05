theory Comma_Semantic_B1_Occurrence_Rows
  imports Comma_Semantic_B1_Occurrence_Publication
begin

text \<open>
An admitted occurrence owns canonical geometry, a clock rebase, and its
exact output binding.  This adapter exposes the completed return rows used by
the B32 composer.  It performs no source recurrence and does not regroup the
published rows; distinct output bindings certify that grouping is already
the identity at a root.
\<close>

definition comma_semantic_b1_crt_occurrence_rows ::
    "comma_semantic_b1_crt_occurrence \<Rightarrow> comma_crt_return_row list" where
  "comma_semantic_b1_crt_occurrence_rows occurrence =
    comma_crt_shift_return_rows
      (comma_semantic_b1_crt_occurrence_rebase occurrence)
      (zip (comma_semantic_b1_crt_occurrence_columns occurrence)
        (comma_semantic_b1_crt_occurrence_beta occurrence))"

lemma comma_semantic_b1_crt_occurrence_rows_admitted:
  assumes wellformed: "comma_semantic_b1_crt_occurrence_wellformed occurrence"
  shows "comma_crt_rows_admitted
    (comma_semantic_b1_crt_occurrence_rows occurrence)"
proof -
  have raw:
    "comma_crt_rows_admitted
      (zip (comma_semantic_b1_crt_occurrence_columns occurrence)
        (comma_semantic_b1_crt_occurrence_beta occurrence))"
    using wellformed
    by (auto simp: comma_crt_rows_admitted_def
      comma_semantic_b1_crt_occurrence_wellformed_def
      list_all_iff in_set_zip)
  show ?thesis
    unfolding comma_semantic_b1_crt_occurrence_rows_def
    by (rule comma_crt_shift_return_rows_admitted[OF raw])
qed

lemma comma_semantic_b1_crt_occurrence_find_index_column:
  assumes wellformed: "comma_semantic_b1_crt_occurrence_wellformed occurrence"
    and phase: "phase<924"
    and index: "index < length (comma_semantic_b1_crt_occurrence_columns occurrence)"
    and evaluates:
      "comma_crt_eval phase (comma_semantic_b1_crt_occurrence_columns occurrence ! index)"
  shows "comma_semantic_b1_crt_occurrence_find_index phase
      (comma_semantic_b1_crt_occurrence_columns occurrence) = Some index"
proof -
  let ?columns = "comma_semantic_b1_crt_occurrence_columns occurrence"
  have covered: "comma_semantic_b1_crt_occurrence_covered ?columns"
    using wellformed
    by (simp add: comma_semantic_b1_crt_occurrence_wellformed_def)
  obtain selected where selected_bound: "selected<length ?columns"
    and found:
      "comma_semantic_b1_crt_occurrence_find_index phase ?columns = Some selected"
    using comma_semantic_b1_crt_occurrence_find_index_total[OF phase covered]
    by blast
  have selected_eval:
      "comma_crt_eval phase (?columns ! selected)"
    using comma_semantic_b1_crt_occurrence_find_index_entry[OF found] by blast
  have indexed_length:
      "length (comma_semantic_b1_crt_occurrence_indexed_columns ?columns) =
        length ?columns"
    by (simp add: comma_semantic_b1_crt_occurrence_indexed_columns_def)
  have indexed_nth:
      "comma_semantic_b1_crt_occurrence_indexed_columns ?columns ! index =
        (index, ?columns ! index)"
    using index by (simp add: comma_semantic_b1_crt_occurrence_indexed_columns_def
      nth_zip)
  have selected_indexed_nth:
      "comma_semantic_b1_crt_occurrence_indexed_columns ?columns ! selected =
        (selected, ?columns ! selected)"
    using selected_bound
    by (simp add: comma_semantic_b1_crt_occurrence_indexed_columns_def nth_zip)
  have indexed_member:
      "(index, ?columns ! index) \<in>
        set (comma_semantic_b1_crt_occurrence_indexed_columns ?columns)"
  proof -
    have bound: "index < length
        (comma_semantic_b1_crt_occurrence_indexed_columns ?columns)"
      using index indexed_length by simp
    show ?thesis
      using nth_mem[OF bound] indexed_nth by simp
  qed
  have selected_member:
      "(selected, ?columns ! selected) \<in>
        set (comma_semantic_b1_crt_occurrence_indexed_columns ?columns)"
  proof -
    have bound: "selected < length
        (comma_semantic_b1_crt_occurrence_indexed_columns ?columns)"
      using selected_bound indexed_length by simp
    show ?thesis
      using nth_mem[OF bound] selected_indexed_nth by simp
  qed
  have disjoint:
      "comma_crt_set (?columns ! index) \<inter>
        comma_crt_set (?columns ! selected) = {}"
    if "index \<noteq> selected"
  proof -
    have indexed_disjoint:
      "comma_semantic_b1_crt_occurrence_disjoint ?columns"
      using wellformed
      by (simp add: comma_semantic_b1_crt_occurrence_wellformed_def)
    show ?thesis
      using indexed_disjoint indexed_member selected_member that
      by (auto simp: comma_semantic_b1_crt_occurrence_disjoint_def)
  qed
  have phase_in_left:
      "phase \<in> comma_crt_set (?columns ! index)"
    using phase evaluates by (auto simp: comma_crt_set_def)
  have phase_in_right:
      "phase \<in> comma_crt_set (?columns ! selected)"
    using phase selected_eval by (auto simp: comma_crt_set_def)
  have same_index: "selected=index"
  proof (rule ccontr)
    assume "selected \<noteq> index"
    have "phase \<in> comma_crt_set (?columns ! index) \<inter>
        comma_crt_set (?columns ! selected)"
      using phase_in_left phase_in_right by simp
    with disjoint[of index selected] `selected \<noteq> index` show False by blast
  qed
  show ?thesis using found same_index by simp
qed

lemma comma_semantic_b1_crt_occurrence_lookup_selected_index:
  assumes lookup:
    "comma_semantic_b1_crt_occurrence_lookup occurrence clock = Some result"
  obtains index where
    "comma_semantic_b1_crt_occurrence_find_index
       ((clock + comma_semantic_b1_crt_occurrence_rebase occurrence) mod 924)
       (comma_semantic_b1_crt_occurrence_columns occurrence) = Some index"
    "index < length (comma_semantic_b1_crt_occurrence_beta occurrence)"
    "comma_semantic_b1_crt_occurrence_beta occurrence ! index = result"
  using lookup
  by (auto simp: comma_semantic_b1_crt_occurrence_lookup_def
      split: option.splits if_splits)

lemma comma_semantic_b1_crt_distinct_nth_injective:
  assumes distinct: "distinct values"
    and left: "i<length values"
    and right: "j<length values"
    and equal: "values!i=values!j"
  shows "i=j"
  using distinct left right equal
  by (auto simp: distinct_conv_nth; metis less_linear)

lemma comma_semantic_b1_crt_occurrence_raw_column_fiber:
  assumes wellformed: "comma_semantic_b1_crt_occurrence_wellformed occurrence"
    and exact: "comma_semantic_b1_crt_occurrence_exact source occurrence"
    and labels: "distinct (comma_semantic_b1_crt_occurrence_beta occurrence)"
    and index: "index < length (comma_semantic_b1_crt_occurrence_columns occurrence)"
  shows "comma_crt_set (comma_semantic_b1_crt_occurrence_columns occurrence ! index) =
    {phase. phase<924 \<and>
      comma_semantic_b1_round_output
        ((phase + comma_semantic_b1_inverse_shift
          (comma_semantic_b1_crt_occurrence_rebase occurrence)) mod 924)
        source =
        comma_semantic_b1_crt_occurrence_beta occurrence ! index}"
proof -
  let ?columns = "comma_semantic_b1_crt_occurrence_columns occurrence"
  let ?beta = "comma_semantic_b1_crt_occurrence_beta occurrence"
  let ?rho = "comma_semantic_b1_crt_occurrence_rebase occurrence"
  let ?inverse = "comma_semantic_b1_inverse_shift ?rho"
  let ?action = "\<lambda>phase. comma_semantic_b1_round_output
    ((phase + ?inverse) mod 924) source"
  have wf: "comma_semantic_b1_crt_occurrence_wellformed occurrence"
    using exact by (simp add: comma_semantic_b1_crt_occurrence_exact_def)
  have width: "length ?columns=length ?beta"
    using wf by (simp add: comma_semantic_b1_crt_occurrence_wellformed_def)
  have beta_bound: "index<length ?beta" using index width by simp
  show ?thesis
  proof (rule set_eqI)
    fix phase :: nat
    show "phase \<in> comma_crt_set (?columns ! index) \<longleftrightarrow>
        phase \<in> {phase. phase<924 \<and> ?action phase=?beta!index}"
    proof
      assume member: "phase \<in> comma_crt_set (?columns ! index)"
      have phase: "phase<924" and evaluates: "comma_crt_eval phase (?columns!index)"
        using member by (auto simp: comma_crt_set_def)
      let ?clock = "(phase + ?inverse) mod 924"
      have query: "((?clock + ?rho) mod 924)=phase"
        using phase
        by (simp add: comma_semantic_b1_inverse_shift_cancel_right)
      have selected:
        "comma_semantic_b1_crt_occurrence_find_index
          ((?clock + ?rho) mod 924) ?columns=Some index"
        using comma_semantic_b1_crt_occurrence_find_index_column
          [OF wf _ index evaluates]
        by (rule; simp)
      have lookup:
        "comma_semantic_b1_crt_occurrence_lookup occurrence ?clock=Some (?beta!index)"
        using selected index beta_bound
        by (simp add: comma_semantic_b1_crt_occurrence_lookup_def)
      have exact_action:
        "comma_semantic_b1_crt_occurrence_lookup occurrence ?clock=
          Some (comma_semantic_b1_round_output ?clock source)"
        using exact phase
        by (auto simp: comma_semantic_b1_crt_occurrence_exact_def)
      have "?beta!index=comma_semantic_b1_round_output ?clock source"
        using lookup exact_action by simp
      then show "phase \<in> {phase. phase<924 \<and> ?action phase=?beta!index}"
        using phase by simp
    next
      assume member: "phase \<in> {phase. phase<924 \<and> ?action phase=?beta!index}"
      then have phase: "phase<924"
        and output: "?action phase=?beta!index" by auto
      let ?clock = "(phase + ?inverse) mod 924"
      have query: "((?clock + ?rho) mod 924)=phase"
        using phase
        by (simp add: comma_semantic_b1_inverse_shift_cancel_right)
      have exact_action:
        "comma_semantic_b1_crt_occurrence_lookup occurrence ?clock=
          Some (comma_semantic_b1_round_output ?clock source)"
        using exact by (auto simp: comma_semantic_b1_crt_occurrence_exact_def)
      have output_clock:
        "comma_semantic_b1_round_output ?clock source=?beta!index"
        using output by simp
      have lookup: "comma_semantic_b1_crt_occurrence_lookup occurrence ?clock=
          Some (?beta!index)"
        using exact_action output_clock by simp
      obtain selected where found_clock:
          "comma_semantic_b1_crt_occurrence_find_index
            ((?clock + ?rho) mod 924) ?columns=Some selected"
        and selected_bound: "selected<length ?beta"
        and selected_clock_label: "?beta!selected=
          comma_semantic_b1_round_output ?clock source"
        using comma_semantic_b1_crt_occurrence_lookup_selected_index[OF lookup]
        by blast
      have found: "comma_semantic_b1_crt_occurrence_find_index phase ?columns=Some selected"
        using found_clock query by simp
      have selected_label: "?beta!selected=?beta!index"
        using selected_clock_label output by simp
      have selected_eval:
          "comma_crt_eval phase (?columns!selected)"
        using comma_semantic_b1_crt_occurrence_find_index_entry[OF found]
        by blast
      have same_index: "selected=index"
        by (rule comma_semantic_b1_crt_distinct_nth_injective
          [OF labels selected_bound beta_bound selected_label])
      show "phase \<in> comma_crt_set (?columns ! index)"
        using phase selected_eval same_index by (auto simp: comma_crt_set_def)
    qed
  qed
qed

lemma comma_semantic_b1_crt_occurrence_rows_exact:
  assumes wellformed: "comma_semantic_b1_crt_occurrence_wellformed occurrence"
    and exact: "comma_semantic_b1_crt_occurrence_exact source occurrence"
    and labels: "distinct (comma_semantic_b1_crt_occurrence_beta occurrence)"
  shows "comma_semantic_b1_binding_table_exact
    (\<lambda>phase. comma_semantic_b1_round_output phase source) 0
    (map comma_crt_project_row (comma_semantic_b1_crt_occurrence_rows occurrence))"
proof -
  let ?columns = "comma_semantic_b1_crt_occurrence_columns occurrence"
  let ?beta = "comma_semantic_b1_crt_occurrence_beta occurrence"
  let ?rho = "comma_semantic_b1_crt_occurrence_rebase occurrence"
  let ?inverse = "comma_semantic_b1_inverse_shift ?rho"
  let ?action = "\<lambda>phase. comma_semantic_b1_round_output
    ((phase + ?inverse) mod 924) source"
  let ?raw = "zip ?columns ?beta"
  let ?shifted = "comma_semantic_b1_crt_occurrence_rows occurrence"
  have wf: "comma_semantic_b1_crt_occurrence_wellformed occurrence"
    using exact by (simp add: comma_semantic_b1_crt_occurrence_exact_def)
  have width: "length ?columns=length ?beta"
    using wf by (simp add: comma_semantic_b1_crt_occurrence_wellformed_def)
  have raw_admitted: "comma_crt_rows_admitted ?raw"
    using wf by (auto simp: comma_crt_rows_admitted_def
      comma_semantic_b1_crt_occurrence_wellformed_def list_all_iff in_set_zip)
  have raw_labels: "distinct (map snd ?raw)"
    using labels width by (simp add: length_zip)
  have raw_supported: "list_all (\<lambda>row. comma_crt_supported (fst row)) ?raw"
    using wf width
    by (auto simp: list_all_iff comma_semantic_b1_crt_occurrence_wellformed_def
      in_set_zip)
  have raw_supported_set:
    "\<forall>row\<in>set ?raw. comma_crt_supported (fst row)"
    using raw_supported by (auto simp: list_all_iff)
  have row_cover:
    "phase<924 \<Longrightarrow> \<exists>row\<in>set ?raw.
       phase\<in>comma_crt_set (fst row) \<and> snd row=?action phase"
    for phase
  proof -
    assume phase: "phase<924"
    let ?clock = "(phase + ?inverse) mod 924"
    have selected_query:
      "((?clock + ?rho) mod 924)=phase"
      using phase by (simp add: comma_semantic_b1_inverse_shift_cancel_right)
    have exact_action:
      "comma_semantic_b1_crt_occurrence_lookup occurrence ?clock=
        Some (comma_semantic_b1_round_output ?clock source)"
      using exact by (auto simp: comma_semantic_b1_crt_occurrence_exact_def)
    have output_action: "comma_semantic_b1_round_output ?clock source=?action phase"
      by simp
    obtain index where found_clock:
      "comma_semantic_b1_crt_occurrence_find_index
        ((?clock + ?rho) mod 924) ?columns=Some index"
      and bound: "index<length ?beta"
      and clock_label: "?beta!index=
        comma_semantic_b1_round_output ?clock source"
      using comma_semantic_b1_crt_occurrence_lookup_selected_index[OF exact_action]
      by blast
    have found:
      "comma_semantic_b1_crt_occurrence_find_index phase ?columns=Some index"
      using found_clock selected_query by simp
    have label: "?beta!index=?action phase"
      using clock_label output_action by simp
    have column_bound: "index<length ?columns" using bound width by simp
    have evaluates: "comma_crt_eval phase (?columns!index)"
      using comma_semantic_b1_crt_occurrence_find_index_entry[OF found]
      by blast
    have raw_member: "(?columns!index,?beta!index)\<in>set ?raw"
      using column_bound width by (auto simp: in_set_conv_nth nth_zip)
    show ?thesis
      using phase evaluates label raw_member by (auto simp: comma_crt_set_def)
  qed
  have exact_rows:
    "\<forall>row\<in>set ?raw. comma_semantic_b1_binding_row_exact ?action 0
      (comma_crt_project_row row)"
  proof (intro ballI)
    fix row
    assume row: "row\<in>set ?raw"
    obtain index where index: "index<length ?columns"
      and row_eq: "row=(?columns!index,?beta!index)"
      using row width by (auto simp: in_set_conv_nth nth_zip)
    have fiber:
      "comma_crt_set (?columns!index) =
        {phase. phase<924 \<and> ?action phase=?beta!index}"
      by (rule comma_semantic_b1_crt_occurrence_raw_column_fiber
        [OF wf exact labels index])
    have nonempty: "comma_crt_set (fst row)\<noteq>{}"
    proof -
      have admitted: "comma_crt_admitted 0 (fst row)"
        using raw_admitted row by (auto simp: comma_crt_rows_admitted_def)
      have supported: "comma_crt_supported (fst row)"
        using raw_supported row by (auto simp: list_all_iff)
      show ?thesis
        using comma_crt_supported_nonempty[OF admitted] supported by blast
    qed
    have projected_fiber:
      "comma_crt_set (fst row) =
        {phase. phase<924 \<and> ?action phase=snd row}"
      using fiber row_eq by simp
    show "comma_semantic_b1_binding_row_exact ?action 0
        (comma_crt_project_row row)"
      unfolding comma_crt_project_row_def
      by (simp only: comma_semantic_b1_binding_row_exact_zero_iff;
          simp add: nonempty projected_fiber)
  qed
  have projected_cover:
    "(\<Union> (fst ` set (map comma_crt_project_row ?raw)))={..<924}"
  proof (rule set_eqI)
    fix phase
    show "phase\<in>(\<Union> (fst ` set (map comma_crt_project_row ?raw)))
        \<longleftrightarrow> phase\<in>{..<924}"
    proof
      assume member:
        "phase\<in>(\<Union> (fst ` set (map comma_crt_project_row ?raw)))"
      then obtain row where row: "row\<in>set ?raw"
        and phase_member: "phase\<in>comma_crt_set (fst row)"
        by (auto simp: comma_crt_project_row_def)
      have "phase<924"
        using phase_member by (auto simp: comma_crt_set_def)
      then show "phase\<in>{..<924}" by simp
    next
      assume phase: "phase\<in>{..<924}"
      then obtain row where row: "row\<in>set ?raw"
        and member: "phase\<in>comma_crt_set (fst row)"
        and label: "snd row=?action phase"
        using row_cover by blast
      show "phase\<in>(\<Union> (fst ` set (map comma_crt_project_row ?raw)))"
        using row member by (auto simp: comma_crt_project_row_def)
    qed
  qed
  have grouped_fibers:
    "comma_crt_set (comma_crt_group_column outcome ?raw) =
      {phase. phase<924 \<and> ?action phase=outcome}"
    for outcome
    by (rule comma_crt_exact_rows_group_column_fiber
      [OF raw_labels exact_rows projected_cover])
  have raw_table:
    "comma_semantic_b1_binding_table_exact ?action 0
      (map comma_crt_project_row ?raw)"
    by (rule comma_crt_exact_table_from_fibers
      [OF raw_admitted raw_supported_set raw_labels grouped_fibers])
  have shifted_table:
    "comma_semantic_b1_binding_table_exact ?action ?rho
      (map comma_crt_project_row ?shifted)"
    unfolding comma_semantic_b1_crt_occurrence_rows_def
    by (rule comma_crt_shift_return_rows_exact[OF raw_admitted raw_table])
  have agreement:
    "?action ((phase+?rho) mod 924)=
      comma_semantic_b1_round_output phase source"
    if "phase<924" for phase
    using comma_semantic_b1_cancel_shift[of phase ?rho] that
    by (simp add: Let_def)
  let ?rebased_action = "\<lambda>phase. ?action ((phase+?rho) mod 924)"
  have rebased_at_zero:
    "comma_semantic_b1_binding_table_exact ?rebased_action 0
      (map comma_crt_project_row ?shifted)"
    using shifted_table
    by (simp add: comma_semantic_b1_binding_table_exact_def
      comma_semantic_b1_binding_row_exact_def Let_def)
  have action_agreement:
    "?rebased_action phase=comma_semantic_b1_round_output phase source"
    if "phase<924" for phase
    using agreement[OF that] by simp
  show ?thesis
    by (rule comma_semantic_b1_binding_table_exact_action_congruent
      [OF rebased_at_zero action_agreement])
qed

end
