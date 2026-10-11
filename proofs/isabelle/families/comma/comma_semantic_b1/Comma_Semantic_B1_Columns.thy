theory Comma_Semantic_B1_Columns
  imports Comma_Semantic_B1_Rebase
begin
ML \<open>Comma_Proof_Profile.report "Semantic B1 columns stage=entered"\<close>

text \<open>
Graph evaluation is recursive executable semantics.  The return-column
proofs reason about a checked graph result through the refinement theorem;
they must not expand that evaluator while normalizing a symbolic partition.
Keep it opaque to the inherited simp set and use explicit evaluation rules
only in constructor-level proofs that need them.
\<close>

declare comma_semantic_b1_graph_eval.simps [simp del]

text \<open>
The return-template observer retains the partition of clock phases into
equal-output columns, rather than the output labels themselves.  The template
is the orbit of that partition under common cyclic clock translation.  A
particular occurrence carries its selected translation and an output binding;
the binding restores the exact Live/Stop/Invalid label after template lookup.
No finite class count or concrete merge is assumed here.
\<close>

type_synonym comma_semantic_b1_column = "nat set"
type_synonym comma_semantic_b1_partition = "comma_semantic_b1_column set"
type_synonym comma_semantic_b1_return_template = "comma_semantic_b1_partition set"

definition comma_semantic_b1_inverse_shift :: "nat \<Rightarrow> nat" where
  "comma_semantic_b1_inverse_shift shift = (924 - shift mod 924) mod 924"

lemma comma_semantic_b1_cancel_shift:
  "(((clock+shift) mod 924 +
      comma_semantic_b1_inverse_shift shift) mod 924) = clock mod 924"
proof -
  let ?q = "shift div 924"
  let ?r = "shift mod 924"
  have remainder_bound: "?r<924" by simp
  have inverse_value:
    "comma_semantic_b1_inverse_shift shift = (924-?r) mod 924"
    by (simp add: comma_semantic_b1_inverse_shift_def)
  have quotient_remainder: "?q*924+?r=shift"
    by (rule div_mult_mod_eq)
  have decomposition: "shift=924*?q+?r"
    using quotient_remainder by (simp add: mult.commute)
  have complement: "shift+(924-?r)=924*(?q+1)"
  proof -
    have "shift+(924-?r)=924*?q+?r+(924-?r)"
      by (rule arg_cong[where f="\<lambda>n. n+(924-?r)", OF decomposition])
    also have "...=924*?q+(?r+(924-?r))"
      by (rule add.assoc)
    also have "...=924*?q+924"
      using remainder_bound by simp
    also have "...=924*(?q+1)"
      by (simp add: distrib_left)
    finally show ?thesis .
  qed
  have phase:
    "(((clock+shift) mod 924+(924-?r)) mod 924)=clock mod 924"
  proof -
    have "(((clock+shift) mod 924+(924-?r)) mod 924) =
        ((clock+shift+(924-?r)) mod 924)"
      by (rule mod_add_left_eq)
    also have "...=((clock+(shift+(924-?r))) mod 924)"
      by (simp add: add.assoc)
    also have "...=((clock+924*(?q+1)) mod 924)"
      using complement by simp
    also have "...=clock mod 924"
    proof -
      have "((clock+924*(?q+1)) mod 924) =
          ((924*(?q+1)+clock) mod 924)"
        by (simp add: add.commute)
      also have "...=((924*(?q+1) mod 924+clock) mod 924)"
        by (rule mod_add_left_eq[symmetric])
      also have "...=clock mod 924" by simp
      finally show ?thesis .
    qed
    finally show ?thesis .
  qed
  show ?thesis
  proof -
    have "(((clock+shift) mod 924+
        comma_semantic_b1_inverse_shift shift) mod 924) =
        (((clock+shift) mod 924+(924-?r)) mod 924)"
      by (simp only: inverse_value mod_add_right_eq)
    also have "...=clock mod 924" by (rule phase)
    finally show ?thesis .
  qed
qed

definition comma_semantic_b1_column_at ::
    "(nat \<Rightarrow> comma_semantic_b1_result) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
      comma_semantic_b1_column" where
  "comma_semantic_b1_column_at action shift phase =
    {q. q<924 \<and>
      action ((q+shift) mod 924) = action ((phase+shift) mod 924)}"

definition comma_semantic_b1_partition_at ::
    "(nat \<Rightarrow> comma_semantic_b1_result) \<Rightarrow> nat \<Rightarrow>
      comma_semantic_b1_partition" where
  "comma_semantic_b1_partition_at action shift =
    {comma_semantic_b1_column_at action shift phase | phase. phase<924}"

definition comma_semantic_b1_template_id ::
    "(nat \<Rightarrow> comma_semantic_b1_result) \<Rightarrow>
      comma_semantic_b1_return_template" where
  "comma_semantic_b1_template_id action =
    {comma_semantic_b1_partition_at action shift | shift. shift<924}"

definition comma_semantic_b1_template_function ::
    "(nat \<Rightarrow> comma_semantic_b1_result) \<Rightarrow> nat \<Rightarrow>
      nat \<Rightarrow> comma_semantic_b1_column" where
  "comma_semantic_b1_template_function action return_shift phase =
    comma_semantic_b1_column_at action
      (comma_semantic_b1_inverse_shift return_shift) phase"

definition comma_semantic_b1_output_binding ::
    "(nat \<Rightarrow> comma_semantic_b1_result) \<Rightarrow> nat \<Rightarrow>
      comma_semantic_b1_column \<Rightarrow> comma_semantic_b1_result" where
  "comma_semantic_b1_output_binding action return_shift column =
    action ((Min column + comma_semantic_b1_inverse_shift return_shift) mod 924)"

type_synonym comma_semantic_b1_binding_row =
  "comma_semantic_b1_column \<times> comma_semantic_b1_result"

definition comma_semantic_b1_binding_lookup ::
    "comma_semantic_b1_binding_row list \<Rightarrow>
      comma_semantic_b1_column \<Rightarrow> comma_semantic_b1_result" where
  "comma_semantic_b1_binding_lookup rows column =
    (THE result. (column,result) \<in> set rows)"

definition comma_semantic_b1_binding_row_exact ::
    "(nat \<Rightarrow> comma_semantic_b1_result) \<Rightarrow> nat \<Rightarrow>
      comma_semantic_b1_binding_row \<Rightarrow> bool" where
  "comma_semantic_b1_binding_row_exact action shift row \<longleftrightarrow>
    fst row \<noteq> {} \<and>
    fst row = {phase. phase<924 \<and>
      action ((phase+shift) mod 924) = snd row}"

lemma comma_semantic_b1_binding_row_exact_zero_iff:
  "comma_semantic_b1_binding_row_exact action 0 row \<longleftrightarrow>
    fst row \<noteq> {} \<and>
    fst row = {phase. phase<924 \<and> action phase=snd row}"
proof -
  have fiber:
    "{phase. phase<924 \<and> action ((phase+0) mod 924)=snd row} =
      {phase. phase<924 \<and> action phase=snd row}"
  proof (rule Collect_cong)
    fix phase :: nat
    show "(phase<924 \<and> action ((phase+0) mod 924)=snd row) =
        (phase<924 \<and> action phase=snd row)"
    proof (cases "phase<924")
      case True
      then show ?thesis by (simp add: mod_less)
    next
      case False
      then show ?thesis by simp
    qed
  qed
  show ?thesis
    unfolding comma_semantic_b1_binding_row_exact_def
    by (simp only: fiber)
qed

definition comma_semantic_b1_binding_table_exact ::
    "(nat \<Rightarrow> comma_semantic_b1_result) \<Rightarrow> nat \<Rightarrow>
      comma_semantic_b1_binding_row list \<Rightarrow> bool" where
  "comma_semantic_b1_binding_table_exact action shift rows \<longleftrightarrow>
    distinct (map fst rows) \<and>
    (\<Union> (fst ` set rows)) = {..<924} \<and>
    (\<forall>row\<in>set rows. comma_semantic_b1_binding_row_exact action shift row) \<and>
    (\<forall>left\<in>set rows. \<forall>right\<in>set rows.
      left\<noteq>right \<longrightarrow> fst left \<inter> fst right = {})"

lemma comma_semantic_b1_binding_table_exact_action_congruent:
  assumes exact:
      "comma_semantic_b1_binding_table_exact action shift rows"
    and agreement: "\<And>phase. phase<924 \<Longrightarrow> action phase=target phase"
  shows "comma_semantic_b1_binding_table_exact target shift rows"
proof -
  have shifted_agreement:
      "action ((phase+shift) mod 924)=target ((phase+shift) mod 924)"
    for phase :: nat
    using agreement[of "(phase+shift) mod 924"] by simp
  have row_equivalence:
      "comma_semantic_b1_binding_row_exact action shift row =
        comma_semantic_b1_binding_row_exact target shift row"
    for row
  proof -
    have columns_equal:
        "{phase. phase<924 \<and> action ((phase+shift) mod 924)=snd row} =
         {phase. phase<924 \<and> target ((phase+shift) mod 924)=snd row}"
    proof (rule set_eqI)
      fix phase :: nat
      show "phase\<in>{phase. phase<924 \<and> action ((phase+shift) mod 924)=snd row} \<longleftrightarrow>
          phase\<in>{phase. phase<924 \<and> target ((phase+shift) mod 924)=snd row}"
        using shifted_agreement[of phase] by simp
    qed
    show ?thesis
      by (simp only: comma_semantic_b1_binding_row_exact_def columns_equal)
  qed
  have table_equivalence:
      "comma_semantic_b1_binding_table_exact action shift rows =
        comma_semantic_b1_binding_table_exact target shift rows"
    unfolding comma_semantic_b1_binding_table_exact_def
    using row_equivalence by auto
  show ?thesis using exact table_equivalence by blast
qed

definition comma_semantic_b1_graph_binding_row_exact ::
    "comma_semantic_b1_node list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
      comma_semantic_b1_binding_row \<Rightarrow> bool" where
  "comma_semantic_b1_graph_binding_row_exact nodes cid shift row \<longleftrightarrow>
    fst row \<noteq> {} \<and>
    fst row = {phase. phase<924 \<and>
      comma_semantic_b1_graph_eval nodes cid ((phase+shift) mod 924) =
        Some (snd row)}"

definition comma_semantic_b1_graph_binding_table_exact ::
    "comma_semantic_b1_node list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
      comma_semantic_b1_binding_row list \<Rightarrow> bool" where
  "comma_semantic_b1_graph_binding_table_exact nodes cid shift rows \<longleftrightarrow>
    distinct (map fst rows) \<and>
    (\<Union> (fst ` set rows)) = {..<924} \<and>
    (\<forall>row\<in>set rows. comma_semantic_b1_graph_binding_row_exact
      nodes cid shift row) \<and>
    (\<forall>left\<in>set rows. \<forall>right\<in>set rows.
      left\<noteq>right \<longrightarrow> fst left \<inter> fst right = {})"

lemma comma_semantic_b1_graph_binding_root_exact:
  assumes graph: "comma_semantic_b1_graph_valid bindings nodes"
    and binding: "binding\<in>set bindings"
    and source:
      "comma_semantic_b1_binding_source binding =
        Comma_Entry 1 0 (comma_offset_representatives!root)"
    and root: "root<46"
  shows "\<forall>clock<924. comma_semantic_b1_graph_eval nodes
      (comma_semantic_b1_binding_cid binding) clock =
    Some (comma_semantic_b1 clock root)"
proof (intro allI impI)
  fix clock :: nat
  assume clock: "clock<924"
  have all_correct: "\<forall>cid. comma_semantic_b1_graph_correct_at bindings nodes cid"
    by (rule comma_semantic_b1_graph_eval_refines_endpoint[OF graph])
  have correct:
    "comma_semantic_b1_graph_correct_at bindings nodes
      (comma_semantic_b1_binding_cid binding)"
    using all_correct by blast
  have correct_all_clocks:
    "\<forall>clock<924. comma_semantic_b1_graph_eval nodes
        (comma_semantic_b1_binding_cid binding) clock =
      Some (comma_semantic_b1_round_output clock
        (comma_semantic_b1_binding_source binding))"
  proof (intro allI impI)
    fix clock :: nat
    assume clock: "clock<924"
    have binding_correct:
      "comma_semantic_b1_graph_eval nodes
          (comma_semantic_b1_binding_cid binding) clock =
        Some (comma_semantic_b1_round_output clock
          (comma_semantic_b1_binding_source binding))"
      using correct binding unfolding comma_semantic_b1_graph_correct_at_def
      by blast
    show "comma_semantic_b1_graph_eval nodes
        (comma_semantic_b1_binding_cid binding) clock =
      Some (comma_semantic_b1_round_output clock
        (comma_semantic_b1_binding_source binding))"
      using binding_correct .
  qed
  have evaluated:
    "comma_semantic_b1_graph_eval nodes
        (comma_semantic_b1_binding_cid binding) clock =
      Some (comma_semantic_b1_round_output clock
        (comma_semantic_b1_binding_source binding))"
    using correct_all_clocks clock by blast
  have output_exact:
    "comma_semantic_b1_round_output clock
        (comma_semantic_b1_binding_source binding) =
      comma_semantic_b1 clock root"
    by (simp only: source comma_semantic_b1_round_output_def
      comma_semantic_b1_def comma_decisive_B1_def clock root
      simp_thms if_True comma_decisive_B1_source_def)
  show "comma_semantic_b1_graph_eval nodes
      (comma_semantic_b1_binding_cid binding) clock =
    Some (comma_semantic_b1 clock root)"
    using evaluated output_exact by simp
qed

lemma comma_semantic_b1_graph_scopes_refine_binding_table:
  assumes graph_table:
      "comma_semantic_b1_graph_binding_table_exact nodes cid shift rows"
    and graph_action:
      "\<forall>clock<924. comma_semantic_b1_graph_eval nodes cid clock =
        Some (action clock)"
  shows "comma_semantic_b1_binding_table_exact action shift rows"
proof -
  have table_definition:
    "comma_semantic_b1_graph_binding_table_exact nodes cid shift rows =
      (distinct (map fst rows) \<and>
      (\<Union> (fst ` set rows))={..<924} \<and>
      (\<forall>row\<in>set rows.
        comma_semantic_b1_graph_binding_row_exact nodes cid shift row) \<and>
      (\<forall>left\<in>set rows. \<forall>right\<in>set rows.
        left\<noteq>right \<longrightarrow> fst left \<inter> fst right = {}))"
    by (simp only: comma_semantic_b1_graph_binding_table_exact_def)
  have table_facts:
    "distinct (map fst rows) \<and>
      (\<Union> (fst ` set rows))={..<924} \<and>
      (\<forall>row\<in>set rows.
        comma_semantic_b1_graph_binding_row_exact nodes cid shift row) \<and>
      (\<forall>left\<in>set rows. \<forall>right\<in>set rows.
        left\<noteq>right \<longrightarrow> fst left \<inter> fst right = {})"
    using graph_table table_definition by blast
  have distinct_keys: "distinct (map fst rows)"
    and covered: "(\<Union> (fst ` set rows))={..<924}"
    and graph_rows:
      "\<forall>row\<in>set rows.
        comma_semantic_b1_graph_binding_row_exact nodes cid shift row"
    and disjoint:
      "\<forall>left\<in>set rows. \<forall>right\<in>set rows.
        left\<noteq>right \<longrightarrow> fst left \<inter> fst right = {}"
    using table_facts by blast+
  have exact_rows:
    "\<forall>row\<in>set rows. comma_semantic_b1_binding_row_exact action shift row"
  proof (intro ballI)
    fix row
    assume row_member: "row\<in>set rows"
    obtain row_key row_value where row_pair: "row=(row_key,row_value)"
      by (cases row) auto
    have graph_row:
      "comma_semantic_b1_graph_binding_row_exact nodes cid shift (row_key,row_value)"
      using graph_rows row_member row_pair by blast
    have graph_row_facts:
      "row_key \<noteq> {}"
      "row_key = {phase. phase<924 \<and>
        comma_semantic_b1_graph_eval nodes cid ((phase+shift) mod 924)=Some row_value}"
      using graph_row
      by (auto simp: comma_semantic_b1_graph_binding_row_exact_def)
    have nonempty: "row_key\<noteq>{}"
      using graph_row_facts(1) .
    have key:
      "row_key={phase. phase<924 \<and>
        comma_semantic_b1_graph_eval nodes cid ((phase+shift) mod 924)=Some row_value}"
      using graph_row_facts(2) .
    have graph_action_shifted:
      "\<And>phase.
        comma_semantic_b1_graph_eval nodes cid ((phase+shift) mod 924) =
          Some (action ((phase+shift) mod 924))"
    proof -
      fix phase :: nat
      have argument_bound: "((phase+shift) mod 924)<924" by simp
      show "comma_semantic_b1_graph_eval nodes cid ((phase+shift) mod 924) =
          Some (action ((phase+shift) mod 924))"
        using graph_action argument_bound by blast
    qed
    have key_action:
      "row_key={phase. phase<924 \<and> action ((phase+shift) mod 924)=row_value}"
      using key
      by (simp only: graph_action_shifted option.inject)
    show "comma_semantic_b1_binding_row_exact action shift row"
      using nonempty key_action row_pair
      by (simp add: comma_semantic_b1_binding_row_exact_def)
  qed
  show ?thesis
    using distinct_keys covered disjoint exact_rows
    by (simp add: comma_semantic_b1_binding_table_exact_def)
qed

corollary comma_semantic_b1_graph_root_scopes_refine_binding_table:
  assumes graph:
      "comma_semantic_b1_graph_valid bindings nodes"
    and binding: "binding\<in>set bindings"
    and source:
      "comma_semantic_b1_binding_source binding =
        Comma_Entry 1 0 (comma_offset_representatives!root)"
    and root: "root<46"
    and graph_table:
      "comma_semantic_b1_graph_binding_table_exact nodes
        (comma_semantic_b1_binding_cid binding)
        (comma_semantic_b1_inverse_shift return_shift) rows"
  shows "comma_semantic_b1_binding_table_exact
      (comma_semantic_b1_id_of_root root)
      (comma_semantic_b1_inverse_shift return_shift) rows"
proof (rule comma_semantic_b1_graph_scopes_refine_binding_table[OF graph_table])
  show "\<forall>clock<924. comma_semantic_b1_graph_eval nodes
      (comma_semantic_b1_binding_cid binding) clock =
    Some (comma_semantic_b1_id_of_root root clock)"
  proof (intro allI impI)
    fix clock :: nat
    assume clock: "clock<924"
    have evaluated:
      "comma_semantic_b1_graph_eval nodes
        (comma_semantic_b1_binding_cid binding) clock =
        Some (comma_semantic_b1 clock root)"
      using comma_semantic_b1_graph_binding_root_exact[OF graph binding source root]
        clock by blast
    show "comma_semantic_b1_graph_eval nodes
        (comma_semantic_b1_binding_cid binding) clock =
      Some (comma_semantic_b1_id_of_root root clock)"
      using evaluated by (simp only: comma_semantic_b1_id_of_root_def mod_less[OF clock])
  qed
qed

lemma comma_semantic_b1_binding_row_exact_phase:
  assumes row: "comma_semantic_b1_binding_row_exact action shift (column,value)"
    and phase: "phase\<in>column"
  shows "action ((phase+shift) mod 924)=value"
  using row phase by (auto simp: comma_semantic_b1_binding_row_exact_def)

lemma comma_semantic_b1_binding_table_lookup_exact:
  assumes table: "comma_semantic_b1_binding_table_exact action shift rows"
    and phase: "phase<924"
  shows "comma_semantic_b1_binding_lookup rows
      (comma_semantic_b1_column_at action shift phase) =
    action ((phase+shift) mod 924)"
proof -
  let ?column = "comma_semantic_b1_column_at action shift phase"
  let ?value = "action ((phase+shift) mod 924)"
  have cover: "(\<Union> (fst ` set rows)) = {..<924}"
    using table by (simp add: comma_semantic_b1_binding_table_exact_def)
  have phase_covered: "phase\<in>(\<Union> (fst ` set rows))"
    using phase cover by simp
  then obtain column where column_image: "column\<in>fst ` set rows"
    and phase_column: "phase\<in>column" by blast
  then obtain row where row: "row\<in>set rows" and row_column: "column=fst row"
    by blast
  obtain row_key row_value where row_pair: "row=(row_key,row_value)"
    by (cases row) auto
  have row_exact:
    "comma_semantic_b1_binding_row_exact action shift (row_key,row_value)"
    using table row row_pair
    by (auto simp: comma_semantic_b1_binding_table_exact_def)
  have phase_value: "row_value=?value"
    using comma_semantic_b1_binding_row_exact_phase[OF row_exact]
      phase_column row_column row_pair
    by simp
  have queried_column:
    "?column={q. q<924 \<and> action ((q+shift) mod 924)=?value}"
    by (auto simp: comma_semantic_b1_column_at_def)
  have row_key_is_query: "row_key=?column"
    using row_exact phase_value row_pair queried_column
    by (auto simp: comma_semantic_b1_binding_row_exact_def)
  have selected_row_present: "(row_key,row_value)\<in>set rows"
    using row row_pair by simp
  have key_present: "(?column,?value)\<in>set rows"
    using selected_row_present row_key_is_query phase_value by simp
  have unique:
    "\<And>result. (?column,result)\<in>set rows \<Longrightarrow> result=?value"
  proof -
    fix result
    assume result_row: "(?column,result)\<in>set rows"
    have keys_distinct: "distinct (map fst rows)"
      using table by (simp add: comma_semantic_b1_binding_table_exact_def)
    have first_injective: "inj_on fst (set rows)"
      using keys_distinct by (simp add: distinct_map)
    have "(?column,result)=(?column,?value)"
      by (rule inj_onD[OF first_injective]) (use result_row key_present in auto)
    then show "result=?value" by simp
  qed
  show ?thesis
    unfolding comma_semantic_b1_binding_lookup_def
    by (rule the_equality) (auto intro: key_present dest: unique)
qed

theorem comma_semantic_b1_occurrence_binding_table_reconstructs:
  assumes table:
      "comma_semantic_b1_binding_table_exact action
        (comma_semantic_b1_inverse_shift return_shift) rows"
  shows "comma_semantic_b1_binding_lookup rows
      (comma_semantic_b1_column_at action
        (comma_semantic_b1_inverse_shift return_shift)
        ((clock+return_shift+source_shift) mod 924)) =
    action ((clock+source_shift) mod 924)"
proof -
  let ?phase="(clock+return_shift+source_shift) mod 924"
  have phase_bound: "?phase<924" by simp
  have lookup:
    "comma_semantic_b1_binding_lookup rows
        (comma_semantic_b1_column_at action
          (comma_semantic_b1_inverse_shift return_shift) ?phase) =
      action ((?phase+comma_semantic_b1_inverse_shift return_shift) mod 924)"
    by (rule comma_semantic_b1_binding_table_lookup_exact[OF table phase_bound])
  have inverse_sum:
    "((?phase+comma_semantic_b1_inverse_shift return_shift) mod 924) =
      ((clock+source_shift) mod 924)"
  proof -
    have reassociated:
      "?phase=((clock+source_shift+return_shift) mod 924)"
      by (simp add: add.assoc add.commute add.left_commute)
    have cancelled:
      "(((clock+source_shift+return_shift) mod 924+
          comma_semantic_b1_inverse_shift return_shift) mod 924) =
        ((clock+source_shift) mod 924)"
      by (rule comma_semantic_b1_cancel_shift)
    show ?thesis using reassociated cancelled by simp
  qed
  show ?thesis using lookup inverse_sum by simp
qed

ML \<open>Thm.consolidate [@{thm comma_semantic_b1_occurrence_binding_table_reconstructs}]; Comma_Proof_Profile.report "Semantic B1 columns claim=occurrence-binding-table checked"\<close>

record comma_semantic_b1_occurrence_binding =
  comma_semantic_b1_occurrence_template :: comma_semantic_b1_return_template
  comma_semantic_b1_occurrence_template_function :: "nat \<Rightarrow> comma_semantic_b1_column"
  comma_semantic_b1_occurrence_return_shift :: nat
  comma_semantic_b1_occurrence_source_shift :: nat
  comma_semantic_b1_occurrence_output_binding ::
    "comma_semantic_b1_column \<Rightarrow> comma_semantic_b1_result"
  comma_semantic_b1_occurrence_complete :: bool

definition comma_semantic_b1_bind_occurrence ::
    "(nat \<Rightarrow> comma_semantic_b1_result) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
      comma_semantic_b1_occurrence_binding" where
  "comma_semantic_b1_bind_occurrence action return_shift source_shift =
    \<lparr>comma_semantic_b1_occurrence_template = comma_semantic_b1_template_id action,
      comma_semantic_b1_occurrence_template_function =
        comma_semantic_b1_template_function action return_shift,
      comma_semantic_b1_occurrence_return_shift = return_shift mod 924,
      comma_semantic_b1_occurrence_source_shift = source_shift mod 924,
      comma_semantic_b1_occurrence_output_binding =
        comma_semantic_b1_output_binding action return_shift,
      comma_semantic_b1_occurrence_complete = True\<rparr>"

lemma comma_semantic_b1_column_at_finite:
  "finite (comma_semantic_b1_column_at action shift phase)"
  unfolding comma_semantic_b1_column_at_def
  by (rule finite_subset[of _ "{..<924}"]) auto

lemma comma_semantic_b1_column_at_nonempty:
  assumes phase: "phase<924"
  shows "comma_semantic_b1_column_at action shift phase \<noteq> {}"
  using phase by (auto simp: comma_semantic_b1_column_at_def)

lemma comma_semantic_b1_column_at_min_member:
  assumes phase: "phase<924"
  shows "Min (comma_semantic_b1_column_at action shift phase) < 924"
    "Min (comma_semantic_b1_column_at action shift phase) \<in>
      comma_semantic_b1_column_at action shift phase"
proof -
  let ?column = "comma_semantic_b1_column_at action shift phase"
  have finite: "finite ?column"
    by (rule comma_semantic_b1_column_at_finite)
  have nonempty: "?column \<noteq> {}"
    by (rule comma_semantic_b1_column_at_nonempty[OF phase])
  have member: "Min ?column \<in> ?column"
    by (rule Min_in[OF finite nonempty])
  then show "Min ?column < 924"
    by (auto simp: comma_semantic_b1_column_at_def)
  show "Min ?column \<in> ?column" by (rule member)
qed

lemma comma_semantic_b1_bind_column_exact:
  assumes phase: "phase<924"
  shows "comma_semantic_b1_output_binding action shift
      (comma_semantic_b1_column_at action
        (comma_semantic_b1_inverse_shift shift) phase) =
    action ((phase + comma_semantic_b1_inverse_shift shift) mod 924)"
proof -
  let ?phase = "comma_semantic_b1_inverse_shift shift"
  let ?column = "comma_semantic_b1_column_at action ?phase phase"
  have representative:
    "Min ?column \<in> ?column"
    by (rule comma_semantic_b1_column_at_min_member[OF phase])
  have same_output:
    "action ((Min ?column + ?phase) mod 924) =
      action ((phase + ?phase) mod 924)"
    using representative by (auto simp: comma_semantic_b1_column_at_def)
  show ?thesis
    using same_output by (simp add: comma_semantic_b1_output_binding_def)
qed

lemma comma_semantic_b1_template_partition_member:
  assumes shift: "shift<924"
  shows "{comma_semantic_b1_template_function action shift phase | phase. phase<924}
      \<in> comma_semantic_b1_template_id action"
  using shift
  by (auto simp: comma_semantic_b1_template_function_def
      comma_semantic_b1_inverse_shift_def comma_semantic_b1_partition_at_def
      comma_semantic_b1_template_id_def)

lemma comma_semantic_b1_occurrence_template_member:
  "{comma_semantic_b1_occurrence_template_function
      (comma_semantic_b1_bind_occurrence action return_shift source_shift) phase |
      phase. phase<924} \<in>
    comma_semantic_b1_occurrence_template
      (comma_semantic_b1_bind_occurrence action return_shift source_shift)"
proof -
  let ?inverse = "comma_semantic_b1_inverse_shift return_shift"
  have inverse_bound: "?inverse<924"
    by (simp add: comma_semantic_b1_inverse_shift_def)
  have member:
    "{comma_semantic_b1_template_function action return_shift phase |
        phase. phase<924} \<in> comma_semantic_b1_template_id action"
  proof -
    have partition:
      "{comma_semantic_b1_template_function action return_shift phase |
          phase. phase<924} =
        comma_semantic_b1_partition_at action ?inverse"
      by (auto simp: comma_semantic_b1_template_function_def
          comma_semantic_b1_partition_at_def)
    have in_template:
      "comma_semantic_b1_partition_at action ?inverse
        \<in> comma_semantic_b1_template_id action"
      unfolding comma_semantic_b1_template_id_def
      using inverse_bound by blast
    show ?thesis using partition in_template by simp
  qed
  show ?thesis using member
    by (simp add: comma_semantic_b1_bind_occurrence_def)
qed

lemma comma_semantic_b1_translation_partition:
  assumes shift: "shift<924" and delta: "delta<924"
  shows "comma_semantic_b1_partition_at
      (\<lambda>phase. action ((phase+delta) mod 924)) shift =
    comma_semantic_b1_partition_at action ((shift+delta) mod 924)"
proof -
  have clock_sum:
    "((q+shift) mod 924+delta) mod 924 =
      (q+(shift+delta) mod 924) mod 924" for q :: nat
    by (simp only: mod_add_left_eq mod_add_right_eq add.assoc)
  show ?thesis
    by (simp only: comma_semantic_b1_partition_at_def
      comma_semantic_b1_column_at_def clock_sum)
qed

lemma comma_semantic_b1_template_phase_invariant:
  assumes delta: "delta<924"
  shows "comma_semantic_b1_template_id
      (\<lambda>phase. action ((phase+delta) mod 924)) =
    comma_semantic_b1_template_id action"
proof (unfold comma_semantic_b1_template_id_def, rule set_eqI, rule iffI)
  fix partition
  assume member:
    "partition \<in> {comma_semantic_b1_partition_at
      (\<lambda>phase. action ((phase+delta) mod 924)) shift | shift. shift<924}"
  then obtain shift where shift: "shift<924"
    and partition:
      "partition=comma_semantic_b1_partition_at
        (\<lambda>phase. action ((phase+delta) mod 924)) shift"
    by blast
  have translated:
    "partition=comma_semantic_b1_partition_at action ((shift+delta) mod 924)"
    using comma_semantic_b1_translation_partition[OF shift delta] partition by simp
  have translated_bound: "(shift+delta) mod 924<924" by simp
  show "partition \<in>
    {comma_semantic_b1_partition_at action shift | shift. shift<924}"
    using translated translated_bound by blast
next
  fix partition
  assume member:
    "partition \<in> {comma_semantic_b1_partition_at action shift | shift. shift<924}"
  then obtain phase where phase: "phase<924"
    and partition: "partition=comma_semantic_b1_partition_at action phase"
    by blast
  let ?back = "(phase + (924-delta)) mod 924"
  have back_bound: "?back<924" by simp
  have shifted_back: "((?back+delta) mod 924)=phase"
  proof -
    have phase_cancel:
      "(((phase+(924-delta)) mod 924+delta) mod 924)=phase mod 924"
    proof -
      have sum: "phase+(924-delta)+delta=phase+924"
        using delta by arith
      have "(((phase+(924-delta)) mod 924+delta) mod 924) =
          (phase+(924-delta)+delta) mod 924"
        by (rule mod_add_left_eq)
      also have "...=(phase+924) mod 924" by (simp only: sum)
      also have "...=phase mod 924" by simp
      finally show ?thesis .
    qed
    show ?thesis using phase_cancel phase by simp
  qed
  have translated:
    "comma_semantic_b1_partition_at
      (\<lambda>clock. action ((clock+delta) mod 924)) ?back =
      comma_semantic_b1_partition_at action phase"
    using comma_semantic_b1_translation_partition[OF back_bound delta]
      phase shifted_back by simp
  show "partition \<in>
    {comma_semantic_b1_partition_at
      (\<lambda>clock. action ((clock+delta) mod 924)) shift | shift. shift<924}"
    using partition translated back_bound by blast
qed

lemma comma_semantic_b1_column_label_invariant:
  assumes injective: "inj relabel"
  shows "comma_semantic_b1_column_at (\<lambda>phase. relabel (action phase))
      shift phase = comma_semantic_b1_column_at action shift phase"
proof -
  have relabel_eq: "\<And>x y. relabel x = relabel y \<longleftrightarrow> x=y"
    using injective by (rule inj_eq)
  show ?thesis
    unfolding comma_semantic_b1_column_at_def
    by (simp only: relabel_eq)
qed

lemma comma_semantic_b1_partition_label_invariant:
  assumes injective: "inj relabel"
  shows "comma_semantic_b1_partition_at
      (\<lambda>phase. relabel (action phase)) shift =
    comma_semantic_b1_partition_at action shift"
proof -
  have columns:
    "\<forall>phase<924. comma_semantic_b1_column_at
        (\<lambda>clock. relabel (action clock)) shift phase =
      comma_semantic_b1_column_at action shift phase"
    using comma_semantic_b1_column_label_invariant[OF injective]
    by blast
  show ?thesis
    unfolding comma_semantic_b1_partition_at_def
    using columns by blast
qed

lemma comma_semantic_b1_template_label_invariant:
  assumes injective: "inj relabel"
  shows "comma_semantic_b1_template_id (\<lambda>phase. relabel (action phase)) =
    comma_semantic_b1_template_id action"
proof -
  have partitions:
    "\<forall>shift<924. comma_semantic_b1_partition_at
        (\<lambda>phase. relabel (action phase)) shift =
      comma_semantic_b1_partition_at action shift"
    using comma_semantic_b1_partition_label_invariant[OF injective]
    by blast
  show ?thesis
    unfolding comma_semantic_b1_template_id_def
    using partitions by blast
qed

theorem comma_semantic_b1_occurrence_reconstructs:
  "comma_semantic_b1_occurrence_complete
      (comma_semantic_b1_bind_occurrence action return_shift source_shift)
    \<and> comma_semantic_b1_occurrence_template
      (comma_semantic_b1_bind_occurrence action return_shift source_shift) =
        comma_semantic_b1_template_id action
    \<and> (\<forall>clock. comma_semantic_b1_occurrence_output_binding
          (comma_semantic_b1_bind_occurrence action return_shift source_shift)
          (comma_semantic_b1_occurrence_template_function
            (comma_semantic_b1_bind_occurrence action return_shift source_shift)
            ((clock + return_shift + source_shift) mod 924)) =
        action ((clock+source_shift) mod 924))"
proof (intro conjI allI)
  show "comma_semantic_b1_occurrence_complete
      (comma_semantic_b1_bind_occurrence action return_shift source_shift)"
    by (simp add: comma_semantic_b1_bind_occurrence_def)
  show "comma_semantic_b1_occurrence_template
      (comma_semantic_b1_bind_occurrence action return_shift source_shift) =
        comma_semantic_b1_template_id action"
    by (simp add: comma_semantic_b1_bind_occurrence_def)
  fix clock
  let ?phase = "(clock + return_shift + source_shift) mod 924"
  let ?inverse = "comma_semantic_b1_inverse_shift return_shift"
  have phase_bound: "?phase<924" by simp
  have bound_column:
    "comma_semantic_b1_output_binding action return_shift
        (comma_semantic_b1_template_function action return_shift ?phase) =
      action ((?phase+?inverse) mod 924)"
    unfolding comma_semantic_b1_template_function_def
    by (rule comma_semantic_b1_bind_column_exact[OF phase_bound])
  have inverse_sum:
    "((?phase+?inverse) mod 924) =
      ((clock+source_shift) mod 924)"
  proof -
    have reassociated:
      "?phase=((clock+source_shift+return_shift) mod 924)"
      by (simp add: add.assoc add.commute add.left_commute)
    have cancelled:
      "(((clock+source_shift+return_shift) mod 924+?inverse) mod 924)=
        (clock+source_shift) mod 924"
      by (rule comma_semantic_b1_cancel_shift)
    show ?thesis using reassociated cancelled by simp
  qed
  show "comma_semantic_b1_occurrence_output_binding
      (comma_semantic_b1_bind_occurrence action return_shift source_shift)
      (comma_semantic_b1_occurrence_template_function
        (comma_semantic_b1_bind_occurrence action return_shift source_shift) ?phase) =
      action ((clock+source_shift) mod 924)"
    using bound_column inverse_sum
    by (simp add: comma_semantic_b1_bind_occurrence_def)
qed

ML \<open>Thm.consolidate [@{thm comma_semantic_b1_occurrence_reconstructs}]; Comma_Proof_Profile.report "Semantic B1 columns claim=occurrence-reconstructs checked"\<close>

theorem comma_semantic_b1_root_template_reconstructs:
  assumes root: "root<46"
  shows "\<forall>clock. comma_semantic_b1_occurrence_output_binding
      (comma_semantic_b1_bind_occurrence
        (comma_semantic_b1_id_of_root root) return_shift 0)
      (comma_semantic_b1_occurrence_template_function
        (comma_semantic_b1_bind_occurrence
          (comma_semantic_b1_id_of_root root) return_shift 0)
        ((clock+return_shift) mod 924)) =
    comma_semantic_b1_of_word (comma_orbit_word 0 (clock mod 924) root)"
proof (intro allI)
  fix clock
  have reconstruction:
    "comma_semantic_b1_occurrence_complete
        (comma_semantic_b1_bind_occurrence
          (comma_semantic_b1_id_of_root root) return_shift 0)
      \<and> comma_semantic_b1_occurrence_template
        (comma_semantic_b1_bind_occurrence
          (comma_semantic_b1_id_of_root root) return_shift 0) =
          comma_semantic_b1_template_id (comma_semantic_b1_id_of_root root)
      \<and> (\<forall>clock. comma_semantic_b1_occurrence_output_binding
            (comma_semantic_b1_bind_occurrence
              (comma_semantic_b1_id_of_root root) return_shift 0)
            (comma_semantic_b1_occurrence_template_function
              (comma_semantic_b1_bind_occurrence
                (comma_semantic_b1_id_of_root root) return_shift 0)
              ((clock+return_shift) mod 924)) =
          comma_semantic_b1_id_of_root root (clock mod 924))"
    using comma_semantic_b1_occurrence_reconstructs
      [of "comma_semantic_b1_id_of_root root" return_shift 0]
    by (simp add: add.assoc)
  have occurrence:
    "comma_semantic_b1_occurrence_output_binding
        (comma_semantic_b1_bind_occurrence
          (comma_semantic_b1_id_of_root root) return_shift 0)
        (comma_semantic_b1_occurrence_template_function
          (comma_semantic_b1_bind_occurrence
            (comma_semantic_b1_id_of_root root) return_shift 0)
          ((clock+return_shift) mod 924)) =
      comma_semantic_b1 (clock mod 924) root"
    using reconstruction
    by (auto simp: comma_semantic_b1_id_of_root_def)
  have orbit:
    "comma_semantic_b1 (clock mod 924) root =
      comma_semantic_b1_of_word (comma_orbit_word 0 (clock mod 924) root)"
    by (rule comma_semantic_b1_exact_orbit) (simp_all add: assms)
  show "comma_semantic_b1_occurrence_output_binding
        (comma_semantic_b1_bind_occurrence
          (comma_semantic_b1_id_of_root root) return_shift 0)
        (comma_semantic_b1_occurrence_template_function
          (comma_semantic_b1_bind_occurrence
            (comma_semantic_b1_id_of_root root) return_shift 0)
          ((clock+return_shift) mod 924)) =
      comma_semantic_b1_of_word (comma_orbit_word 0 (clock mod 924) root)"
    using occurrence orbit by simp
qed
ML \<open>Thm.consolidate [@{thm comma_semantic_b1_root_template_reconstructs}]; Comma_Proof_Profile.report "Semantic B1 columns claim=root-template checked"\<close>

ML \<open>
  val checked = @{thms comma_semantic_b1_column_at_min_member
    comma_semantic_b1_bind_column_exact
    comma_semantic_b1_binding_table_lookup_exact
    comma_semantic_b1_binding_table_exact_action_congruent
    comma_semantic_b1_occurrence_binding_table_reconstructs
    comma_semantic_b1_graph_binding_root_exact
    comma_semantic_b1_graph_scopes_refine_binding_table
    comma_semantic_b1_graph_root_scopes_refine_binding_table
    comma_semantic_b1_template_partition_member
    comma_semantic_b1_occurrence_template_member
    comma_semantic_b1_translation_partition
    comma_semantic_b1_template_phase_invariant
    comma_semantic_b1_column_label_invariant
    comma_semantic_b1_partition_label_invariant
    comma_semantic_b1_template_label_invariant
    comma_semantic_b1_occurrence_reconstructs
    comma_semantic_b1_root_template_reconstructs};
  val _ = Thm.consolidate checked;
  val _ = Comma_Proof_Profile.report "Semantic B1 columns claims consolidated";
  val _ = Comma_Proof_Profile.report "Semantic B1 columns audit=native entered";
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Output-column template and occurrence binding" checked;
  val _ = Comma_Proof_Profile.report "Semantic B1 columns audit=native checked";
  val _ = Comma_Proof_Profile.report "Semantic B1 columns audit=graph-output entered";
  val _ = Comma_Proof_Dependency_Audit.require_expected_paths @{context}
    "B1 graph-column output binding"
    ["comma_semantic_b1_graph_eval_refines_endpoint"]
    @{thms comma_semantic_b1_graph_binding_root_exact
      comma_semantic_b1_graph_root_scopes_refine_binding_table};
  val _ = Comma_Proof_Profile.report "Semantic B1 columns audit=graph-output checked";
  val _ = Comma_Proof_Profile.report "Semantic B1 columns audit=template entered";
  val _ = Comma_Proof_Dependency_Audit.require_expected_paths @{context}
    "Exact B1 output reconstruction through a label-free template"
    ["comma_semantic_b1_occurrence_reconstructs",
      "comma_semantic_b1_exact_orbit"]
    @{thms comma_semantic_b1_root_template_reconstructs};
  val _ = Comma_Proof_Profile.report "Semantic B1 columns audit=template checked";
\<close>

end
