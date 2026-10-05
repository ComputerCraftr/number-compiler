theory Comma_Semantic_B1_Instance
  imports Comma_Semantic_B1.Comma_Semantic_B1_CRT_Split_Bindings
    Comma_Semantic_B1_Occurrence_Rows
begin

definition comma_semantic_b1_crt_root_split_action ::
    "nat \<Rightarrow> comma_crt_split_action" where
  "comma_semantic_b1_crt_root_split_action root =
    (case comma_semantic_b1_crt_root_occurrence root of
       None \<Rightarrow> comma_crt_occurrence_split_initial
     | Some occurrence \<Rightarrow>
         comma_crt_occurrence_split_action occurrence)"

lemma comma_semantic_b1_crt_occurrence_split_shifted_cover:
  fixes occurrence :: comma_semantic_b1_crt_occurrence
  assumes wellformed: "comma_semantic_b1_crt_occurrence_wellformed occurrence"
  shows "\<Union> (comma_crt_set ` set
      (map (comma_crt_shift (comma_semantic_b1_crt_occurrence_rebase occurrence))
        (comma_semantic_b1_crt_occurrence_columns occurrence))) = {..<924}"
proof (rule set_eqI)
  fix phase :: nat
  let ?columns = "comma_semantic_b1_crt_occurrence_columns occurrence"
  let ?rho = "comma_semantic_b1_crt_occurrence_rebase occurrence"
  show "phase \<in> \<Union> (comma_crt_set ` set (map (comma_crt_shift ?rho) ?columns))
      \<longleftrightarrow> phase \<in> {..<924}"
  proof
    assume member: "phase \<in> \<Union> (comma_crt_set ` set (map (comma_crt_shift ?rho) ?columns))"
    then obtain shifted where
      shifted_member: "shifted \<in> set (map (comma_crt_shift ?rho) ?columns)"
      and phase_member: "phase \<in> comma_crt_set shifted"
      by blast
    obtain column where column_member: "column \<in> set ?columns"
      and shifted_eq: "shifted=comma_crt_shift ?rho column"
      using shifted_member by auto
    have column_admitted: "comma_crt_admitted 0 column"
      using wellformed column_member
      by (auto simp: comma_semantic_b1_crt_occurrence_wellformed_def list_all_iff)
    have "phase \<in> comma_semantic_b1_column_advance ?rho (comma_crt_set column)"
      using phase_member shifted_eq comma_crt_shift_is_power_advance[OF column_admitted]
      by simp
    then show "phase \<in> {..<924}"
      by (auto simp: comma_semantic_b1_column_advance_def)
  next
    assume phase_bound: "phase \<in> {..<924}"
    have clock_bound: "(phase+?rho) mod 924<924" by simp
    have covered: "comma_semantic_b1_crt_occurrence_covered ?columns"
      using wellformed by (simp add: comma_semantic_b1_crt_occurrence_wellformed_def)
    let ?clock = "(phase+?rho) mod 924"
    obtain index where index_bound: "index<length ?columns"
      and selected: "comma_semantic_b1_crt_occurrence_find_index ?clock ?columns=Some index"
      using comma_semantic_b1_crt_occurrence_find_index_total[OF clock_bound covered]
      by blast
    have evaluates: "comma_crt_eval ?clock (?columns!index)"
      using comma_semantic_b1_crt_occurrence_find_index_entry[OF selected] by blast
    have column_admitted: "comma_crt_admitted 0 (?columns!index)"
      using wellformed index_bound
      by (auto simp: comma_semantic_b1_crt_occurrence_wellformed_def list_all_iff)
    have shifted_set:
      "comma_crt_set (comma_crt_shift ?rho (?columns!index)) =
        comma_semantic_b1_column_advance ?rho (comma_crt_set (?columns!index))"
      by (rule comma_crt_shift_is_power_advance[OF column_admitted])
    have in_advance:
      "phase \<in> comma_semantic_b1_column_advance ?rho (comma_crt_set (?columns!index))"
      using phase_bound evaluates by (auto simp: comma_semantic_b1_column_advance_def
        comma_crt_set_def)
    have shifted_member:
      "comma_crt_shift ?rho (?columns!index) \<in>
        set (map (comma_crt_shift ?rho) ?columns)"
      using index_bound by (auto simp: in_set_conv_nth)
    show "phase \<in> \<Union> (comma_crt_set ` set (map (comma_crt_shift ?rho) ?columns))"
      using shifted_set in_advance shifted_member by blast
  qed
qed

lemma comma_semantic_b1_crt_occurrence_split_shifted_fiber:
  fixes occurrence :: comma_semantic_b1_crt_occurrence
    and source :: comma_finite_position and index :: nat
  assumes wellformed: "comma_semantic_b1_crt_occurrence_wellformed occurrence"
    and exact: "comma_semantic_b1_crt_occurrence_exact source occurrence"
    and labels: "distinct (comma_semantic_b1_crt_occurrence_beta occurrence)"
    and index: "index<length (comma_semantic_b1_crt_occurrence_columns occurrence)"
  shows "comma_crt_set (comma_crt_shift
      (comma_semantic_b1_crt_occurrence_rebase occurrence)
      (comma_semantic_b1_crt_occurrence_columns occurrence ! index)) =
    {phase. phase<924 \<and> comma_semantic_b1_round_output phase source =
      comma_semantic_b1_crt_occurrence_beta occurrence ! index}"
proof -
  let ?columns = "comma_semantic_b1_crt_occurrence_columns occurrence"
  let ?beta = "comma_semantic_b1_crt_occurrence_beta occurrence"
  let ?rho = "comma_semantic_b1_crt_occurrence_rebase occurrence"
  have admitted: "comma_crt_admitted 0 (?columns!index)"
    using wellformed index
    by (auto simp: comma_semantic_b1_crt_occurrence_wellformed_def list_all_iff)
  have raw_fiber:
    "comma_crt_set (?columns!index) =
      {phase. phase<924 \<and>
        comma_semantic_b1_round_output
          ((phase+comma_semantic_b1_inverse_shift ?rho) mod 924) source = ?beta!index}"
    by (rule comma_semantic_b1_crt_occurrence_raw_column_fiber
      [OF wellformed exact labels index])
  have shifted:
    "comma_crt_set (comma_crt_shift ?rho (?columns!index)) =
      comma_semantic_b1_column_advance ?rho (comma_crt_set (?columns!index))"
    by (rule comma_crt_shift_is_power_advance[OF admitted])
  have cancel:
    "\<And>phase. (((phase+?rho) mod 924 + comma_semantic_b1_inverse_shift ?rho) mod 924) =
      phase mod 924"
    by (rule comma_semantic_b1_cancel_shift)
  show ?thesis
  proof (rule set_eqI)
    fix phase :: nat
    show "phase \<in> comma_crt_set (comma_crt_shift ?rho (?columns!index)) \<longleftrightarrow>
        phase \<in> {phase. phase<924 \<and>
          comma_semantic_b1_round_output phase source = ?beta!index}"
      using shifted raw_fiber cancel[of phase]
      by (auto simp: comma_semantic_b1_column_advance_def)
  qed
qed

lemma comma_semantic_b1_crt_occurrence_split_exact:
  fixes occurrence :: comma_semantic_b1_crt_occurrence
    and source :: comma_finite_position
  assumes wellformed: "comma_semantic_b1_crt_occurrence_wellformed occurrence"
    and exact: "comma_semantic_b1_crt_occurrence_exact source occurrence"
    and labels: "distinct (comma_semantic_b1_crt_occurrence_beta occurrence)"
  shows "comma_crt_mdd_split_consistent 0
      (comma_crt_split_control (comma_semantic_b1_crt_occurrence_split_action occurrence))
      (comma_crt_split_weight (comma_semantic_b1_crt_occurrence_split_action occurrence)) \<and>
    (\<forall>phase<924. comma_crt_split_mdd_result_at phase
      (comma_crt_split_control (comma_semantic_b1_crt_occurrence_split_action occurrence))
      (comma_crt_split_weight (comma_semantic_b1_crt_occurrence_split_action occurrence)) =
      Some (comma_semantic_b1_round_output phase source))"
proof -
  let ?columns = "comma_semantic_b1_crt_occurrence_columns occurrence"
  let ?beta = "comma_semantic_b1_crt_occurrence_beta occurrence"
  let ?rho = "comma_semantic_b1_crt_occurrence_rebase occurrence"
  have width: "length ?columns=length ?beta"
    using wellformed by (simp add: comma_semantic_b1_crt_occurrence_wellformed_def)
  have admitted: "list_all (comma_crt_admitted 0) ?columns"
    using wellformed by (simp add: comma_semantic_b1_crt_occurrence_wellformed_def)
  have fibers: "\<forall>i<length ?columns.
      comma_crt_set (comma_crt_shift ?rho (?columns!i)) =
        {phase. phase<924 \<and> comma_semantic_b1_round_output phase source = ?beta!i}"
    using comma_semantic_b1_crt_occurrence_split_shifted_fiber
      [OF wellformed exact labels] by blast
  have covers:
    "\<Union> (comma_crt_set ` set (map (comma_crt_shift ?rho) ?columns))={..<924}"
    by (rule comma_semantic_b1_crt_occurrence_split_shifted_cover[OF wellformed])
  have checked:
    "comma_crt_mdd_split_consistent 0
      (comma_crt_split_control
        (comma_crt_occurrence_split_from_bindings ?rho ?columns ?beta
          comma_crt_occurrence_split_initial))
      (comma_crt_split_weight
        (comma_crt_occurrence_split_from_bindings ?rho ?columns ?beta
          comma_crt_occurrence_split_initial)) \<and>
    (\<forall>phase<924. comma_crt_split_mdd_result_at phase
      (comma_crt_split_control
        (comma_crt_occurrence_split_from_bindings ?rho ?columns ?beta
          comma_crt_occurrence_split_initial))
      (comma_crt_split_weight
        (comma_crt_occurrence_split_from_bindings ?rho ?columns ?beta
          comma_crt_occurrence_split_initial)) =
      Some (comma_semantic_b1_round_output phase source))"
    by (rule comma_crt_occurrence_split_from_bindings_exact
      [where action="(\<lambda>phase. comma_semantic_b1_round_output phase source)"
        and rebase=?rho,
       OF width admitted labels fibers covers])
  show ?thesis
    using checked by (simp only: comma_crt_occurrence_split_action_def)
qed

lemma comma_semantic_b1_crt_root_split_action_exact:
  assumes root: "root<46"
  shows "comma_crt_mdd_split_consistent 0
      (comma_crt_split_control (comma_semantic_b1_crt_root_split_action root))
      (comma_crt_split_weight (comma_semantic_b1_crt_root_split_action root)) \<and>
    (\<forall>phase<924. comma_crt_split_mdd_result_at phase
      (comma_crt_split_control (comma_semantic_b1_crt_root_split_action root))
      (comma_crt_split_weight (comma_semantic_b1_crt_root_split_action root)) =
      Some (comma_semantic_b1_round_output phase
        (Comma_Entry 1 0 (comma_offset_representatives!root)))"
proof -
  let ?source = "Comma_Entry 1 0 (comma_offset_representatives!root)"
  obtain occurrence where lookup:
      "comma_semantic_b1_crt_root_occurrence root=Some occurrence"
    and exact: "comma_semantic_b1_crt_occurrence_exact ?source occurrence"
    using comma_semantic_b1_crt_root_occurrence_exact[OF root] by blast
  have wellformed: "comma_semantic_b1_crt_occurrence_wellformed occurrence"
    using exact by (simp add: comma_semantic_b1_crt_occurrence_exact_def)
  have distinct: "distinct (comma_semantic_b1_crt_occurrence_beta occurrence)"
    by (rule comma_semantic_b1_crt_root_occurrence_distinct_binding[OF root lookup])
  have occurrence_exact:
    "comma_crt_mdd_split_consistent 0
        (comma_crt_split_control (comma_crt_occurrence_split_action occurrence))
        (comma_crt_split_weight (comma_crt_occurrence_split_action occurrence)) \<and>
      (\<forall>phase<924. comma_crt_split_mdd_result_at phase
        (comma_crt_split_control (comma_crt_occurrence_split_action occurrence))
        (comma_crt_split_weight (comma_crt_occurrence_split_action occurrence)) =
        Some (comma_semantic_b1_round_output phase ?source))"
    by (rule comma_semantic_b1_crt_occurrence_split_exact
      [OF wellformed exact distinct])
  show ?thesis
    using occurrence_exact lookup root
    by (simp add: comma_semantic_b1_crt_root_split_action_def)
qed

lemma comma_semantic_b1_crt_root_split_action_consistent:
  "comma_crt_mdd_split_consistent 0
      (comma_crt_split_control (comma_semantic_b1_crt_root_split_action root))
      (comma_crt_split_weight (comma_semantic_b1_crt_root_split_action root))"
proof (cases "root<46")
  case True
  then show ?thesis using comma_semantic_b1_crt_root_split_action_exact by blast
next
  case False
  then show ?thesis
    by (simp add: comma_semantic_b1_crt_root_split_action_def
      comma_crt_occurrence_split_initial_def comma_crt_split_invalid_action_def
      comma_crt_mdd_split_consistent_def)
qed

lemma comma_crt_split_mdd_result_at_periodic:
  assumes consistent:
    "comma_crt_mdd_split_consistent 0 controls weights"
  shows "comma_crt_split_mdd_result_at (phase mod 924) controls weights =
    comma_crt_split_mdd_result_at phase controls weights"
proof -
  have controls_admitted: "comma_crt_mdd_admitted 0 controls"
    and weights_admitted: "comma_crt_mdd_admitted 0 weights"
    using consistent by (auto simp: comma_crt_mdd_split_consistent_def)
  have control_periodic:
    "comma_crt_mdd_eval (phase mod 924) controls =
      comma_crt_mdd_eval phase controls"
    by (rule comma_crt_mdd_eval_periodic[OF controls_admitted])
  have weight_periodic:
    "comma_crt_mdd_eval (phase mod 924) weights =
      comma_crt_mdd_eval phase weights"
    by (rule comma_crt_mdd_eval_periodic[OF weights_admitted])
  show ?thesis using control_periodic weight_periodic
    by (simp add: comma_crt_split_mdd_result_at_def)
qed

lemma comma_semantic_b1_crt_root_split_orbit_exact:
  assumes root: "root<46" and phase: "phase<924"
  shows "comma_crt_split_mdd_result_at phase
      (comma_crt_split_control (comma_semantic_b1_crt_root_split_action root))
      (comma_crt_split_weight (comma_semantic_b1_crt_root_split_action root)) =
    Some (comma_semantic_b1_of_word (comma_orbit_word 0 phase root))"
proof -
  have split_exact:
    "comma_crt_split_mdd_result_at phase
      (comma_crt_split_control (comma_semantic_b1_crt_root_split_action root))
      (comma_crt_split_weight (comma_semantic_b1_crt_root_split_action root)) =
      Some (comma_semantic_b1_round_output phase
        (Comma_Entry 1 0 (comma_offset_representatives!root)))"
    using comma_semantic_b1_crt_root_split_action_exact[OF root] phase by blast
  have round_exact:
    "comma_semantic_b1_round_output phase
      (Comma_Entry 1 0 (comma_offset_representatives!root)) =
      comma_semantic_b1 phase root"
    by (rule comma_semantic_b1_round_output_root_exact[OF phase root])
  have orbit_exact:
    "comma_semantic_b1 phase root =
      comma_semantic_b1_of_word (comma_orbit_word 0 phase root)"
    by (rule comma_semantic_b1_exact_orbit[OF phase root])
  show ?thesis using split_exact round_exact orbit_exact by simp
qed

fun comma_semantic_b1_crt_power_split_action ::
    "nat \<Rightarrow> nat \<Rightarrow> comma_crt_split_action" where
  "comma_semantic_b1_crt_power_split_action 0 root =
    comma_semantic_b1_crt_root_split_action root"
| "comma_semantic_b1_crt_power_split_action (Suc k) root =
    (let left = comma_semantic_b1_crt_power_split_action k root;
         composed = comma_crt_split_compose_from 4 (2^k)
           (comma_crt_split_control left) (comma_crt_split_weight left)
           (\<lambda>next_root. comma_crt_split_control
             (comma_semantic_b1_crt_power_split_action k next_root))
           (\<lambda>next_root. comma_crt_split_weight
             (comma_semantic_b1_crt_power_split_action k next_root))
     in \<lparr>comma_crt_split_control=fst composed,
         comma_crt_split_weight=snd composed\<rparr>)"

definition comma_semantic_b1_crt_split_compose ::
    "nat \<Rightarrow> nat \<Rightarrow>
      comma_crt_control_mdd \<times> comma_crt_weight_mdd" where
  "comma_semantic_b1_crt_split_compose k root =
    comma_crt_split_compose_from 4 (2^k)
      (comma_crt_split_control (comma_semantic_b1_crt_power_split_action k root))
      (comma_crt_split_weight (comma_semantic_b1_crt_power_split_action k root))
      (\<lambda>next_root. comma_crt_split_control
        (comma_semantic_b1_crt_power_split_action k next_root))
      (\<lambda>next_root. comma_crt_split_weight
        (comma_semantic_b1_crt_power_split_action k next_root))"

lemma comma_semantic_b1_crt_power_split_action_consistent:
  "comma_crt_mdd_split_consistent 0
    (comma_crt_split_control (comma_semantic_b1_crt_power_split_action k root))
    (comma_crt_split_weight (comma_semantic_b1_crt_power_split_action k root))"
proof (induction k arbitrary: root)
  case 0
  show ?case by (simp add: comma_semantic_b1_crt_root_split_action_consistent)
next
  case (Suc k)
  let ?left = "comma_semantic_b1_crt_power_split_action k root"
  let ?controls = "\<lambda>next_root. comma_crt_split_control
    (comma_semantic_b1_crt_power_split_action k next_root)"
  let ?weights = "\<lambda>next_root. comma_crt_split_weight
    (comma_semantic_b1_crt_power_split_action k next_root)"
  have left: "comma_crt_mdd_split_consistent 0
      (comma_crt_split_control ?left) (comma_crt_split_weight ?left)"
    by (rule Suc.IH)
  have right: "\<And>next_root. comma_crt_mdd_split_consistent 0
      (?controls next_root) (?weights next_root)"
    by (rule Suc.IH)
  have combined: "comma_crt_mdd_split_consistent 0
      (fst (comma_crt_split_compose_from 4 (2^k)
        (comma_crt_split_control ?left) (comma_crt_split_weight ?left)
        ?controls ?weights))
      (snd (comma_crt_split_compose_from 4 (2^k)
        (comma_crt_split_control ?left) (comma_crt_split_weight ?left)
        ?controls ?weights))"
    by (rule comma_crt_split_compose_from_consistent
      [where remaining=4, simplified diff_self_eq_0, OF _ left right]) simp
  show ?case using combined
    by (simp only: comma_semantic_b1_crt_power_split_action.simps Let_def
      comma_crt_split_action.select_convs)
qed

lemma comma_semantic_b1_crt_power_split_action_exact:
  fixes k root phase :: nat
  assumes root: "root<46" and phase: "phase<924"
  shows "comma_crt_split_mdd_result_at phase
      (comma_crt_split_control (comma_semantic_b1_crt_power_split_action k root))
      (comma_crt_split_weight (comma_semantic_b1_crt_power_split_action k root)) =
    Some (comma_semantic_b1_of_word (comma_orbit_word k phase root))"
  using root phase
proof (induction k arbitrary: root phase)
  case 0
  show ?case using "0.prems"
    by (simp only: comma_semantic_b1_crt_power_split_action.simps(1)
      comma_semantic_b1_crt_root_split_orbit_exact)
next
  case (Suc k)
  let ?span = "2^k"
  let ?left = "comma_semantic_b1_crt_power_split_action k root"
  let ?controls = "\<lambda>next_root. comma_crt_split_control
    (comma_semantic_b1_crt_power_split_action k next_root)"
  let ?weights = "\<lambda>next_root. comma_crt_split_weight
    (comma_semantic_b1_crt_power_split_action k next_root)"
  have left_consistent: "comma_crt_mdd_split_consistent 0
      (comma_crt_split_control ?left) (comma_crt_split_weight ?left)"
    by (rule comma_semantic_b1_crt_power_split_action_consistent)
  have right_consistent: "\<And>next_root. comma_crt_mdd_split_consistent 0
      (?controls next_root) (?weights next_root)"
    by (rule comma_semantic_b1_crt_power_split_action_consistent)
  have left_control: "comma_crt_mdd_admitted 0 (comma_crt_split_control ?left)"
    and left_weight: "comma_crt_mdd_admitted 0 (comma_crt_split_weight ?left)"
    using left_consistent by (auto simp: comma_crt_mdd_split_consistent_def)
  have right_control: "\<And>next_root. comma_crt_mdd_admitted 0 (?controls next_root)"
    and right_weight: "\<And>next_root. comma_crt_mdd_admitted 0 (?weights next_root)"
    using right_consistent by (auto simp: comma_crt_mdd_split_consistent_def)
  have composed_exact:
    "comma_crt_split_mdd_result_at phase
        (fst (comma_semantic_b1_crt_split_compose k root))
        (snd (comma_semantic_b1_crt_split_compose k root)) =
      comma_crt_split_compose_expected_at ?span
        (comma_crt_split_control ?left) (comma_crt_split_weight ?left)
        ?controls ?weights phase"
  unfolding comma_semantic_b1_crt_split_compose_def
  proof (rule comma_crt_split_compose_from_refines
      [where remaining=4, simplified diff_self_eq_0])
    show "4\<le>4" by simp
    show "comma_crt_mdd_admitted 0 (comma_crt_split_control ?left)"
      by (rule left_control)
    show "comma_crt_mdd_admitted 0 (comma_crt_split_weight ?left)"
      by (rule left_weight)
    show "\<And>next_root. comma_crt_mdd_admitted 0 (?controls next_root)"
      by (rule right_control)
    show "\<And>next_root. comma_crt_mdd_admitted 0 (?weights next_root)"
      by (rule right_weight)
  qed
  have left_exact:
    "comma_crt_split_mdd_result_at phase
        (comma_crt_split_control ?left) (comma_crt_split_weight ?left) =
      Some (comma_semantic_b1_of_word (comma_orbit_word k phase root))"
    by (rule Suc.IH[OF Suc.prems])
  have expected_exact:
    "comma_crt_split_compose_expected_at ?span
        (comma_crt_split_control ?left) (comma_crt_split_weight ?left)
        ?controls ?weights phase =
      Some (comma_semantic_b1_of_word (comma_orbit_word (Suc k) phase root))"
  proof -
    let ?left_result = "comma_semantic_b1_of_word (comma_orbit_word k phase root)"
    have word_square:
      "comma_semantic_b1_of_word (comma_orbit_word (Suc k) phase root) =
        comma_semantic_word_then ?span
          (\<lambda>p i. comma_semantic_b1_of_word (comma_orbit_word k p i))
          (\<lambda>p i. comma_semantic_b1_of_word (comma_orbit_word k p i))
          phase root"
      by (rule comma_semantic_b1_square[OF Suc.prems])
    show ?thesis
    proof (cases ?left_result)
      case (Comma_Semantic_B1_Live next_root)
      have word_live:
        "comma_orbit_word k phase root=Comma_Word_Live next_root"
        using Comma_Semantic_B1_Live
        by (cases "comma_orbit_word k phase root") (simp_all add:
          comma_semantic_b1_of_word.simps)
      have next_root_bound: "next_root<46"
        by (rule comma_orbit_word_live_bound[OF word_live])
      let ?right_phase = "(phase+?span) mod 924"
      have right_phase_bound: "?right_phase<924" by simp
      have right_exact:
        "comma_crt_split_mdd_result_at ?right_phase
          (?controls next_root) (?weights next_root) =
            Some (comma_semantic_b1_of_word
              (comma_orbit_word k ?right_phase next_root))"
        by (rule Suc.IH[OF next_root_bound right_phase_bound])
      have right_unmodded:
        "comma_crt_split_mdd_result_at (phase+?span)
          (?controls next_root) (?weights next_root) =
            Some (comma_semantic_b1_of_word
              (comma_orbit_word k ?right_phase next_root))"
      proof -
        have periodic:
          "comma_crt_split_mdd_result_at ((phase+?span) mod 924)
              (?controls next_root) (?weights next_root) =
            comma_crt_split_mdd_result_at (phase+?span)
              (?controls next_root) (?weights next_root)"
          by (rule comma_crt_split_mdd_result_at_periodic
            [OF right_consistent[of next_root]])
        show ?thesis using right_exact periodic by simp
      qed
      show ?thesis
        using left_exact right_unmodded Comma_Semantic_B1_Live word_square
        by (simp add: comma_crt_split_compose_expected_at_def
          comma_crt_split_mdd_result_at_def comma_semantic_word_then_def
          comma_semantic_b1_cell_result_def comma_semantic_b1_weight_after_def)
    next
      case (Comma_Semantic_B1_Stop D)
      then show ?thesis using left_exact word_square
        by (simp add: comma_crt_split_compose_expected_at_def
          comma_crt_split_mdd_result_at_def comma_semantic_word_then_def)
    next
      case Comma_Semantic_B1_Invalid
      then show ?thesis using left_exact word_square
        by (simp add: comma_crt_split_compose_expected_at_def
          comma_crt_split_mdd_result_at_def comma_semantic_word_then_def)
    qed
  qed
  show ?case
    using composed_exact expected_exact
    by (simp only: comma_semantic_b1_crt_power_split_action.simps
      comma_semantic_b1_crt_split_compose_def Let_def
      comma_crt_split_action.select_convs)
qed

fun comma_crt_mdd_stop_weights_bounded242 ::
    "comma_crt_weight_mdd \<Rightarrow> bool" where
  "comma_crt_mdd_stop_weights_bounded242 (Comma_CRT_MDD_Leaf None) = False"
| "comma_crt_mdd_stop_weights_bounded242 (Comma_CRT_MDD_Leaf (Some D)) =
    (D\<le>242)"
| "comma_crt_mdd_stop_weights_bounded242 (Comma_CRT_MDD_Node level children) =
    list_all comma_crt_mdd_stop_weights_bounded242 children"

lemma comma_crt_mdd_stop_weights_bounded242_eval:
  assumes admitted: "comma_crt_mdd_admitted lower weights"
    and bounded: "comma_crt_mdd_stop_weights_bounded242 weights"
  shows "\<exists>D\<le>242. comma_crt_mdd_eval phase weights=Some (Some D)"
  using admitted bounded
proof (induction weights arbitrary: lower phase)
  case (Comma_CRT_MDD_Leaf payload)
  then show ?case by (cases payload) auto
next
  case (Comma_CRT_MDD_Node level children)
  have level_valid: "level<4"
    and width: "length children=comma_crt_period level"
    and children_admitted:
      "list_all (comma_crt_mdd_admitted (Suc level)) children"
    using Comma_CRT_MDD_Node.prems(1) by auto
  have children_bounded:
      "list_all comma_crt_mdd_stop_weights_bounded242 children"
    using Comma_CRT_MDD_Node.prems(2)
    by (simp only: comma_crt_mdd_stop_weights_bounded242.simps)
  have positive: "0<comma_crt_period level"
    by (rule comma_crt_period_positive[OF level_valid])
  have selected: "phase mod comma_crt_period level<length children"
    using positive width by simp
  have child_admitted:
      "comma_crt_mdd_admitted (Suc level)
        (children!(phase mod comma_crt_period level))"
    using children_admitted nth_mem[OF selected]
    by (auto simp: list_all_iff)
  have child_bounded:
      "comma_crt_mdd_stop_weights_bounded242
        (children!(phase mod comma_crt_period level))"
    using children_bounded nth_mem[OF selected]
    by (auto simp: list_all_iff)
  obtain D where D: "D\<le>242" and child_eval:
      "comma_crt_mdd_eval phase
        (children!(phase mod comma_crt_period level))=Some (Some D)"
    using Comma_CRT_MDD_Node.IH[OF nth_mem[OF selected]
      child_admitted child_bounded] by blast
  show ?case using level_valid width selected D child_eval
    by (simp add: comma_crt_mdd_eval_node_selected)
qed

lemma comma_crt_split_mdd_stop242_from_consistent:
  assumes consistent:
      "comma_crt_mdd_split_consistent 0 controls weights"
    and bounded: "comma_crt_mdd_stop_weights_bounded242 weights"
    and phase: "phase<924"
  obtains D where
    "comma_crt_split_mdd_result_at phase controls weights =
      Some (Comma_Semantic_B1_Stop D)" "D\<le>242"
proof -
  have weights_admitted: "comma_crt_mdd_admitted 0 weights"
    using consistent by (simp add: comma_crt_mdd_split_consistent_def)
  obtain D where D: "D\<le>242" and weight_eval:
      "comma_crt_mdd_eval phase weights=Some (Some D)"
    using comma_crt_mdd_stop_weights_bounded242_eval
      [OF weights_admitted bounded] by blast
  have controls_admitted: "comma_crt_mdd_admitted 0 controls"
    using consistent by (simp add: comma_crt_mdd_split_consistent_def)
  obtain control where control_eval:
      "comma_crt_mdd_eval phase controls=Some control"
    using comma_crt_mdd_admitted_eval_some[OF controls_admitted] by blast
  have value_consistent:
      "comma_crt_split_value_consistent control (Some D)"
    using consistent phase control_eval weight_eval
    by (auto simp: comma_crt_mdd_split_consistent_def)
  have stop_control: "control=Comma_CRT_Control_Stop"
    using value_consistent by (cases control) auto
  show thesis using control_eval weight_eval stop_control D
    by (rule that) (simp_all add: comma_crt_split_mdd_result_at_def)
qed

text \<open>The old concrete B1/B32 row publishers are retired.  The powered
owner composes source-selected control geometry and terminal weight diagrams
independently; no return-row table is a concrete dependency.\<close>

definition comma_semantic_b1_crt_power_result ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
      comma_semantic_b1_result option" where
  "comma_semantic_b1_crt_power_result k root phase =
    (if root<46 \<and> phase<924 then
       comma_crt_split_mdd_result_at phase
         (comma_crt_split_control (comma_semantic_b1_crt_power_split_action k root))
         (comma_crt_split_weight (comma_semantic_b1_crt_power_split_action k root))
     else None)"

lemma comma_semantic_b1_crt_power_result_exact:
  fixes k root phase :: nat
  assumes root: "root<46" and phase: "phase<924"
  shows "comma_semantic_b1_crt_power_result k root phase =
    Some (comma_semantic_b1_of_word (comma_orbit_word k phase root))"
proof -
  have split_exact:
      "comma_crt_split_mdd_result_at phase
        (comma_crt_split_control (comma_semantic_b1_crt_power_split_action k root))
        (comma_crt_split_weight (comma_semantic_b1_crt_power_split_action k root)) =
       Some (comma_semantic_b1_of_word (comma_orbit_word k phase root))"
    by (rule comma_semantic_b1_crt_power_split_action_exact[OF root phase])
  show ?thesis
    unfolding comma_semantic_b1_crt_power_result_def
    using split_exact root phase by simp
qed

corollary comma_semantic_b1_crt_b32_result_exact:
  assumes root: "root<46" and phase: "phase<924"
  shows "comma_semantic_b1_crt_power_result 5 root phase =
    Some (comma_semantic_b1_of_word (comma_orbit_word 5 phase root))"
  by (rule comma_semantic_b1_crt_power_result_exact[OF root phase])

theorem comma_semantic_b1_crt_b32_stop242:
  assumes roots_stop:
      "list_all (\<lambda>root. comma_crt_mdd_stop_weights_bounded242
        (comma_crt_split_weight (comma_semantic_b1_crt_power_split_action 5 root)))
          [0..<46]"
    and root: "root<46"
    and phase: "phase<924"
  obtains D where
    "comma_semantic_b1_crt_power_result 5 root phase =
      Some (Comma_Semantic_B1_Stop D)"
    "D\<le>242"
proof -
  have root_stop:
      "comma_crt_mdd_stop_weights_bounded242
        (comma_crt_split_weight (comma_semantic_b1_crt_power_split_action 5 root))"
    using roots_stop root by (auto simp: list_all_iff)
  have consistent: "comma_crt_mdd_split_consistent 0
      (comma_crt_split_control (comma_semantic_b1_crt_power_split_action 5 root))
      (comma_crt_split_weight (comma_semantic_b1_crt_power_split_action 5 root))"
    by (rule comma_semantic_b1_crt_power_split_action_consistent)
  obtain D where stopped_output:
      "comma_crt_split_mdd_result_at phase
        (comma_crt_split_control (comma_semantic_b1_crt_power_split_action 5 root))
        (comma_crt_split_weight (comma_semantic_b1_crt_power_split_action 5 root)) =
        Some (Comma_Semantic_B1_Stop D)"
    and bound: "D\<le>242"
    by (rule comma_crt_split_mdd_stop242_from_consistent[OF consistent root_stop phase])
  have provider_stop:
      "comma_semantic_b1_crt_power_result 5 root phase =
        Some (Comma_Semantic_B1_Stop D)"
    using stopped_output root phase
    by (simp add: comma_semantic_b1_crt_power_result_def)
  show thesis by (rule that[OF provider_stop bound])
qed

lemma comma_semantic_b1_crt_power_result_outside_domain:
  assumes outside: "\<not> (root<46 \<and> phase<924)"
  shows "comma_semantic_b1_crt_power_result k root phase=None"
  using outside by (auto simp: comma_semantic_b1_crt_power_result_def)

ML \<open>
  val checked = @{thms comma_semantic_b1_crt_power_split_action_consistent
    comma_semantic_b1_crt_power_split_action_exact
    comma_semantic_b1_crt_power_result_exact
    comma_semantic_b1_crt_b32_result_exact
    comma_semantic_b1_crt_b32_stop242
    comma_semantic_b1_crt_power_result_outside_domain};
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "published semantic B1 occurrence provider" checked;
\<close>

ML_file "semantic_b1_b32_projection.ML"
ML_file "semantic_b1_crt_conversion.ML"

local_setup \<open>fn lthy =>
  let
    val started = Time.now ();
    val engine = Comma_Semantic_B1_CRT_Conversion.make lthy;
    val smoke = #smoke_split_root engine ();
    val _ = if #validate engine smoke then ()
      else error "Published-occurrence split B32 root certificate failed validation";
    val {certificate = checked, roots} = #b32_stop242_all engine ();
    val published = Comma_Semantic_B1_B32_Projection.publish_local roots lthy;
    val _ = Comma_Proof_Dependency_Audit.require_native_clean published
      "Published-occurrence all-root split B32 Stop242 certificate" [checked];
    val _ = Comma_Proof_Profile.report
      ("Published-occurrence split CRT B32 roots=46 proof_ms=" ^
        Comma_Proof_Profile.elapsed_ms started ^ " " ^ #report engine ());
  in #2 (Local_Theory.note
      ((Binding.name "comma_semantic_b1_crt_b32_roots_stop242_checked", []),
      [checked]) published) end
\<close>

lemmas comma_semantic_b1_crt_b32_stop242_checked =
  comma_semantic_b1_crt_b32_stop242
    [OF comma_semantic_b1_crt_b32_roots_stop242_checked]

end
