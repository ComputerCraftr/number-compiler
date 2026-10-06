theory Comma_Semantic_B1_Power
  imports Comma_Semantic_B1_Columns
begin

ML_file "../comma_entry_arithmetic/proof_profile.ML"

text \<open>
This theory proves the weighted semantic composition law used by the grouped
CRT return-table publisher.  A left Live result advances the right action by
the completed-decade span; Stop and Invalid are absorbing.  The concrete
publisher and its table-level refinement are defined in the CRT theories.
\<close>

definition comma_semantic_b1_column_advance :: "nat \<Rightarrow> nat set \<Rightarrow> nat set" where
  "comma_semantic_b1_column_advance n column =
    {phase. phase < 924 \<and> (phase+n) mod 924 \<in> column}"

lemma comma_semantic_b1_column_advance_member:
  "phase \<in> comma_semantic_b1_column_advance n column \<longleftrightarrow>
    phase < 924 \<and> (phase+n) mod 924 \<in> column"
  by (simp add: comma_semantic_b1_column_advance_def)

definition comma_semantic_b1_weight_after ::
    "nat \<Rightarrow> comma_semantic_b1_result \<Rightarrow> comma_semantic_b1_result" where
  "comma_semantic_b1_weight_after n result =
    (case result of
       Comma_Semantic_B1_Stop D \<Rightarrow> Comma_Semantic_B1_Stop (9*n+D)
     | value \<Rightarrow> value)"

definition comma_semantic_b1_cell_result ::
    "nat \<Rightarrow> comma_semantic_b1_result \<Rightarrow>
      comma_semantic_b1_result \<Rightarrow> comma_semantic_b1_result" where
  "comma_semantic_b1_cell_result n left right =
    (case left of
       Comma_Semantic_B1_Live _ \<Rightarrow> comma_semantic_b1_weight_after n right
     | result \<Rightarrow> result)"

lemma comma_semantic_b1_cell_result_eq_word_then:
  "comma_semantic_word_then n (\<lambda>_ _. left) (\<lambda>_ _. right) phase root =
    comma_semantic_b1_cell_result n left right"
  by (cases left; cases right)
    (simp_all add: comma_semantic_word_then_def comma_semantic_b1_cell_result_def
      comma_semantic_b1_weight_after_def)

lemma comma_semantic_b1_first_stop_decades:
  "comma_semantic_b1_cell_result n (Comma_Semantic_B1_Live root)
      (Comma_Semantic_B1_Stop (comma_terminal_weight_encode height terminal)) =
    Comma_Semantic_B1_Stop
      (comma_terminal_weight_encode (n+height) terminal)"
  by (simp add: comma_semantic_b1_cell_result_def comma_semantic_b1_weight_after_def
      comma_terminal_weight_encode_def algebra_simps)

definition comma_semantic_b1_compose_left_row ::
    "nat \<Rightarrow> (nat \<Rightarrow> comma_semantic_b1_binding_row list) \<Rightarrow>
      comma_semantic_b1_binding_row \<Rightarrow> comma_semantic_b1_binding_row list" where
  "comma_semantic_b1_compose_left_row n right_tables left =
    (case snd left of
       Comma_Semantic_B1_Live root \<Rightarrow>
         map (\<lambda>right.
           (fst left \<inter> comma_semantic_b1_column_advance n (fst right),
            comma_semantic_b1_weight_after n (snd right))) (right_tables root)
     | result \<Rightarrow> [left])"

definition comma_semantic_b1_compose_raw_rows ::
    "nat \<Rightarrow> comma_semantic_b1_binding_row list \<Rightarrow>
      (nat \<Rightarrow> comma_semantic_b1_binding_row list) \<Rightarrow>
      comma_semantic_b1_binding_row list" where
  "comma_semantic_b1_compose_raw_rows n left_rows right_tables =
    concat (map (comma_semantic_b1_compose_left_row n right_tables) left_rows)"

lemma comma_semantic_b1_binding_table_row_at:
  assumes table: "comma_semantic_b1_binding_table_exact action 0 rows"
    and phase: "phase < 924"
  obtains row where "row \<in> set rows" "phase \<in> fst row"
    "snd row = action phase"
proof -
  have covered: "phase \<in> (\<Union> (fst ` set rows))"
    using table phase
    by (auto simp: comma_semantic_b1_binding_table_exact_def)
  then obtain row where row: "row \<in> set rows" and member: "phase \<in> fst row"
    by blast
  have exact: "comma_semantic_b1_binding_row_exact action 0 row"
    using table row by (auto simp: comma_semantic_b1_binding_table_exact_def)
  have row_value: "snd row = action phase"
    using exact member phase
    by (auto simp: comma_semantic_b1_binding_row_exact_def)
  show thesis by (rule that[OF row member row_value])
qed

lemma comma_semantic_b1_compose_raw_rows_sound_for_targets:
  fixes target :: "nat \<Rightarrow> bool"
  assumes left_table:
      "comma_semantic_b1_binding_table_exact (\<lambda>phase. left_action phase root) 0 left_rows"
    and right_tables:
      "\<And>next_root. target next_root \<Longrightarrow> comma_semantic_b1_binding_table_exact
        (\<lambda>phase. right_action phase next_root) 0 (right_rows next_root)"
    and live_targets:
      "\<And>phase next_root. phase < 924 \<Longrightarrow>
        left_action phase root = Comma_Semantic_B1_Live next_root \<Longrightarrow>
        target next_root"
    and row: "row \<in> set (comma_semantic_b1_compose_raw_rows n left_rows right_rows)"
    and phase: "phase < 924"
    and member: "phase \<in> fst row"
  shows "snd row = comma_semantic_word_then n left_action right_action phase root"
proof -
  obtain left where left: "left \<in> set left_rows"
    and row_left: "row \<in> set (comma_semantic_b1_compose_left_row n right_rows left)"
    using row by (auto simp: comma_semantic_b1_compose_raw_rows_def)
  have left_exact: "comma_semantic_b1_binding_row_exact
      (\<lambda>clock. left_action clock root) 0 left"
    using left_table left by (auto simp: comma_semantic_b1_binding_table_exact_def)
  have phase_left: "phase \<in> fst left"
    using member row_left
    by (cases "snd left")
      (auto simp: comma_semantic_b1_compose_left_row_def)
  have left_value: "snd left = left_action phase root"
    using left_exact phase phase_left
    by (auto simp: comma_semantic_b1_binding_row_exact_def)
  show ?thesis
  proof (cases "snd left")
    case (Comma_Semantic_B1_Live next_root)
    have left_is_live: "left_action phase root = Comma_Semantic_B1_Live next_root"
      using left_value Comma_Semantic_B1_Live by simp
    have target: "target next_root"
      by (rule live_targets[OF phase left_is_live])
    obtain right where right: "right \<in> set (right_rows next_root)"
      and row_eq:
        "row = (fst left \<inter>
          comma_semantic_b1_column_advance n (fst right),
          comma_semantic_b1_weight_after n (snd right))"
      using row_left Comma_Semantic_B1_Live
      by (auto simp: comma_semantic_b1_compose_left_row_def)
    have advanced_phase: "(phase+n) mod 924 \<in> fst right"
      using member row_eq phase
      by (auto simp: comma_semantic_b1_column_advance_def)
    have right_exact: "comma_semantic_b1_binding_row_exact
        (\<lambda>clock. right_action clock next_root) 0 right"
      using right_tables[OF target] right
      by (auto simp: comma_semantic_b1_binding_table_exact_def)
    have right_value:
      "snd right = right_action ((phase+n) mod 924) next_root"
      using right_exact advanced_phase by (auto simp: comma_semantic_b1_binding_row_exact_def)
    show ?thesis
      using row_eq right_value left_is_live
      by (simp add: comma_semantic_word_then_def comma_semantic_b1_weight_after_def
          split: comma_semantic_b1_result.splits)
  next
    case (Comma_Semantic_B1_Stop D)
    have row_eq: "row=left"
      using row_left Comma_Semantic_B1_Stop
      by (auto simp: comma_semantic_b1_compose_left_row_def)
    have left_is_stop: "left_action phase root=Comma_Semantic_B1_Stop D"
      using left_value Comma_Semantic_B1_Stop by simp
    show ?thesis using row_eq left_is_stop left_value Comma_Semantic_B1_Stop
      by (simp add: comma_semantic_word_then_def)
  next
    case Comma_Semantic_B1_Invalid
    have row_eq: "row=left"
      using row_left Comma_Semantic_B1_Invalid
      by (auto simp: comma_semantic_b1_compose_left_row_def)
    have left_is_invalid: "left_action phase root=Comma_Semantic_B1_Invalid"
      using left_value Comma_Semantic_B1_Invalid by simp
    show ?thesis using row_eq left_is_invalid left_value Comma_Semantic_B1_Invalid
      by (simp add: comma_semantic_word_then_def)
  qed
qed

lemma comma_semantic_b1_compose_raw_rows_sound:
  assumes left_table:
      "comma_semantic_b1_binding_table_exact (\<lambda>phase. left_action phase root) 0 left_rows"
    and right_tables:
      "\<And>next_root. comma_semantic_b1_binding_table_exact
        (\<lambda>phase. right_action phase next_root) 0 (right_rows next_root)"
    and row: "row \<in> set (comma_semantic_b1_compose_raw_rows n left_rows right_rows)"
    and phase: "phase < 924"
    and member: "phase \<in> fst row"
  shows "snd row = comma_semantic_word_then n left_action right_action phase root"
proof (rule comma_semantic_b1_compose_raw_rows_sound_for_targets
    [where target="\<lambda>_. True"])
  show "comma_semantic_b1_binding_table_exact (\<lambda>phase. left_action phase root) 0 left_rows"
    by (rule left_table)
  show "\<And>next_root. (\<lambda>_. True) next_root \<Longrightarrow>
      comma_semantic_b1_binding_table_exact
        (\<lambda>phase. right_action phase next_root) 0 (right_rows next_root)"
    using right_tables by simp
  show "\<And>phase next_root. phase < 924 \<Longrightarrow>
      left_action phase root = Comma_Semantic_B1_Live next_root \<Longrightarrow>
      (\<lambda>_. True) next_root"
    by simp
  show "row \<in> set (comma_semantic_b1_compose_raw_rows n left_rows right_rows)"
    by (rule row)
  show "phase < 924" by (rule phase)
  show "phase \<in> fst row" by (rule member)
qed

lemma comma_semantic_b1_compose_raw_rows_cover_for_targets:
  fixes target :: "nat \<Rightarrow> bool"
  assumes left_table:
      "comma_semantic_b1_binding_table_exact (\<lambda>phase. left_action phase root) 0 left_rows"
    and right_tables:
      "\<And>next_root. target next_root \<Longrightarrow> comma_semantic_b1_binding_table_exact
        (\<lambda>phase. right_action phase next_root) 0 (right_rows next_root)"
    and live_targets:
      "\<And>phase next_root. phase < 924 \<Longrightarrow>
        left_action phase root = Comma_Semantic_B1_Live next_root \<Longrightarrow>
        target next_root"
    and phase: "phase < 924"
  obtains row where "row \<in> set (comma_semantic_b1_compose_raw_rows n left_rows right_rows)"
    "phase \<in> fst row"
    "snd row = comma_semantic_word_then n left_action right_action phase root"
proof -
  obtain left where left: "left \<in> set left_rows" and phase_left: "phase \<in> fst left"
    and left_value: "snd left = left_action phase root"
    by (rule comma_semantic_b1_binding_table_row_at[OF left_table phase])
  show thesis
  proof (cases "snd left")
    case (Comma_Semantic_B1_Live next_root)
    have left_is_live: "left_action phase root=Comma_Semantic_B1_Live next_root"
      using left_value Comma_Semantic_B1_Live by simp
    have target_next: "target next_root"
      by (rule live_targets[OF phase left_is_live])
    let ?next = "(phase+n) mod 924"
    have next_bound: "?next < 924" by simp
    obtain right where right: "right \<in> set (right_rows next_root)"
      and next_member: "?next \<in> fst right"
      and right_value: "snd right = right_action ?next next_root"
      by (rule comma_semantic_b1_binding_table_row_at
        [OF right_tables[OF target_next] next_bound])
    let ?row = "(fst left \<inter>
      comma_semantic_b1_column_advance n (fst right),
      comma_semantic_b1_weight_after n (snd right))"
    have row_in_left:
      "?row \<in> set (comma_semantic_b1_compose_left_row n right_rows left)"
      using right Comma_Semantic_B1_Live
      by (simp add: comma_semantic_b1_compose_left_row_def)
    have row_member:
      "?row \<in> set (comma_semantic_b1_compose_raw_rows n left_rows right_rows)"
    proof -
      show ?thesis
        using left row_in_left
        by (auto simp: comma_semantic_b1_compose_raw_rows_def set_concat)
    qed
    have phase_member: "phase \<in> fst ?row"
      using phase_left next_member phase
      by (auto simp: comma_semantic_b1_column_advance_def)
    have output_eq:
      "snd ?row = comma_semantic_word_then n left_action right_action phase root"
      using left_is_live right_value
      by (simp add: comma_semantic_word_then_def comma_semantic_b1_weight_after_def
          split: comma_semantic_b1_result.splits)
    show thesis by (rule that[OF row_member phase_member output_eq])
  next
    case (Comma_Semantic_B1_Stop D)
    have row_in_left:
      "left \<in> set (comma_semantic_b1_compose_left_row n right_rows left)"
      using Comma_Semantic_B1_Stop by (simp add: comma_semantic_b1_compose_left_row_def)
    have row_member:
      "left \<in> set (comma_semantic_b1_compose_raw_rows n left_rows right_rows)"
      using left row_in_left
      by (auto simp: comma_semantic_b1_compose_raw_rows_def set_concat)
    have left_is_stop: "left_action phase root=Comma_Semantic_B1_Stop D"
      using left_value Comma_Semantic_B1_Stop by simp
    have output_eq:
      "snd left = comma_semantic_word_then n left_action right_action phase root"
      using left_value left_is_stop
      by (simp add: comma_semantic_word_then_def)
    show thesis by (rule that[OF row_member phase_left output_eq])
  next
    case Comma_Semantic_B1_Invalid
    have row_in_left:
      "left \<in> set (comma_semantic_b1_compose_left_row n right_rows left)"
      using Comma_Semantic_B1_Invalid by (simp add: comma_semantic_b1_compose_left_row_def)
    have row_member:
      "left \<in> set (comma_semantic_b1_compose_raw_rows n left_rows right_rows)"
      using left row_in_left
      by (auto simp: comma_semantic_b1_compose_raw_rows_def set_concat)
    have left_is_invalid: "left_action phase root=Comma_Semantic_B1_Invalid"
      using left_value Comma_Semantic_B1_Invalid by simp
    have output_eq:
      "snd left = comma_semantic_word_then n left_action right_action phase root"
      using left_value left_is_invalid
      by (simp add: comma_semantic_word_then_def)
    show thesis by (rule that[OF row_member phase_left output_eq])
  qed
qed

lemma comma_semantic_b1_compose_raw_rows_cover:
  assumes left_table:
      "comma_semantic_b1_binding_table_exact (\<lambda>phase. left_action phase root) 0 left_rows"
    and right_tables:
      "\<And>next_root. comma_semantic_b1_binding_table_exact
        (\<lambda>phase. right_action phase next_root) 0 (right_rows next_root)"
    and phase: "phase < 924"
  obtains row where "row \<in> set (comma_semantic_b1_compose_raw_rows n left_rows right_rows)"
    "phase \<in> fst row"
    "snd row = comma_semantic_word_then n left_action right_action phase root"
proof (rule comma_semantic_b1_compose_raw_rows_cover_for_targets
    [where target="\<lambda>_. True"])
  show "comma_semantic_b1_binding_table_exact (\<lambda>phase. left_action phase root) 0 left_rows"
    by (rule left_table)
  show "\<And>next_root. (\<lambda>_. True) next_root \<Longrightarrow>
      comma_semantic_b1_binding_table_exact
        (\<lambda>phase. right_action phase next_root) 0 (right_rows next_root)"
    using right_tables by simp
  show "\<And>phase next_root. phase < 924 \<Longrightarrow>
      left_action phase root = Comma_Semantic_B1_Live next_root \<Longrightarrow>
      (\<lambda>_. True) next_root"
    by simp
  show "phase < 924" by (rule phase)
qed

ML \<open>
  val checked = @{thms comma_semantic_b1_cell_result_eq_word_then
    comma_semantic_b1_first_stop_decades
    comma_semantic_b1_compose_raw_rows_sound_for_targets
    comma_semantic_b1_compose_raw_rows_cover_for_targets
    comma_semantic_b1_compose_raw_rows_sound
    comma_semantic_b1_compose_raw_rows_cover};
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Semantic B1 weighted composition" checked;
\<close>

end
