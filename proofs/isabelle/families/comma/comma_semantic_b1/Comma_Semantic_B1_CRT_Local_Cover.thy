theory Comma_Semantic_B1_CRT_Local_Cover
imports Comma_Semantic_B1_CRT_Lift_Bindings
begin

ML \<open>
structure Comma_Local_Cover_Checkpoints =
struct
  val started = Time.now ()
  fun report stage =
    Comma_Proof_Profile.report
      (stage ^ " elapsed_ms=" ^
        LargeInt.toString (Time.toMilliseconds (Time.- (Time.now (), started))))
end
\<close>

text \<open>
The compact lift references certify local output fibers directly.  A parent
column is selected by its result binding; each terminal scope or lifted child
column must imply that selected column.  This avoids reconstructing the
accumulator-sensitive paired split action while retaining its geometry-to-
label obligation.
\<close>

fun comma_semantic_b1_crt_find_result_index ::
    "comma_semantic_b1_result list \<Rightarrow> comma_semantic_b1_result \<Rightarrow> nat option" where
  "comma_semantic_b1_crt_find_result_index [] result = None"
| "comma_semantic_b1_crt_find_result_index (head # tail) result =
    (if head = result then Some 0 else
      map_option Suc (comma_semantic_b1_crt_find_result_index tail result))"

definition comma_semantic_b1_crt_local_parent_column ::
    "comma_semantic_b1_crt_occurrence \<Rightarrow> comma_semantic_b1_result \<Rightarrow>
      comma_crt_column option" where
  "comma_semantic_b1_crt_local_parent_column parent result =
    (let columns = comma_semantic_b1_crt_occurrence_columns parent;
         beta = comma_semantic_b1_crt_occurrence_beta parent
     in if length columns = length beta then
          (case comma_semantic_b1_crt_find_result_index beta result of
             None \<Rightarrow> None
           | Some index \<Rightarrow>
               if index < length columns then
                 Some (comma_crt_shift
                   (comma_semantic_b1_crt_occurrence_rebase parent) (columns ! index))
               else None)
        else None)"

lemma comma_semantic_b1_crt_find_result_index_sound:
  assumes found:
    "comma_semantic_b1_crt_find_result_index beta result = Some index"
  shows "index < length beta \<and> beta ! index = result"
  using found
proof (induction beta arbitrary: index)
  case Nil
  then show ?case by simp
next
  case (Cons head tail)
  show ?case
  proof (cases "head = result")
    case True
    then show ?thesis using Cons.prems by simp
  next
    case False
    then obtain tail_index where tail_found:
        "comma_semantic_b1_crt_find_result_index tail result = Some tail_index"
      and index_eq: "index = Suc tail_index"
      using Cons.prems by (auto split: option.splits)
    have tail_facts: "tail_index < length tail \<and> tail ! tail_index = result"
      by (rule Cons.IH[OF tail_found])
    show ?thesis using tail_facts index_eq by simp
  qed
qed

definition comma_semantic_b1_crt_local_piece_covered ::
    "comma_semantic_b1_crt_occurrence \<Rightarrow> comma_crt_column \<Rightarrow>
      comma_semantic_b1_result \<Rightarrow> bool" where
  "comma_semantic_b1_crt_local_piece_covered parent candidate result =
    (case comma_semantic_b1_crt_local_parent_column parent result of
       None \<Rightarrow> comma_crt_admitted 0 candidate \<and>
         \<not> comma_crt_supported candidate
     | Some parent_column \<Rightarrow>
         comma_crt_admitted 0 candidate \<and>
         comma_crt_admitted 0 parent_column \<and>
         \<not> comma_crt_supported
           (comma_crt_apply Comma_CRT_And candidate
             (comma_crt_negate parent_column)))"

lemma comma_semantic_b1_crt_local_parent_column_some:
  assumes selected:
    "comma_semantic_b1_crt_local_parent_column parent result = Some column"
  obtains index where
    "index < length (comma_semantic_b1_crt_occurrence_columns parent)"
    "comma_semantic_b1_crt_occurrence_beta parent ! index = result"
    "column = comma_crt_shift (comma_semantic_b1_crt_occurrence_rebase parent)
       (comma_semantic_b1_crt_occurrence_columns parent ! index)"
proof -
  let ?columns = "comma_semantic_b1_crt_occurrence_columns parent"
  let ?beta = "comma_semantic_b1_crt_occurrence_beta parent"
  obtain index where find:
      "comma_semantic_b1_crt_find_result_index ?beta result = Some index"
    and selected_column:
      "index < length ?columns \<and>
       column = comma_crt_shift
         (comma_semantic_b1_crt_occurrence_rebase parent) (?columns ! index)"
    using selected
    by (auto simp: comma_semantic_b1_crt_local_parent_column_def Let_def
        split: if_splits option.splits)
  have result_at_index: "?beta ! index = result"
    using comma_semantic_b1_crt_find_result_index_sound[OF find] by blast
  show thesis
    by (rule that[OF conjunct1[OF selected_column] result_at_index
        conjunct2[OF selected_column]])
qed

ML \<open>
  val _ = Thm.consolidate @{thms comma_semantic_b1_crt_local_parent_column_some}
  val _ = Comma_Local_Cover_Checkpoints.report "Local cover stage=parent-selection"
\<close>

lemma comma_semantic_b1_crt_local_piece_covered_sound:
  assumes covered:
      "comma_semantic_b1_crt_local_piece_covered parent candidate result"
    and candidate_admitted: "comma_crt_admitted 0 candidate"
    and phase_bound: "phase < 924"
    and candidate_eval: "comma_crt_eval phase candidate"
  shows "\<exists>parent_column.
      comma_semantic_b1_crt_local_parent_column parent result = Some parent_column \<and>
      comma_crt_eval phase parent_column"
proof (cases "comma_semantic_b1_crt_local_parent_column parent result")
  case None
  then have unsupported: "\<not> comma_crt_supported candidate"
    using covered candidate_admitted
    by (simp add: comma_semantic_b1_crt_local_piece_covered_def)
  have supported: "comma_crt_supported candidate"
    by (rule comma_crt_eval_supported[OF candidate_admitted candidate_eval])
  show ?thesis using unsupported supported by contradiction
next
  case (Some parent_column)
  then have output_admitted: "comma_crt_admitted 0 parent_column"
    and no_bad_intersection:
      "\<not> comma_crt_supported
        (comma_crt_apply Comma_CRT_And candidate
          (comma_crt_negate parent_column))"
    using covered candidate_admitted
    by (auto simp: comma_semantic_b1_crt_local_piece_covered_def)
  have negated_admitted: "comma_crt_admitted 0 (comma_crt_negate parent_column)"
    by (rule comma_crt_negate_admitted[OF output_admitted])
  have difference_admitted:
      "comma_crt_admitted 0
        (comma_crt_apply Comma_CRT_And candidate (comma_crt_negate parent_column))"
    by (rule comma_crt_apply_admitted[OF candidate_admitted negated_admitted])
  have output_eval: "comma_crt_eval phase parent_column"
  proof (rule ccontr)
    assume outside: "\<not> comma_crt_eval phase parent_column"
    have difference_eval:
      "comma_crt_eval phase
        (comma_crt_apply Comma_CRT_And candidate (comma_crt_negate parent_column))"
      using comma_crt_apply_refines_boolean
        [OF candidate_admitted negated_admitted, where operation=Comma_CRT_And
          and phase=phase]
        comma_crt_negate_eval[OF output_admitted, of phase] candidate_eval outside
      by (simp add: comma_crt_boolean_value_def)
    have supported:
      "comma_crt_supported
        (comma_crt_apply Comma_CRT_And candidate (comma_crt_negate parent_column))"
      by (rule comma_crt_eval_supported[OF difference_admitted difference_eval])
    show False using no_bad_intersection supported by contradiction
  qed
  show ?thesis using Some output_eval by blast
qed

ML \<open>
  val _ = Thm.consolidate @{thms comma_semantic_b1_crt_local_piece_covered_sound}
  val _ = Comma_Local_Cover_Checkpoints.report "Local cover stage=piece-inclusion"
\<close>

lemma comma_semantic_b1_crt_local_columns_disjoint_at:
  assumes wellformed: "comma_semantic_b1_crt_occurrence_wellformed occurrence"
    and left_bound:
      "left < length (comma_semantic_b1_crt_occurrence_columns occurrence)"
    and right_bound:
      "right < length (comma_semantic_b1_crt_occurrence_columns occurrence)"
    and different: "left \<noteq> right"
    and phase_bound: "phase < 924"
  shows "\<not> (comma_crt_eval phase
      (comma_semantic_b1_crt_occurrence_columns occurrence ! left) \<and>
    comma_crt_eval phase
      (comma_semantic_b1_crt_occurrence_columns occurrence ! right))"
proof -
  let ?columns = "comma_semantic_b1_crt_occurrence_columns occurrence"
  have disjoint: "comma_semantic_b1_crt_occurrence_disjoint ?columns"
    using wellformed by (auto simp: comma_semantic_b1_crt_occurrence_wellformed_def)
  have left_entry:
      "(left, ?columns ! left) \<in>
        set (comma_semantic_b1_crt_occurrence_indexed_columns ?columns)"
  proof -
    have zip_bound:
        "left < length (zip [0..<length ?columns] ?columns)"
      using left_bound by simp
    have zip_nth:
        "zip [0..<length ?columns] ?columns ! left = (left, ?columns ! left)"
      using left_bound by (simp add: nth_zip)
    show ?thesis using nth_mem[OF zip_bound] zip_nth
      by (simp add: comma_semantic_b1_crt_occurrence_indexed_columns_def)
  qed
  have right_entry:
      "(right, ?columns ! right) \<in>
        set (comma_semantic_b1_crt_occurrence_indexed_columns ?columns)"
  proof -
    have zip_bound:
        "right < length (zip [0..<length ?columns] ?columns)"
      using right_bound by simp
    have zip_nth:
        "zip [0..<length ?columns] ?columns ! right = (right, ?columns ! right)"
      using right_bound by (simp add: nth_zip)
    show ?thesis using nth_mem[OF zip_bound] zip_nth
      by (simp add: comma_semantic_b1_crt_occurrence_indexed_columns_def)
  qed
  have column_sets_disjoint:
      "comma_crt_set (?columns ! left) \<inter> comma_crt_set (?columns ! right) = {}"
  proof -
    have indexed:
      "\<forall>l\<in>set (comma_semantic_b1_crt_occurrence_indexed_columns ?columns).
        \<forall>r\<in>set (comma_semantic_b1_crt_occurrence_indexed_columns ?columns).
          fst l \<noteq> fst r \<longrightarrow>
            comma_crt_set (snd l) \<inter> comma_crt_set (snd r) = {}"
      using disjoint by (simp only: comma_semantic_b1_crt_occurrence_disjoint_def)
    have selected_left:
      "\<forall>r\<in>set (comma_semantic_b1_crt_occurrence_indexed_columns ?columns).
        fst (left,?columns!left) \<noteq> fst r \<longrightarrow>
          comma_crt_set (snd (left,?columns!left)) \<inter>
            comma_crt_set (snd r) = {}"
      by (rule bspec[OF indexed left_entry])
    have selected_pair:
      "fst (left,?columns!left) \<noteq> fst (right,?columns!right) \<longrightarrow>
        comma_crt_set (snd (left,?columns!left)) \<inter>
          comma_crt_set (snd (right,?columns!right)) = {}"
      by (rule bspec[OF selected_left right_entry])
    show ?thesis using selected_pair different by simp
  qed
  show ?thesis
  proof
    assume both:
      "comma_crt_eval phase (?columns ! left) \<and>
       comma_crt_eval phase (?columns ! right)"
    have left_in: "phase \<in> comma_crt_set (?columns ! left)"
      using both phase_bound by (simp add: comma_crt_set_def)
    have right_in: "phase \<in> comma_crt_set (?columns ! right)"
      using both phase_bound by (simp add: comma_crt_set_def)
    show False using column_sets_disjoint left_in right_in by blast
  qed
qed

ML \<open>
  val _ = Thm.consolidate @{thms comma_semantic_b1_crt_local_columns_disjoint_at}
  val _ = Comma_Local_Cover_Checkpoints.report "Local cover stage=partition"
\<close>

lemma comma_semantic_b1_crt_local_parent_lookup_from_column:
  fixes parent :: comma_semantic_b1_crt_occurrence
  assumes wellformed: "comma_semantic_b1_crt_occurrence_wellformed parent"
    and clock_bound: "clock < 924"
    and index_bound:
      "index < length (comma_semantic_b1_crt_occurrence_columns parent)"
    and result_at_index:
      "comma_semantic_b1_crt_occurrence_beta parent ! index = result"
    and active:
      "comma_crt_eval clock
        (comma_crt_shift (comma_semantic_b1_crt_occurrence_rebase parent)
          (comma_semantic_b1_crt_occurrence_columns parent ! index))"
  shows "comma_semantic_b1_crt_occurrence_lookup parent clock = Some result"
proof -
  let ?columns = "comma_semantic_b1_crt_occurrence_columns parent"
  let ?beta = "comma_semantic_b1_crt_occurrence_beta parent"
  let ?rebase = "comma_semantic_b1_crt_occurrence_rebase parent"
  let ?phase = "(clock + ?rebase) mod 924"
  have covered: "comma_semantic_b1_crt_occurrence_covered ?columns"
    using wellformed by (simp add: comma_semantic_b1_crt_occurrence_wellformed_def)
  have phase_bound: "?phase < 924" by simp
  obtain selected where selected_bound: "selected < length ?columns"
    and selected_found:
      "comma_semantic_b1_crt_occurrence_find_index ?phase ?columns = Some selected"
    using comma_semantic_b1_crt_occurrence_find_index_total[OF phase_bound covered]
    by blast
  have selected_active:
      "comma_crt_eval ?phase (?columns ! selected)"
    using comma_semantic_b1_crt_occurrence_find_index_entry[OF selected_found]
      by blast
  have width: "length ?columns = length ?beta"
    using wellformed by (auto simp: comma_semantic_b1_crt_occurrence_wellformed_def)
  have index_admitted: "comma_crt_admitted 0 (?columns ! index)"
    using wellformed index_bound nth_mem[OF index_bound]
    by (auto simp: comma_semantic_b1_crt_occurrence_wellformed_def list_all_iff)
  have active_at_phase:
      "comma_crt_eval ?phase (?columns ! index)"
  proof -
    have shift_eval:
        "comma_crt_eval clock (comma_crt_shift ?rebase (?columns ! index)) =
         comma_crt_eval (clock+?rebase) (?columns ! index)"
      by (rule comma_crt_shift_refines[OF index_admitted])
    have periodic:
        "comma_crt_eval ?phase (?columns ! index) =
         comma_crt_eval (clock+?rebase) (?columns ! index)"
      using comma_crt_eval_periodic[OF index_admitted, of "clock+?rebase"]
      by simp
    show ?thesis using active shift_eval periodic by simp
  qed
  have same_index: "selected = index"
  proof (rule ccontr)
    assume different_indices: "selected \<noteq> index"
    have disjoint_eval:
      "\<not> (comma_crt_eval ?phase (?columns ! selected) \<and>
        comma_crt_eval ?phase (?columns ! index))"
      by (rule comma_semantic_b1_crt_local_columns_disjoint_at
        [OF wellformed selected_bound index_bound different_indices phase_bound])
    show False using disjoint_eval selected_active active_at_phase by blast
  qed
  have beta_bound: "selected < length ?beta" using selected_bound width by simp
  show ?thesis using selected_found beta_bound same_index result_at_index
    by (simp add: comma_semantic_b1_crt_occurrence_lookup_def)
qed

ML \<open>
  val _ = Thm.consolidate @{thms comma_semantic_b1_crt_local_parent_lookup_from_column}
  val _ = Comma_Local_Cover_Checkpoints.report "Local cover stage=lookup"
\<close>

lemma comma_semantic_b1_crt_local_piece_lookup:
  assumes parent_wellformed:
      "comma_semantic_b1_crt_occurrence_wellformed parent"
    and covered:
      "comma_semantic_b1_crt_local_piece_covered parent candidate result"
    and candidate_admitted: "comma_crt_admitted 0 candidate"
    and phase_bound: "phase < 924"
    and candidate_active: "comma_crt_eval phase candidate"
  shows "comma_semantic_b1_crt_occurrence_lookup parent phase = Some result"
proof -
  obtain parent_column where parent_selected:
      "comma_semantic_b1_crt_local_parent_column parent result = Some parent_column"
    and parent_active: "comma_crt_eval phase parent_column"
    using comma_semantic_b1_crt_local_piece_covered_sound
      [OF covered candidate_admitted phase_bound candidate_active] by blast
  obtain index where index_bound:
      "index < length (comma_semantic_b1_crt_occurrence_columns parent)"
    and result_at_index:
      "comma_semantic_b1_crt_occurrence_beta parent ! index = result"
    and parent_column_eq:
      "parent_column = comma_crt_shift
        (comma_semantic_b1_crt_occurrence_rebase parent)
        (comma_semantic_b1_crt_occurrence_columns parent ! index)"
    by (rule comma_semantic_b1_crt_local_parent_column_some[OF parent_selected])
  have selected_active:
      "comma_crt_eval phase
        (comma_crt_shift (comma_semantic_b1_crt_occurrence_rebase parent)
          (comma_semantic_b1_crt_occurrence_columns parent ! index))"
    using parent_active parent_column_eq by simp
  show ?thesis
    by (rule comma_semantic_b1_crt_local_parent_lookup_from_column
      [OF parent_wellformed phase_bound index_bound result_at_index selected_active])
qed

ML \<open>
  val _ = Thm.consolidate @{thms comma_semantic_b1_crt_local_piece_lookup}
  val _ = Comma_Local_Cover_Checkpoints.report "Local cover stage=piece-lookup"
\<close>

definition comma_semantic_b1_crt_lift_local_slot_valid ::
    "comma_finite_position list \<Rightarrow>
      (nat \<Rightarrow> comma_semantic_b1_crt_occurrence option) \<Rightarrow>
      comma_semantic_b1_crt_descriptor list \<Rightarrow>
      comma_crt_column list list \<Rightarrow>
      comma_finite_position \<Rightarrow> comma_semantic_b1_crt_occurrence \<Rightarrow>
      comma_semantic_b1_crt_lift_ref list \<Rightarrow>
      comma_semantic_b1_crt_lift_descriptor list \<Rightarrow> nat \<Rightarrow> bool" where
  "comma_semantic_b1_crt_lift_local_slot_valid sources occurrence_at
      occurrence_descriptors templates source parent refs descriptors slot \<longleftrightarrow>
    comma_semantic_b1_crt_lift_slot_valid sources occurrence_at occurrence_descriptors
      templates source parent refs descriptors slot \<and>
    (if slot < length refs then
       (case (refs ! slot, comma_semantic_b1_source_slot_action source slot) of
          (Comma_B1_Lift_Terminal_Ref ref_slot parent_index, action) \<Rightarrow>
            (case comma_semantic_b1_terminal_action_result action of
               None \<Rightarrow> False
             | Some result \<Rightarrow>
                 comma_semantic_b1_crt_local_piece_covered parent
                   (comma_crt_source_scope_column
                     (comma_decisive_sector_period
                       (comma_source_continuation_base source), slot)) result)
        | (Comma_B1_Lift_Goto_Ref ref_slot child_index lift_cid,
            Comma_Continuation_Goto child shift) \<Rightarrow>
            (if lift_cid < length descriptors then
               (case (occurrence_at child_index,
                   comma_semantic_b1_crt_lift_columns_option templates
                     (descriptors ! lift_cid)) of
                  (Some child_occurrence, Some lifted_columns) \<Rightarrow>
                    (let child_beta =
                       comma_semantic_b1_crt_occurrence_beta child_occurrence
                     in length lifted_columns = length child_beta \<and>
                       list_all (\<lambda>entry.
                         comma_semantic_b1_crt_local_piece_covered parent
                           (fst entry) (snd entry))
                         (zip lifted_columns child_beta))
                | _ \<Rightarrow> False)
             else False)
        | _ \<Rightarrow> False)
     else False)"

definition comma_semantic_b1_crt_lift_local_cover_witness ::
    "comma_finite_position list \<Rightarrow>
      (nat \<Rightarrow> comma_semantic_b1_crt_occurrence option) \<Rightarrow>
      comma_semantic_b1_crt_descriptor list \<Rightarrow>
      comma_crt_column list list \<Rightarrow>
      comma_finite_position \<Rightarrow> comma_semantic_b1_crt_occurrence \<Rightarrow>
      comma_semantic_b1_crt_lift_ref list \<Rightarrow>
      comma_semantic_b1_crt_lift_descriptor list \<Rightarrow> bool" where
  "comma_semantic_b1_crt_lift_local_cover_witness sources occurrence_at
      occurrence_descriptors templates source parent refs descriptors \<longleftrightarrow>
    source = comma_source_continuation_base source \<and>
    comma_round_admitted source \<and>
    comma_semantic_b1_crt_occurrence_binding_check parent \<and>
    distinct (comma_semantic_b1_crt_occurrence_beta parent) \<and>
    length occurrence_descriptors = length sources \<and>
    length refs = comma_decisive_sector_period source \<and>
    map comma_semantic_b1_crt_lift_ref_slot refs = [0..<length refs] \<and>
    list_all (comma_semantic_b1_crt_lift_local_slot_valid sources occurrence_at
      occurrence_descriptors templates source parent refs descriptors)
      [0..<length refs]"

lemma comma_semantic_b1_crt_lift_local_cover_rejects_truncated_refs:
  assumes truncated: "length refs < comma_decisive_sector_period source"
  shows "\<not> comma_semantic_b1_crt_lift_local_cover_witness sources occurrence_at
    occurrence_descriptors templates source parent refs descriptors"
  using truncated by (auto simp:
    comma_semantic_b1_crt_lift_local_cover_witness_def)

lemma comma_semantic_b1_crt_lift_local_terminal_lookup:
  fixes sources :: "comma_finite_position list"
    and occurrence_at :: "nat \<Rightarrow> comma_semantic_b1_crt_occurrence option"
    and occurrence_descriptors :: "comma_semantic_b1_crt_descriptor list"
    and templates :: "comma_crt_column list list"
    and source :: comma_finite_position
    and descriptors :: "comma_semantic_b1_crt_lift_descriptor list"
    and parent :: comma_semantic_b1_crt_occurrence
    and refs :: "comma_semantic_b1_crt_lift_ref list"
    and slot parent_index phase :: nat
    and ref :: comma_semantic_b1_crt_lift_ref
    and action :: comma_source_continuation_action
    and result :: comma_semantic_b1_result
  assumes normalized: "source = comma_source_continuation_base source"
    and source_period:
      "comma_decisive_sector_period (comma_source_continuation_base source)
        \<in> comma_semantic_b1_crt_source_periods"
    and slot_bound:
      "slot < comma_decisive_sector_period (comma_source_continuation_base source)"
    and ref_bound: "slot < length refs"
    and selected_slot: "phase mod
      comma_decisive_sector_period (comma_source_continuation_base source) = slot"
    and reference: "ref = Comma_B1_Lift_Terminal_Ref slot parent_index"
    and selected_ref: "refs ! slot = ref"
    and action:
      "comma_semantic_b1_source_slot_action source slot = action"
    and terminal:
      "comma_semantic_b1_terminal_action_result action = Some result"
    and slot_valid:
      "comma_semantic_b1_crt_lift_local_slot_valid sources occurrence_at
        occurrence_descriptors templates source parent refs descriptors slot"
    and parent_wellformed:
      "comma_semantic_b1_crt_occurrence_wellformed parent"
    and phase_bound: "phase < 924"
  shows "comma_semantic_b1_crt_occurrence_lookup parent phase = Some result"
proof -
  let ?period = "comma_decisive_sector_period (comma_source_continuation_base source)"
  let ?scope = "comma_crt_source_scope_column (?period, slot)"
  have covered:
      "comma_semantic_b1_crt_local_piece_covered parent ?scope result"
    using slot_valid normalized ref_bound slot_bound reference selected_ref action terminal
    by (auto simp: comma_semantic_b1_crt_lift_local_slot_valid_def
        split: option.splits)
  have scope_admitted: "comma_crt_admitted 0 ?scope"
    by (rule comma_semantic_b1_crt_lift_scope_admitted[OF source_period slot_bound])
  have scope_active: "comma_crt_eval phase ?scope"
    using comma_semantic_b1_crt_lift_scope_eval
      [OF source_period slot_bound phase_bound] selected_slot by simp
  show ?thesis
    by (rule comma_semantic_b1_crt_local_piece_lookup
      [OF parent_wellformed covered scope_admitted phase_bound scope_active])
qed

ML \<open>
  val _ = Thm.consolidate @{thms comma_semantic_b1_crt_lift_local_terminal_lookup}
  val _ = Comma_Local_Cover_Checkpoints.report "Local cover stage=terminal-lookup"
\<close>

lemma comma_semantic_b1_crt_lift_local_goto_lookup:
  fixes sources :: "comma_finite_position list"
    and occurrence_at :: "nat \<Rightarrow> comma_semantic_b1_crt_occurrence option"
    and occurrence_descriptors :: "comma_semantic_b1_crt_descriptor list"
    and templates :: "comma_crt_column list list"
    and source :: comma_finite_position
    and descriptors :: "comma_semantic_b1_crt_lift_descriptor list"
    and parent child_occurrence :: comma_semantic_b1_crt_occurrence
    and refs :: "comma_semantic_b1_crt_lift_ref list"
    and slot child_index lift_cid shift phase :: nat
    and child :: comma_finite_position
  assumes normalized: "source = comma_source_continuation_base source"
    and source_period:
      "comma_decisive_sector_period source \<in> comma_semantic_b1_crt_source_periods"
    and slot_bound: "slot < comma_decisive_sector_period source"
    and ref_bound: "slot < length refs"
    and selected_slot: "phase mod comma_decisive_sector_period source = slot"
    and reference:
      "refs ! slot = Comma_B1_Lift_Goto_Ref slot child_index lift_cid"
    and action:
      "comma_semantic_b1_source_slot_action source slot =
        Comma_Continuation_Goto child shift"
    and slot_valid:
      "comma_semantic_b1_crt_lift_local_slot_valid sources occurrence_at
        occurrence_descriptors templates source parent refs descriptors slot"
    and child_present: "occurrence_at child_index = Some child_occurrence"
    and child_wellformed:
      "comma_semantic_b1_crt_occurrence_wellformed child_occurrence"
    and parent_wellformed:
      "comma_semantic_b1_crt_occurrence_wellformed parent"
    and phase_bound: "phase < 924"
  shows "comma_semantic_b1_crt_occurrence_lookup parent phase =
    comma_semantic_b1_crt_occurrence_lookup child_occurrence
      ((phase + shift) mod 924)"
proof -
  let ?period = "comma_decisive_sector_period source"
  let ?child_columns = "comma_semantic_b1_crt_occurrence_columns child_occurrence"
  let ?child_beta = "comma_semantic_b1_crt_occurrence_beta child_occurrence"
  let ?descriptor = "descriptors ! lift_cid"
  let ?scope = "comma_crt_source_scope_column (?period, slot)"
  let ?net = "comma_semantic_b1_crt_lift_descriptor_net_shift ?descriptor"
  let ?lifted = "map (\<lambda>column. comma_crt_apply_shifted Comma_CRT_And
      ?net ?scope column) ?child_columns"
  let ?child_clock = "(phase + shift) mod 924"
  let ?child_phase =
      "(?child_clock + comma_semantic_b1_crt_occurrence_rebase child_occurrence) mod 924"
  have old_slot_valid:
      "comma_semantic_b1_crt_lift_slot_valid sources occurrence_at
        occurrence_descriptors templates source parent refs descriptors slot"
    using slot_valid by (simp add: comma_semantic_b1_crt_lift_local_slot_valid_def)
  have details:
      "child_index < length sources \<and>
       child_index < length occurrence_descriptors \<and>
       sources ! child_index = comma_source_continuation_base child \<and>
       lift_cid < length descriptors \<and>
       fst (occurrence_descriptors ! child_index) =
         comma_semantic_b1_crt_lift_descriptor_template_cid ?descriptor \<and>
       comma_semantic_b1_crt_lift_descriptor_period ?descriptor = ?period \<and>
       comma_semantic_b1_crt_lift_descriptor_slot ?descriptor = slot \<and>
       comma_semantic_b1_crt_lift_descriptor_template_cid ?descriptor < length templates \<and>
       comma_semantic_b1_crt_occurrence_columns child_occurrence =
         templates ! comma_semantic_b1_crt_lift_descriptor_template_cid ?descriptor \<and>
       comma_semantic_b1_crt_lift_descriptor_net_shift ?descriptor =
         (shift + comma_semantic_b1_crt_occurrence_rebase child_occurrence) mod 924 \<and>
       comma_semantic_b1_crt_lift_descriptor_valid templates ?descriptor"
    using old_slot_valid reference action child_present normalized ref_bound slot_bound
    by (auto simp: comma_semantic_b1_crt_lift_slot_valid_def
        split: option.splits prod.splits)
  have resolved_columns:
      "comma_semantic_b1_crt_lift_columns_option templates ?descriptor = Some ?lifted"
    using details source_period slot_bound
    by (simp add: comma_semantic_b1_crt_lift_columns_option_def)
  have covered_rows:
      "length ?lifted = length ?child_beta \<and>
       list_all (\<lambda>entry. comma_semantic_b1_crt_local_piece_covered parent
          (fst entry) (snd entry)) (zip ?lifted ?child_beta)"
    using slot_valid reference action child_present ref_bound resolved_columns details
      normalized
    by (simp add: comma_semantic_b1_crt_lift_local_slot_valid_def Let_def)
  have child_width: "length ?child_columns = length ?child_beta"
    and child_admitted: "list_all (comma_crt_admitted 0) ?child_columns"
    and child_covered: "comma_semantic_b1_crt_occurrence_covered ?child_columns"
    using child_wellformed
    by (auto simp: comma_semantic_b1_crt_occurrence_wellformed_def)
  have child_phase_bound: "?child_phase < 924" by simp
  obtain selected where selected_bound: "selected < length ?child_columns"
    and selected_found:
      "comma_semantic_b1_crt_occurrence_find_index ?child_phase ?child_columns =
        Some selected"
    using comma_semantic_b1_crt_occurrence_find_index_total
      [OF child_phase_bound child_covered] by blast
  have selected_active:
      "comma_crt_eval ?child_phase (?child_columns ! selected)"
    using comma_semantic_b1_crt_occurrence_find_index_entry[OF selected_found]
    by blast
  have beta_bound: "selected < length ?child_beta"
    using selected_bound child_width by simp
  have child_value:
      "comma_semantic_b1_crt_occurrence_lookup child_occurrence ?child_clock =
        Some (?child_beta ! selected)"
    using selected_found beta_bound
    by (simp add: comma_semantic_b1_crt_occurrence_lookup_def)
  have selected_admitted: "comma_crt_admitted 0 (?child_columns ! selected)"
    using child_admitted selected_bound nth_mem[OF selected_bound]
    by (auto simp: list_all_iff)
  have lifted_index:
      "?lifted ! selected =
        comma_crt_apply_shifted Comma_CRT_And ?net ?scope
          (?child_columns ! selected)"
    using selected_bound by (simp add: nth_map)
  have lifted_active:
      "comma_crt_eval phase (?lifted ! selected)"
  proof -
    have column_eval:
        "comma_crt_eval phase
            (comma_crt_apply_shifted Comma_CRT_And ?net ?scope
              (?child_columns ! selected)) =
          (phase mod ?period = slot \<and>
            comma_crt_eval (phase + ?net) (?child_columns ! selected))"
      by (rule comma_semantic_b1_crt_lift_column_eval
        [OF source_period slot_bound selected_admitted phase_bound])
    have phase_eq:
        "?child_phase = (phase + ?net) mod 924"
      using details
      by (simp add: mod_add_left_eq mod_add_right_eq add.assoc)
    have periodic:
        "comma_crt_eval ?child_phase (?child_columns ! selected) =
          comma_crt_eval (phase + ?net) (?child_columns ! selected)"
      using comma_crt_eval_periodic[OF selected_admitted, of "phase + ?net"]
        phase_eq by simp
    show ?thesis using column_eval lifted_index periodic selected_slot selected_active
      by simp
  qed
  have lifted_bound: "selected < length ?lifted"
    using selected_bound by simp
  have zipped_bound: "selected < length (zip ?lifted ?child_beta)"
    using lifted_bound covered_rows by simp
  have zipped_nth:
      "zip ?lifted ?child_beta ! selected =
        (?lifted ! selected, ?child_beta ! selected)"
    using lifted_bound covered_rows by (simp add: nth_zip)
  have zipped_member:
      "(?lifted ! selected, ?child_beta ! selected) \<in> set (zip ?lifted ?child_beta)"
    using nth_mem[OF zipped_bound] zipped_nth by simp
  have row_covered:
      "comma_semantic_b1_crt_local_piece_covered parent
        (?lifted ! selected) (?child_beta ! selected)"
    using covered_rows zipped_member by (auto simp: list_all_iff)
  have lifted_admitted:
      "comma_crt_admitted 0 (?lifted ! selected)"
    using row_covered
    by (auto simp: comma_semantic_b1_crt_local_piece_covered_def
        split: option.splits)
  have parent_value:
      "comma_semantic_b1_crt_occurrence_lookup parent phase =
        Some (?child_beta ! selected)"
    by (rule comma_semantic_b1_crt_local_piece_lookup
      [OF parent_wellformed row_covered lifted_admitted phase_bound lifted_active])
  show ?thesis using parent_value child_value by simp
qed

ML \<open>
  val _ = Thm.consolidate @{thms comma_semantic_b1_crt_lift_local_goto_lookup}
  val _ = Comma_Local_Cover_Checkpoints.report "Local cover stage=goto-lookup"
\<close>

theorem comma_semantic_b1_crt_lift_local_cover_candidate_matches:
  fixes sources :: "comma_finite_position list"
    and occurrence_at :: "nat \<Rightarrow> comma_semantic_b1_crt_occurrence option"
    and occurrence_descriptors :: "comma_semantic_b1_crt_descriptor list"
    and templates :: "comma_crt_column list list"
    and children :: "comma_finite_position \<Rightarrow> comma_semantic_b1_crt_occurrence option"
    and source :: comma_finite_position
    and parent :: comma_semantic_b1_crt_occurrence
    and refs :: "comma_semantic_b1_crt_lift_ref list"
    and descriptors :: "comma_semantic_b1_crt_lift_descriptor list"
  assumes witness:
      "comma_semantic_b1_crt_lift_local_cover_witness sources occurrence_at
        occurrence_descriptors templates source parent refs descriptors"
    and parent_wellformed:
      "comma_semantic_b1_crt_occurrence_wellformed parent"
    and children_wellformed:
      "\<And>i child. i < length sources \<Longrightarrow>
        occurrence_at i = Some child \<Longrightarrow>
        comma_semantic_b1_crt_occurrence_wellformed child"
    and children_resolve:
      "\<And>i. i < length sources \<Longrightarrow>
        children (sources ! i) = occurrence_at i"
  shows "comma_semantic_b1_crt_occurrence_candidate_matches children source parent"
proof -
  let ?period = "comma_decisive_sector_period source"
  have source_base: "source = comma_source_continuation_base source"
    and source_admitted: "comma_round_admitted source"
    and refs_length: "length refs = ?period"
    and refs_slots:
      "map comma_semantic_b1_crt_lift_ref_slot refs = [0..<length refs]"
    and slots_valid:
      "list_all (comma_semantic_b1_crt_lift_local_slot_valid sources occurrence_at
        occurrence_descriptors templates source parent refs descriptors)
        [0..<length refs]"
    using witness by (auto simp: comma_semantic_b1_crt_lift_local_cover_witness_def)
  have source_period_base:
      "comma_decisive_sector_period (comma_source_continuation_base source)
        \<in> comma_semantic_b1_crt_source_periods"
    by (rule comma_semantic_b1_generated_source_period_six[OF source_admitted])
  have source_period: "?period \<in> comma_semantic_b1_crt_source_periods"
    using source_period_base source_base by simp
  have period_positive: "0 < ?period"
    using source_period by (auto simp: comma_semantic_b1_crt_source_periods_def)
  show ?thesis
    unfolding comma_semantic_b1_crt_occurrence_candidate_matches_def
  proof (intro allI impI)
    fix clock :: nat
    assume clock_bound: "clock < 924"
    let ?slot = "clock mod ?period"
    let ?ref = "refs ! ?slot"
    have slot_bound: "?slot < ?period" using period_positive by simp
    have ref_bound: "?slot < length refs" using slot_bound refs_length by simp
    have slots_at:
        "(map comma_semantic_b1_crt_lift_ref_slot refs) ! ?slot =
          [0..<length refs] ! ?slot"
      by (rule arg_cong[OF refs_slots, where f="\<lambda>xs. xs ! ?slot"])
    have ref_slot:
        "comma_semantic_b1_crt_lift_ref_slot ?ref = ?slot"
      using slots_at ref_bound by (simp add: nth_map nth_upt)
    have slot_member: "?slot \<in> set [0..<length refs]"
      using ref_bound by simp
    have selected_slot_valid:
        "comma_semantic_b1_crt_lift_local_slot_valid sources occurrence_at
          occurrence_descriptors templates source parent refs descriptors ?slot"
      using slots_valid slot_member by (simp add: list_all_iff)
    have base_slot_valid:
        "comma_semantic_b1_crt_lift_slot_valid sources occurrence_at
          occurrence_descriptors templates source parent refs descriptors ?slot"
      using selected_slot_valid
      by (simp add: comma_semantic_b1_crt_lift_local_slot_valid_def)
    show "comma_semantic_b1_crt_occurrence_lookup parent clock =
      comma_semantic_b1_crt_occurrence_local_step children source clock"
    proof (cases "\<exists>child shift.
        comma_semantic_b1_source_slot_action source ?slot =
          Comma_Continuation_Goto child shift")
      case True
      then obtain child shift where action:
          "comma_semantic_b1_source_slot_action source ?slot =
            Comma_Continuation_Goto child shift"
        by blast
      obtain child_index lift_cid where reference:
          "?ref = Comma_B1_Lift_Goto_Ref ?slot child_index lift_cid"
        using base_slot_valid ref_slot ref_bound slot_bound action source_base
        by (cases ?ref)
          (auto simp: comma_semantic_b1_crt_lift_slot_valid_def
            split: option.splits)
      have child_present: "occurrence_at child_index \<noteq> None"
        using base_slot_valid reference action source_base ref_bound slot_bound
        by (auto simp: comma_semantic_b1_crt_lift_slot_valid_def
            split: option.splits prod.splits)
      obtain child_occurrence where child_at:
          "occurrence_at child_index = Some child_occurrence"
        using child_present by (cases "occurrence_at child_index") auto
      have index_bound: "child_index < length sources"
        using base_slot_valid reference action source_base ref_bound slot_bound
        by (auto simp: comma_semantic_b1_crt_lift_slot_valid_def)
      have child_wellformed:
          "comma_semantic_b1_crt_occurrence_wellformed child_occurrence"
        by (rule children_wellformed[OF index_bound child_at])
      have source_child:
          "sources ! child_index = comma_source_continuation_base child"
        using base_slot_valid reference action child_at source_base ref_bound slot_bound
        by (auto simp: comma_semantic_b1_crt_lift_slot_valid_def
            split: option.splits prod.splits)
      have decrease:
          "shift = 0 \<and> child = comma_source_continuation_base child \<and>
           comma_round_admitted child \<and>
           9-comma_sector_number child < 9-comma_sector_number source"
        by (rule comma_semantic_b1_crt_occurrence_goto_decreases
          [OF source_base source_admitted slot_bound action])
      have source_child_eq: "sources ! child_index = child"
        using source_child decrease by simp
      have resolved_child:
          "children child = Some child_occurrence"
        using children_resolve[OF index_bound] child_at source_child_eq by simp
      have selected_slot: "clock mod ?period = ?slot" by simp
      have parent_lookup:
          "comma_semantic_b1_crt_occurrence_lookup parent clock =
            comma_semantic_b1_crt_occurrence_lookup child_occurrence
              ((clock + shift) mod 924)"
        by (rule comma_semantic_b1_crt_lift_local_goto_lookup
          [OF source_base source_period slot_bound ref_bound
            selected_slot reference action selected_slot_valid child_at child_wellformed
            parent_wellformed clock_bound])
      have local_step:
          "comma_semantic_b1_crt_occurrence_local_step children source clock =
            comma_semantic_b1_crt_occurrence_lookup child_occurrence
              ((clock + shift) mod 924)"
        using clock_bound action resolved_child selected_slot
        by (simp add: comma_semantic_b1_crt_occurrence_local_step_def)
      show ?thesis using parent_lookup local_step by simp
    next
      case False
      obtain result where terminal:
          "comma_semantic_b1_terminal_action_result
            (comma_semantic_b1_source_slot_action source ?slot) = Some result"
        using comma_semantic_b1_terminal_action_result_present[OF False] by blast
      obtain parent_index where reference:
          "?ref = Comma_B1_Lift_Terminal_Ref ?slot parent_index"
        using base_slot_valid ref_slot ref_bound slot_bound terminal source_base
        by (cases ?ref)
          (auto simp: comma_semantic_b1_crt_lift_slot_valid_def
            split: option.splits comma_source_continuation_action.splits)
      have selected_ref: "refs ! ?slot = ?ref" by simp
      have selected_slot: "clock mod ?period = ?slot" by simp
      have base_slot_bound:
          "?slot < comma_decisive_sector_period (comma_source_continuation_base source)"
        using slot_bound source_base by simp
      have base_selected_slot:
          "clock mod comma_decisive_sector_period
             (comma_source_continuation_base source) = ?slot"
        using selected_slot source_base by simp
      have parent_lookup:
          "comma_semantic_b1_crt_occurrence_lookup parent clock = Some result"
        by (rule comma_semantic_b1_crt_lift_local_terminal_lookup
          [OF source_base source_period_base base_slot_bound ref_bound base_selected_slot reference
            selected_ref _ terminal selected_slot_valid parent_wellformed clock_bound])
          simp
      have local_step:
          "comma_semantic_b1_crt_occurrence_local_step children source clock =
            Some result"
        using clock_bound terminal selected_slot
        by (cases "comma_semantic_b1_source_slot_action source ?slot")
          (auto simp: comma_semantic_b1_crt_occurrence_local_step_def
            split: comma_source_continuation_action.splits)
      show ?thesis using parent_lookup local_step by simp
    qed
  qed
qed

ML \<open>
  val _ = Thm.consolidate @{thms
    comma_semantic_b1_crt_lift_local_cover_rejects_truncated_refs
    comma_semantic_b1_crt_lift_local_terminal_lookup
    comma_semantic_b1_crt_lift_local_goto_lookup
    comma_semantic_b1_crt_lift_local_cover_candidate_matches}
  val _ = Comma_Local_Cover_Checkpoints.report "Local cover stage=candidate-matches"
\<close>


ML \<open>
val _ =
  if null (Thm_Deps.all_oracles @{thms
    comma_semantic_b1_crt_find_result_index_sound
    comma_semantic_b1_crt_local_parent_column_some
    comma_semantic_b1_crt_local_piece_covered_sound
    comma_semantic_b1_crt_local_columns_disjoint_at
    comma_semantic_b1_crt_local_parent_lookup_from_column
    comma_semantic_b1_crt_local_piece_lookup
    comma_semantic_b1_crt_lift_local_cover_rejects_truncated_refs
    comma_semantic_b1_crt_lift_local_terminal_lookup
    comma_semantic_b1_crt_lift_local_goto_lookup
    comma_semantic_b1_crt_lift_local_cover_candidate_matches
  }) then ()
  else error "Comma_Semantic_B1_CRT_Local_Cover local oracle audit failed"
\<close>
end
