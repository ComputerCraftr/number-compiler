theory Comma_Sector_Response_Check
  imports Comma_Sector_Response Comma_Frobenius_Entry.Comma_Frobenius_Entry
    Comma_Decade_Orbit.Comma_Phase_Mask_Arithmetic
begin

text \<open>Local branch equations for the symbolic response constructor.
This evaluator shares the existing arithmetic kernel and does not unfold a
response tree, traverse the 924 phase population, or assert mask coverage.\<close>

primrec comma_response_mask ::
  "comma_round_result \<Rightarrow> comma_sector_response \<Rightarrow> nat" where
  "comma_response_mask desired (Comma_Response_Leaf result)=
    (if desired=result then mask 924 else 0)"
| "comma_response_mask desired (Comma_Response_Phases f delta x children)=
    comma_indexed_phase_union
      (\<lambda>k r. comma_entry_alphabet_phase f r delta x=k)
      (map (comma_response_mask desired) children) OR
    (if desired=Comma_Round_Invalid then comma_phase_mask
      (\<lambda>r. length children\<le>comma_entry_alphabet_phase f r delta x) else 0)"

text \<open>The Invalid arm makes the projection total even for malformed
phase nodes with missing children. A complete symbolic constructor never
needs to fill missing branches with an assumed safe result. All mask joins
are functions of already constructed child masks, so the proof applies to
shared DAG implementations without expanding a response tree.\<close>
lemma comma_response_mask_member:
  "comma_phase_member (comma_response_mask desired response) r =
    (r<924 \<and> comma_response_value r response=desired)"
proof (induction response arbitrary: desired r)
  case (Comma_Response_Leaf result)
  then show ?case
    by (cases "desired=result") (auto simp: comma_phase_full_mask)
next
  case (Comma_Response_Phases f delta x children)
  have child: "\<And>k. k<length children \<Longrightarrow>
      comma_phase_member (comma_response_mask desired (children!k)) r =
      (r<924 \<and> comma_response_value r (children!k)=desired)"
    using Comma_Response_Phases.IH by (simp add: nth_mem)
  show ?case
    by (auto simp: comma_phase_member_or comma_indexed_phase_union_member
      comma_phase_mask_member child Let_def
      nth_map split: if_splits)
qed

lemma comma_entry_response_mask_refines:
  "comma_phase_member
    (comma_response_mask desired (comma_build_sector_response 9 (Comma_Entry 1 0 x))) r =
    (r<924 \<and> comma_fast_round_aux 9 r (Comma_Entry 1 0 x)=desired)"
  by (simp only: comma_response_mask_member comma_sector_response_refines)

lemma comma_sector_clause_refines:
  assumes sector: "1\<le>f" "f\<le>9" "x\<le>98"
    and phase: "comma_entry_alphabet_phase f r 0 x=k"
    and clause: "comma_fast_step 0
      (Comma_Near f 0 (comma_entry_alphabet_endpoint f x k))=event"
  shows "comma_fast_round_aux (Suc n) r (Comma_Entry f 0 x)=
    (case event of
      Comma_Next target \<Rightarrow>
        if comma_round_crossing
          (Comma_Near f 0 (comma_entry_alphabet_endpoint f x k)) target
        then Comma_Round_Cross target else comma_fast_round_aux n r target
    | Comma_Fork a d \<Rightarrow> Comma_Round_Fork a d
    | Comma_Landmine d \<Rightarrow> Comma_Round_Landmine d
    | Comma_Invalid \<Rightarrow> Comma_Round_Invalid)"
proof -
  have target: "comma_fast_sector_target r (Comma_Entry f 0 x)=
    Comma_Near f 0 (comma_entry_alphabet_endpoint f x k)"
    using sector phase by (simp only: comma_sector_entry_alphabet; simp)
  have step: "comma_fast_step (r mod 924)
    (Comma_Near f 0 (comma_entry_alphabet_endpoint f x k))=event"
    using clause by (simp only: comma_fast_step.simps)
  show ?thesis by (simp only: comma_response_round_successor target Let_def step)
qed


ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_indexed_phase_union_member comma_response_mask_member
      comma_entry_response_mask_refines comma_sector_clause_refines
      comma_guard_single_period comma_guard_join comma_guard_pattern_phase_class
      comma_guard_push_one_numeral comma_guard_full_phase
      comma_mask_and_zero comma_mask_and_self comma_mask_or_zero comma_mask_or_self
      comma_mask_and_swap comma_mask_or_swap
      comma_mask_phase_class_bounded comma_mask_and_full comma_mask_or_full
      comma_mask_and_preserves_bounded
      comma_guard_shifted_pattern comma_guard_drop_one_numeral
      comma_guard_take_num_one comma_guard_take_one_one comma_guard_take_one_numeral}) then ()
    else error "Symbolic sector mask refinement depends on an oracle";
\<close>

ML_file "sector_response_check.ML"

end
