theory Comma_Future_Checked_Instance
  imports Comma_Future_Instance Comma_Fast_Control.Comma_Fast_Kernel
begin

text \<open>This is the concrete release computation. Keep it in a separate
session so a resource-limited build of the generic checker does not claim
this theorem. code_simp constructs kernel equations; no oracle or external
computation result is accepted. A timeout is an unfinished gate.\<close>

text \<open>Check the independent clauses of the certificate separately. This
makes the expensive 14,784-row successor check an observable proof gate apart
from candidate counts, rank bounds, source-list validation, and cycle return.
No aggregate-cost reduction is claimed. The final theorem below still proves
the exact original conjunction.\<close>

lemma comma_fast_boundary_run_numeral:
  "comma_fast_boundary_run rounds r source =
    (if rounds = 0 then None else
      (case comma_fast_round_aux 9 r source of
         Comma_Round_Cross target \<Rightarrow>
           comma_fast_boundary_run (rounds - 1) r target
       | Comma_Round_Fork a d \<Rightarrow> Some (Comma_Fork_At a d)
       | Comma_Round_Landmine d \<Rightarrow> Some (Comma_Landmine_At d)
       | Comma_Round_Invalid \<Rightarrow> None))"
  by (cases rounds; cases "comma_fast_round_aux 9 r source") simp_all

ML_file "../shared/selected_list_conversion.ML"
ML_file "../comma_future_rank_data/rank_table_lookup.ML"
ML_file "future_rank_check.ML"

lemma comma_future_instance_rank_check_computed:
  "comma_future_rank_check 28 comma_rank_candidate_on_valid"
  by (tactic \<open>Comma_Future_Rank_Check.tactic @{context}\<close>)

lemma comma_future_instance_ranked_count_computed:
  "length (filter (\<lambda>q. comma_rank_candidate_on_valid q \<noteq> None)
    comma_boundary_states) = 14470"
  by code_simp

lemma comma_future_instance_unranked_count_computed:
  "length (filter (\<lambda>q. comma_rank_candidate_on_valid q = None)
    comma_boundary_states) = 314"
  by code_simp

lemma comma_future_instance_rank_bound_computed:
  "list_all (\<lambda>q. case comma_rank_candidate_on_valid q of None \<Rightarrow> True
    | Some n \<Rightarrow> n \<le> 136) comma_boundary_states"
  by code_simp

lemma comma_future_instance_maximum_rank_computed:
  "list_ex (\<lambda>q. comma_rank_candidate_on_valid q = Some 136) comma_boundary_states"
  by code_simp

lemma comma_future_instance_survivor_sources_computed:
  "(case comma_fast_surviving_sources 314 28 comma_rank_candidate_on_valid
      (Comma_N,2,10) of
     None \<Rightarrow> False
   | Some sources \<Rightarrow> distinct sources \<and>
       list_all (\<lambda>q. comma_boundary_valid q \<and>
         comma_rank_candidate_on_valid q = None) sources)"
  by code_simp

lemma comma_future_instance_near_child_rank_computed:
  "comma_rank_candidate_on_valid (Comma_N,2,10) = None"
  by code_simp

lemma comma_future_instance_surviving_walk_computed:
  "comma_fast_surviving_walk 314 28 comma_rank_candidate_on_valid (Comma_N,2,10) =
    Some ((Comma_N,2,10),924)"
  by code_simp

theorem comma_future_instance_checked:
  "comma_future_instance_check"
  unfolding comma_future_instance_check_def
  using comma_future_instance_rank_check_computed
    comma_future_instance_ranked_count_computed
    comma_future_instance_unranked_count_computed
    comma_future_instance_rank_bound_computed
    comma_future_instance_maximum_rank_computed
    comma_future_instance_survivor_sources_computed
    comma_future_instance_near_child_rank_computed
    comma_future_instance_surviving_walk_computed
  by simp

corollary comma_future_concrete_rank_checked:
  "comma_rank_witness comma_total_children (set comma_boundary_states)
    comma_rank_candidate_on_valid"
  by (rule comma_future_instance_rank_sound[OF comma_future_instance_checked])

corollary comma_future_concrete_cycle_checked:
  "comma_surviving_delta_path comma_rank_candidate_on_valid 314
    (Comma_N,2,10) (Comma_N,2,10) 924"
  by (rule comma_future_instance_cycle_sound[OF comma_future_instance_checked])

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_future_instance_rank_check_computed
      comma_future_instance_ranked_count_computed
      comma_future_instance_unranked_count_computed
      comma_future_instance_rank_bound_computed
      comma_future_instance_maximum_rank_computed
      comma_future_instance_survivor_sources_computed
      comma_future_instance_near_child_rank_computed
      comma_future_instance_surviving_walk_computed
      comma_future_instance_checked comma_future_concrete_rank_checked
      comma_future_concrete_cycle_checked})
    then () else error "Concrete comma future check depends on an oracle";
\<close>
end
