theory Comma_Future_M204_Source_Code
  imports Comma_Future_M204_Source_Bridge
begin

fun comma_future_m204_encode_source where
  "comma_future_m204_encode_source Comma_Semantic_B1_Invalid = 0"
| "comma_future_m204_encode_source (Comma_Semantic_B1_Live root) = Suc root"
| "comma_future_m204_encode_source (Comma_Semantic_B1_Stop J) = 47+J"

lemma comma_future_m204_physical_source_code:
  assumes valid: "comma_boundary_valid q"
  shows "comma_parametric_typed_mask_code
    (comma_phase_program_full_action_output (snd (snd q))
      (comma_decisive_endpoint_round (snd (snd q)) (comma_finite_initial q))) =
    comma_future_m204_encode_source
      (comma_semantic_b1_round_output (snd (snd q)) (comma_finite_initial q))"
proof -
  let ?phase = "snd (snd q)"
  let ?source = "comma_finite_initial q"
  have source: "comma_round_admitted ?source"
    using valid by (cases q) (auto simp: comma_boundary_valid_def comma_finite_initial_def)
  have initial_delta: "comma_round_delta ?source=0"
    using valid by (cases q) (simp add: comma_finite_initial_def comma_boundary_valid_def)
  obtain steps final event where close: "comma_round_close ?phase ?source=(steps,final,event)"
    by (cases "comma_round_close ?phase ?source") auto
  have final_delta: "comma_round_delta final=0"
    using comma_round_close_delta[OF close source] initial_delta by simp
  have exact: "comma_decisive_endpoint_round ?phase ?source=event"
    using comma_decisive_endpoint_round_refines_close[OF source] close by simp
  show ?thesis
  proof (cases event)
    case (Comma_Round_Fork a d)
    have facts: "d=0 \<and> 2\<le>a \<and> a\<le>9"
      using comma_future_m204_direct_fork_source[OF valid] close Comma_Round_Fork by simp
    show ?thesis using exact Comma_Round_Fork facts
      by (simp add: comma_semantic_b1_round_output_def comma_terminal_weight_encode_def
          comma_phase_program_full_action_terminal; arith)
  next
    case (Comma_Round_Landmine d)
    have "d=0" using comma_future_m204_direct_landmine_source[OF valid]
      close Comma_Round_Landmine by simp
    then show ?thesis using exact Comma_Round_Landmine
      by (simp add: comma_semantic_b1_round_output_def comma_terminal_weight_encode_def
          comma_phase_program_full_action_terminal)
  next
    case (Comma_Round_Cross target)
    obtain d h x where final: "final=Comma_Near 9 d h"
      and target: "target=Comma_Entry 1 (Suc d) x" and off: "x\<le>90"
      using comma_round_close_crossing_shape[OF close[unfolded Comma_Round_Cross]] by blast
    have "d=0" using final_delta final by simp
    have action: "comma_phase_program_full_action_output ?phase
      (Comma_Round_Cross (Comma_Entry 1 1 x)) =
      Comma_Phase_Rank_Mask_Continue (comma_offset_orbit x)"
      using comma_phase_program_full_action_exit_exact
        [where phase="?phase" and shift=0 and source="Comma_Entry 1 1 x"] off
      by (simp add: comma_decade_root_admitted_def)
    show ?thesis using exact Comma_Round_Cross target off \<open>d=0\<close> action
      by (simp add: comma_semantic_b1_round_output_def comma_decade_root_admitted_def)
  next
    case Comma_Round_Invalid
    then show ?thesis using exact
      by (simp add: comma_semantic_b1_round_output_def comma_phase_program_full_action_terminal)
  qed
qed

lemma comma_future_m204_source_live_bound:
  assumes live: "comma_semantic_b1_round_output phase source = Comma_Semantic_B1_Live root"
  shows "root < 46"
proof -
  obtain target where cross: "comma_decisive_endpoint_round phase source = Comma_Round_Cross target"
    using live by (cases "comma_decisive_endpoint_round phase source")
      (auto simp: comma_semantic_b1_round_output_def split: if_splits)
  show ?thesis using live cross comma_offset_orbit_bound
    by (cases target)
       (auto simp: comma_semantic_b1_round_output_def split: if_splits)
qed

lemma comma_future_m204_source_encoded_output:
  assumes valid: "comma_boundary_valid q"
    and code: "code = comma_parametric_typed_mask_code
      (comma_phase_program_full_action_output (snd (snd q))
        (comma_decisive_endpoint_round (snd (snd q)) (comma_finite_initial q)))"
  shows "comma_future_m204_source_output D q =
    (if code=0 then None else if code\<le>46 then
      (let value=D ((snd (snd q)+1) mod 924) (code-1)
       in Some (value mod 9,1+value div 9))
     else Some (code-47,0))"
  using valid code comma_future_m204_physical_source_code[OF valid]
  unfolding comma_future_m204_source_output_def
  by (cases "comma_semantic_b1_round_output (snd (snd q)) (comma_finite_initial q)")
     (auto simp: Let_def dest: comma_future_m204_source_live_bound split: if_splits)

end
