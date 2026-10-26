theory Comma_Semantic_B1_Guarded_Port_Action
  imports Comma_Semantic_B1
begin

text \<open>
The finite source port is built from the decisive closed endpoint and the
guarded Near control formula.  Its producer does not run the packet evaluator
or construct a source-action list.  Packet equations below are refinement
theorems only.  Physical elapsed steps and weighted carry remain separate.
\<close>

definition comma_semantic_b1_next_port_action ::
    "comma_finite_position \<Rightarrow> comma_finite_position \<Rightarrow>
      comma_source_continuation_action" where
  "comma_semantic_b1_next_port_action source successor =
    (if comma_round_crossing source successor then
       Comma_Continuation_Exit (comma_source_continuation_base successor)
         (comma_source_continuation_shift successor)
     else Comma_Continuation_Goto (comma_source_continuation_base successor)
         (comma_source_continuation_shift successor))"

definition comma_semantic_b1_near_control_port_action ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> comma_source_continuation_action" where
  "comma_semantic_b1_near_control_port_action f delta h =
    (if f < 1 \<or> 9 < f \<or> h = 0 \<or> 540 < h then
       Comma_Continuation_Invalid
     else let d = (10 - h mod 10) mod 10 in
       if f < 9 then
         let low = 10 * d + f in
           if low + 1 < h then
             comma_semantic_b1_next_port_action (Comma_Near f delta h)
               (Comma_Near f delta (h - low))
           else if h = low + 1 then Comma_Continuation_Fork (f + 1) delta
           else comma_semantic_b1_next_port_action (Comma_Near f delta h)
             (Comma_Entry (f + 1) delta (low + 1 - h))
       else let same = 10 * d + 9; cross = 10 * d + 1 in
         if same < h then
           comma_semantic_b1_next_port_action (Comma_Near 9 delta h)
             (Comma_Near 9 delta (h - same))
         else if h \<le> cross then
           comma_semantic_b1_next_port_action (Comma_Near 9 delta h)
             (Comma_Entry 1 (Suc delta) (cross - h))
         else Comma_Continuation_Landmine delta)"

definition comma_semantic_b1_source_port_action ::
    "comma_finite_position \<Rightarrow> nat \<Rightarrow>
      comma_source_continuation_action" where
  "comma_semantic_b1_source_port_action source slot =
    (case comma_decisive_sector_target slot
        (comma_source_continuation_base source) of
       Comma_Near f delta h \<Rightarrow>
         comma_semantic_b1_near_control_port_action f delta h
     | Comma_Entry f delta offset \<Rightarrow> Comma_Continuation_Invalid)"

definition comma_semantic_b1_source_port_actions ::
    "comma_finite_position \<Rightarrow> comma_source_continuation_action list" where
  "comma_semantic_b1_source_port_actions source =
    map (comma_semantic_b1_source_port_action source)
      [0..<comma_decisive_sector_period
        (comma_source_continuation_base source)]"

lemma comma_semantic_b1_next_port_action_packet:
  "comma_semantic_b1_next_port_action source successor =
    comma_source_continuation_action_of_packet
      (source, Comma_Next successor)"
  by (simp add: comma_semantic_b1_next_port_action_def
      comma_source_continuation_action_of_packet.simps)

lemma comma_semantic_b1_near_control_port_action_packet:
  assumes sector: "1 \<le> f" "f \<le> 9"
    and headroom: "1 \<le> h" "h \<le> 540"
  shows "comma_semantic_b1_near_control_port_action f delta h =
    comma_source_continuation_action_of_packet
      (Comma_Near f delta h,
       comma_fast_step (r mod 924) (Comma_Near f delta h))"
  using sector headroom
  by (simp add: comma_semantic_b1_near_control_port_action_def
      comma_semantic_b1_next_port_action_packet comma_near_control_formula
      comma_fast_step_correct Let_def split: if_splits)

lemma comma_semantic_b1_source_port_action_packet:
  assumes admitted: "comma_round_admitted source"
  shows "comma_semantic_b1_source_port_action source slot =
    comma_source_continuation_action_of_packet
      (comma_decisive_endpoint_packet slot
        (comma_source_continuation_base source))"
proof -
  let ?base = "comma_source_continuation_base source"
  let ?target = "comma_decisive_sector_target slot ?base"
  have base_admitted: "comma_round_admitted ?base"
    by (rule comma_source_continuation_base_admitted[OF admitted])
  have packet_target:
    "fst (comma_decisive_endpoint_packet slot ?base) = ?target"
    by (simp add: comma_decisive_endpoint_packet_def Let_def)
  have target_admitted: "comma_round_admitted ?target"
    using comma_decisive_packet_target_admitted[OF base_admitted, of slot]
      packet_target by simp
  obtain f delta h where target: "?target = Comma_Near f delta h"
    by (rule comma_decisive_sector_target_near[OF base_admitted])
  have bounds: "1 \<le> f" "f \<le> 9" "1 \<le> h" "h \<le> 540"
    using target_admitted target by simp_all
  show ?thesis
    using target
      comma_semantic_b1_near_control_port_action_packet
        [OF bounds(1,2) bounds(3,4), of delta slot]
    by (simp add: comma_semantic_b1_source_port_action_def
        comma_decisive_endpoint_packet_def Let_def)
qed

lemma comma_semantic_b1_source_id_ports:
  assumes admitted: "comma_round_admitted source"
  shows "comma_source_continuation_id source =
    (comma_decisive_sector_period
       (comma_source_continuation_base source),
     comma_semantic_b1_source_port_actions source)"
proof -
  let ?base = "comma_source_continuation_base source"
  let ?period = "comma_decisive_sector_period ?base"
  have actions:
    "map (comma_semantic_b1_source_port_action source) [0..<?period] =
      map (\<lambda>slot. comma_source_continuation_action_of_packet
        (comma_decisive_endpoint_packet slot ?base)) [0..<?period]"
    by (rule map_cong[OF refl])
      (rule comma_semantic_b1_source_port_action_packet[OF admitted])
  show ?thesis
    using actions
    by (simp add: comma_source_continuation_id_def
        comma_semantic_b1_source_port_actions_def Let_def)
qed

ML \<open>
  val checked = @{thms comma_semantic_b1_near_control_port_action_packet
    comma_semantic_b1_source_port_action_packet
    comma_semantic_b1_source_id_ports};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Guarded semantic B1 port bridge depends on an oracle";
\<close>

end

