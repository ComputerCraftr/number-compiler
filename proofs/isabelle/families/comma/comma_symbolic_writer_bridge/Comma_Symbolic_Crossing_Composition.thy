theory Comma_Symbolic_Crossing_Composition
  imports Comma_Symbolic_Round_Cut
begin

text \<open>Compose two source-issued whole-round actions across an actual
9-to-1 crossing.  The point function descends into the demanded physical
interval; it does not construct a list of crossings or occurrences.\<close>

lemma comma_decisive_sector_target_delta:
  "comma_round_delta (comma_decisive_sector_target r source) = comma_round_delta source"
  by (cases source)
    (auto simp: comma_decisive_sector_target.simps Let_def
      split: option.splits prod.splits)

theorem comma_decisive_cross_shape:
  assumes source: "comma_round_admitted source"
    and result: "comma_decisive_endpoint_round r source = Comma_Round_Cross successor"
  shows "\<exists>offset\<le>90. successor = Comma_Entry 1 (Suc (comma_round_delta source)) offset"
  using source result
proof (induction r source arbitrary: successor rule: comma_decisive_endpoint_round.induct[case_names step])
  case (step r source)
  show ?case
  proof -
  note admitted = step.prems(1)
  obtain target move where packet:
    "comma_decisive_endpoint_packet r source = (target,move)"
    by (cases "comma_decisive_endpoint_packet r source") auto
  have target: "target = comma_decisive_sector_target r source"
    using packet by (simp add: comma_decisive_endpoint_packet_def Let_def)
  have target_admitted: "comma_round_admitted target"
    using comma_decisive_packet_target_admitted[OF admitted, of r] packet by simp
  have action: "comma_fast_step (r mod 924) target = move"
    using packet target by (simp add: comma_decisive_endpoint_packet_def Let_def)
  have round: "comma_decisive_endpoint_round r source =
    (case move of
       Comma_Next child => if comma_round_crossing target child then Comma_Round_Cross child
         else comma_decisive_endpoint_round r child
     | Comma_Fork a delta => Comma_Round_Fork a delta
     | Comma_Landmine delta => Comma_Round_Landmine delta
     | Comma_Invalid => Comma_Round_Invalid)"
    using comma_decisive_endpoint_round_packet[OF admitted, of r] packet by simp
  obtain child where move: "move = Comma_Next child"
    using round step.prems(2) by (cases move) auto
  have finite: "comma_finite_step (r mod 924) target = Comma_Next child"
    using action move by (simp only: comma_fast_step_correct)
  have delta: "comma_round_delta target = comma_round_delta source"
    using target by (simp only: comma_decisive_sector_target_delta)
  show ?case
  proof (cases "comma_round_crossing target child")
    case True
    have "successor = child" using round step.prems(2) move True by simp
    moreover obtain d h offset where "target = Comma_Near 9 d h"
      and "child = Comma_Entry 1 (Suc d) offset" and "offset \<le> 90"
      using comma_round_crossing_offset_bound[OF finite True] by blast
    ultimately show ?thesis using delta by auto
  next
    case False
    have next_admitted: "comma_round_admitted child"
      by (rule comma_round_next_admitted[OF target_admitted finite])
    have eq: "comma_decisive_endpoint_round r child = Comma_Round_Cross successor"
      using round step.prems(2) move False by simp
    have nd: "comma_round_delta child = comma_round_delta target"
      using comma_round_next_delta[OF target_admitted finite] False by simp
    have ih: "\<exists>offset\<le>90. successor = Comma_Entry 1 (Suc (comma_round_delta child)) offset"
      using step.IH[OF admitted target] action move False next_admitted eq by simp
    show ?thesis using ih nd delta by simp
  qed
  qed
qed

definition comma_symbolic_crossing_point ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_symbolic_crossing_point p offset next_offset j =
    (let source = Comma_Entry 1 0 offset;
         elapsed = fst (comma_symbolic_round_receipt p source)
     in if j \<le> elapsed then comma_symbolic_round_point p source j
        else comma_symbolic_round_point (Suc p) (Comma_Entry 1 0 next_offset) (j-elapsed))"

theorem comma_symbolic_crossing_cut_exact:
  fixes p offset next_offset elapsed j :: nat
  assumes exponent: "5 \<le> p" and offset: "offset \<le> 90"
    and crossing: "comma_symbolic_round_receipt p (Comma_Entry 1 0 offset) =
      (elapsed,Comma_Entry 1 1 next_offset,Comma_Round_Cross (Comma_Entry 1 1 next_offset))"
    and bound: "j \<le> elapsed + fst (comma_symbolic_round_receipt (Suc p) (Comma_Entry 1 0 next_offset))"
  shows "comma_literal_path j (comma_chart_value p (Comma_Entry 1 0 offset))
      (comma_symbolic_crossing_point p offset next_offset j) \<and>
    comma_literal_path
      (elapsed + fst (comma_symbolic_round_receipt (Suc p) (Comma_Entry 1 0 next_offset))-j)
      (comma_symbolic_crossing_point p offset next_offset j)
      (comma_chart_value (Suc p)
        (fst (snd (comma_symbolic_round_receipt (Suc p) (Comma_Entry 1 0 next_offset)))))"
proof -
  let ?source = "Comma_Entry 1 0 offset"
  let ?child = "Comma_Entry 1 0 next_offset"
  let ?duration = "fst (comma_symbolic_round_receipt (Suc p) ?child)"
  let ?last = "fst (snd (comma_symbolic_round_receipt (Suc p) ?child))"
  have source_admitted: "comma_round_admitted ?source" using offset by simp
  have source_cross: "comma_decisive_endpoint_round (p mod 924) ?source =
      Comma_Round_Cross (Comma_Entry 1 1 next_offset)"
    using comma_symbolic_round_receipt_control[of p ?source] crossing by simp
  have next_offset_bound: "next_offset \<le> 90"
    using comma_decisive_cross_shape[OF source_admitted source_cross] by auto
  have admitted: "comma_round_admitted ?source" "comma_round_admitted ?child"
    using offset next_offset_bound by simp_all
  have exponent_child: "5 \<le> Suc p" using exponent by simp
  have rebase: "comma_chart_value p (Comma_Entry 1 1 next_offset) =
      comma_chart_value (Suc p) ?child"
    by (simp add: comma_chart_value_def)
  have first: "comma_literal_path elapsed (comma_chart_value p ?source)
      (comma_chart_value (Suc p) ?child)"
    using comma_symbolic_round_receipt_physical[OF exponent admitted(1)] crossing rebase by simp
  have second: "comma_literal_path ?duration (comma_chart_value (Suc p) ?child)
      (comma_chart_value (Suc p) ?last)"
    by (rule comma_symbolic_round_receipt_physical[OF exponent_child admitted(2)])
  show ?thesis
  proof (cases "j \<le> elapsed")
    case True
    have first_cut: "comma_literal_path j (comma_chart_value p ?source)
        (comma_symbolic_round_point p ?source j) \<and>
      comma_literal_path (elapsed-j) (comma_symbolic_round_point p ?source j)
        (comma_chart_value (Suc p) ?child)"
      using comma_symbolic_round_cut_exact[OF admitted(1) exponent, where j=j] True crossing rebase by simp
    have length: "(elapsed-j)+?duration = elapsed+?duration-j" using True by arith
    have tail: "comma_literal_path (elapsed+?duration-j)
        (comma_symbolic_round_point p ?source j) (comma_chart_value (Suc p) ?last)"
      using comma_literal_path_append[OF conjunct2[OF first_cut] second] length by simp
    have point: "comma_symbolic_crossing_point p offset next_offset j = comma_symbolic_round_point p ?source j"
      using crossing True by (simp add: comma_symbolic_crossing_point_def Let_def)
    show ?thesis using first_cut tail point by simp
  next
    case False
    have child_bound: "j-elapsed \<le> ?duration" using bound by arith
    have second_cut: "comma_literal_path (j-elapsed) (comma_chart_value (Suc p) ?child)
        (comma_symbolic_round_point (Suc p) ?child (j-elapsed)) \<and>
      comma_literal_path (?duration-(j-elapsed))
        (comma_symbolic_round_point (Suc p) ?child (j-elapsed)) (comma_chart_value (Suc p) ?last)"
      by (rule comma_symbolic_round_cut_exact[OF admitted(2) exponent_child child_bound])
    have lengths: "elapsed+(j-elapsed)=j" "?duration-(j-elapsed)=elapsed+?duration-j"
      using False bound by arith+
    have prefix: "comma_literal_path j (comma_chart_value p ?source)
        (comma_symbolic_round_point (Suc p) ?child (j-elapsed))"
      using comma_literal_path_append[OF first conjunct1[OF second_cut]] lengths(1) by simp
    have point: "comma_symbolic_crossing_point p offset next_offset j =
        comma_symbolic_round_point (Suc p) ?child (j-elapsed)"
      using crossing False by (simp add: comma_symbolic_crossing_point_def Let_def)
    show ?thesis using second_cut prefix point lengths(2) by metis
  qed
qed

ML \<open>
  val checked = @{thms comma_decisive_cross_shape comma_symbolic_crossing_cut_exact};
  val _ = if null (Thm_Deps.all_oracles checked) then () else error "Crossing cut used an oracle";
  val _ = if Thm_Deps.has_skip_proof checked then error "Crossing cut contains skipped proofs" else ();
  val _ = Comma_Proof_Dependency_Audit.require_paths @{context}
    "Crossing cut excludes legacy authority"
    ["comma_round_close", "comma_finite_macro", "comma_terminal_weight_decode",
     "comma_phase_class_survival_lengths", "comma_python_first_terminal_walk"] checked;
\<close>
end
