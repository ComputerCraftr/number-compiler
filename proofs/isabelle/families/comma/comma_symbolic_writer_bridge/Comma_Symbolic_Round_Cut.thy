theory Comma_Symbolic_Round_Cut
  imports Comma_Symbolic_Round_Physical
begin

text \<open>Demanded physical points descend through the authenticated source
sector, then through its ordered successor. No event history, traversal fuel,
or independently supplied receipt is used to select the cut.\<close>

function comma_symbolic_round_point ::
  "nat \<Rightarrow> comma_finite_position \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_symbolic_round_point p source j =
    (if comma_round_admitted source then
      (let (target,event) = comma_decisive_endpoint_packet (p mod 924) source;
           elapsed = comma_symbolic_sector_duration p source
       in if j \<le> elapsed then comma_symbolic_sector_point p source j
          else (case event of
            Comma_Next successor \<Rightarrow>
              if comma_round_crossing target successor then comma_chart_value p successor
              else comma_symbolic_round_point p successor (j - Suc elapsed)
          | _ \<Rightarrow> comma_symbolic_sector_point p source j))
     else comma_chart_value p source)"
  by pat_completeness auto
termination
  apply (relation "measure (\<lambda>(p,source,j). 9-comma_sector_number source)")
   apply simp
  apply (clarsimp simp: Let_def comma_decisive_endpoint_packet_def split: prod.splits)
  by (metis comma_decisive_endpoint_successor_decreases mod_mod_trivial)

declare comma_symbolic_round_point.simps [simp del]

lemma comma_symbolic_round_sector_remainder:
  assumes source: "comma_round_admitted source" and exponent: "5 \<le> p"
    and packet: "comma_decisive_endpoint_packet (p mod 924) source = (target,event)"
  shows "comma_literal_path
      (fst (comma_symbolic_round_receipt p source) - comma_symbolic_sector_duration p source)
      (comma_chart_value p target)
      (comma_chart_value p (fst (snd (comma_symbolic_round_receipt p source))))"
proof (cases event)
  case (Comma_Next successor)
  have packet_next: "comma_decisive_endpoint_packet (p mod 924) source =
      (target,Comma_Next successor)" using packet Comma_Next by simp
  have successor: "comma_round_admitted successor"
    and edge: "comma_literal_path 1 (comma_chart_value p target) (comma_chart_value p successor)"
    using comma_symbolic_decisive_next_physical[OF source exponent packet_next] by blast+
  show ?thesis
  proof (cases "comma_round_crossing target successor")
    case True
    have result: "comma_symbolic_round_receipt p source =
        (Suc (comma_symbolic_sector_duration p source),successor,Comma_Round_Cross successor)"
      using source packet Comma_Next True
      by (subst comma_symbolic_round_receipt.simps) (simp add: Let_def)
    show ?thesis using edge result by simp
  next
    case False
    obtain n last outcome where tail:
      "comma_symbolic_round_receipt p successor = (n,last,outcome)"
      by (cases "comma_symbolic_round_receipt p successor") (auto split: prod.splits)
    have result: "comma_symbolic_round_receipt p source =
        (Suc (comma_symbolic_sector_duration p source)+n,last,outcome)"
      using source packet Comma_Next False tail
      by (subst comma_symbolic_round_receipt.simps) (simp add: Let_def)
    have rest: "comma_literal_path n (comma_chart_value p successor) (comma_chart_value p last)"
      using comma_symbolic_round_receipt_physical[OF exponent successor] tail by simp
    show ?thesis using comma_literal_path_append[OF edge rest] result by simp
  qed
next
  case (Comma_Fork a delta)
  have result: "comma_symbolic_round_receipt p source =
      (comma_symbolic_sector_duration p source,target,Comma_Round_Fork a delta)"
    using source packet Comma_Fork by (subst comma_symbolic_round_receipt.simps) (simp add: Let_def)
  show ?thesis using result by (simp add: comma_literal_path.zero)
next
  case (Comma_Landmine delta)
  have result: "comma_symbolic_round_receipt p source =
      (comma_symbolic_sector_duration p source,target,Comma_Round_Landmine delta)"
    using source packet Comma_Landmine by (subst comma_symbolic_round_receipt.simps) (simp add: Let_def)
  show ?thesis using result by (simp add: comma_literal_path.zero)
next
  case Comma_Invalid
  have result: "comma_symbolic_round_receipt p source =
      (comma_symbolic_sector_duration p source,target,Comma_Round_Invalid)"
    using source packet Comma_Invalid by (subst comma_symbolic_round_receipt.simps) (simp add: Let_def)
  show ?thesis using result by (simp add: comma_literal_path.zero)
qed

lemma comma_symbolic_round_sector_duration_bound:
  assumes source: "comma_round_admitted source"
  shows "comma_symbolic_sector_duration p source \<le> fst (comma_symbolic_round_receipt p source)"
  using source
  by (subst comma_symbolic_round_receipt.simps)
    (auto simp: Let_def split: prod.splits comma_finite_move.splits if_splits)

theorem comma_symbolic_round_cut_exact:
  assumes source: "comma_round_admitted source" and exponent: "5 \<le> p"
    and bound: "j \<le> fst (comma_symbolic_round_receipt p source)"
  shows "comma_literal_path j (comma_chart_value p source)
       (comma_symbolic_round_point p source j) \<and>
    comma_literal_path (fst (comma_symbolic_round_receipt p source)-j)
      (comma_symbolic_round_point p source j)
      (comma_chart_value p (fst (snd (comma_symbolic_round_receipt p source))))"
  using source exponent bound
proof (induction p source j rule: comma_symbolic_round_point.induct[case_names step])
  case (step p source j)
  obtain target event where packet:
    "comma_decisive_endpoint_packet (p mod 924) source = (target,event)"
    by (cases "comma_decisive_endpoint_packet (p mod 924) source") auto
  have target: "target = comma_decisive_sector_target (p mod 924) source"
    using packet by (simp add: comma_decisive_endpoint_packet_def Let_def)
  let ?duration = "comma_symbolic_sector_duration p source"
  let ?total = "fst (comma_symbolic_round_receipt p source)"
  let ?last = "fst (snd (comma_symbolic_round_receipt p source))"
  show ?case
  proof (cases "j \<le> ?duration")
    case True
    have local_cut: "comma_literal_path j (comma_chart_value p source)
        (comma_symbolic_sector_point p source j) \<and>
      comma_literal_path (?duration-j) (comma_symbolic_sector_point p source j)
        (comma_chart_value p target)"
      using comma_symbolic_sector_cut_exact[OF step.prems(1,2) True] target by simp
    have tail: "comma_literal_path (?total-?duration)
        (comma_chart_value p target) (comma_chart_value p ?last)"
      by (rule comma_symbolic_round_sector_remainder[OF step.prems(1,2) packet])
    have length: "(?duration-j)+(?total-?duration)=?total-j"
      using comma_symbolic_round_sector_duration_bound[OF step.prems(1), of p] True by arith
    have suffix: "comma_literal_path (?total-j)
        (comma_symbolic_sector_point p source j) (comma_chart_value p ?last)"
      using comma_literal_path_append[OF conjunct2[OF local_cut] tail] length by simp
    have point: "comma_symbolic_round_point p source j = comma_symbolic_sector_point p source j"
      using step.prems(1) packet True by (subst comma_symbolic_round_point.simps) (simp add: Let_def)
    show ?thesis using local_cut suffix point by simp
  next
    case False
    note beyond = False
    have larger: "?duration < j" using beyond by simp
    show ?thesis
    proof (cases event)
      case (Comma_Next successor)
      have next_packet: "comma_decisive_endpoint_packet (p mod 924) source =
          (target,Comma_Next successor)" using packet Comma_Next by simp
      have successor: "comma_round_admitted successor"
        and edge: "comma_literal_path 1 (comma_chart_value p target) (comma_chart_value p successor)"
        using comma_symbolic_decisive_next_physical[OF step.prems(1,2) next_packet] by blast+
      have target_path: "comma_literal_path ?duration (comma_chart_value p source) (comma_chart_value p target)"
        using comma_symbolic_sector_finish[OF step.prems(1,2)] target by simp
      have head: "comma_literal_path (Suc ?duration) (comma_chart_value p source) (comma_chart_value p successor)"
        using comma_literal_path_append[OF target_path edge] by simp
      show ?thesis
      proof (cases "comma_round_crossing target successor")
        case True
        have result: "comma_symbolic_round_receipt p source = (Suc ?duration,successor,Comma_Round_Cross successor)"
          using step.prems packet Comma_Next True by (subst comma_symbolic_round_receipt.simps) (simp add: Let_def)
        have j: "j=Suc ?duration" using larger step.prems(3) result by simp
        have point: "comma_symbolic_round_point p source j = comma_chart_value p successor"
          using step.prems(1) packet Comma_Next True beyond by (subst comma_symbolic_round_point.simps) (simp add: Let_def)
        show ?thesis using head result j point by (simp add: comma_literal_path.zero)
      next
        case False
        note no_cross = False
        obtain n last outcome where tail_result:
          "comma_symbolic_round_receipt p successor = (n,last,outcome)"
          by (cases "comma_symbolic_round_receipt p successor") (auto split: prod.splits)
        have result: "comma_symbolic_round_receipt p source = (Suc ?duration+n,last,outcome)"
          using step.prems packet Comma_Next no_cross tail_result
          by (subst comma_symbolic_round_receipt.simps) (simp add: Let_def)
        have residual: "j-Suc ?duration \<le> n" using step.prems(3) result by simp
        have rec_cut: "comma_literal_path (j-Suc ?duration) (comma_chart_value p successor)
              (comma_symbolic_round_point p successor (j-Suc ?duration)) \<and>
            comma_literal_path (n-(j-Suc ?duration))
              (comma_symbolic_round_point p successor (j-Suc ?duration)) (comma_chart_value p last)"
          using step.IH step.prems packet Comma_Next beyond no_cross successor residual tail_result
          by (auto simp: Let_def)
        have point: "comma_symbolic_round_point p source j =
            comma_symbolic_round_point p successor (j-Suc ?duration)"
          using step.prems(1) packet Comma_Next beyond no_cross
          by (subst comma_symbolic_round_point.simps) (simp add: Let_def)
        have sum: "Suc ?duration + (j-Suc ?duration) = j" using larger by arith
        have diff: "n-(j-Suc ?duration) = Suc ?duration+n-j"
          using larger step.prems(3) result by simp
        have combined: "comma_literal_path j (comma_chart_value p source)
            (comma_symbolic_round_point p successor (j-Suc ?duration))"
          using comma_literal_path_append[OF head conjunct1[OF rec_cut]] sum by simp
        show ?thesis using combined rec_cut result point diff by simp
      qed
    next
      case (Comma_Fork a delta)
      have result: "fst (comma_symbolic_round_receipt p source)=?duration"
        using step.prems packet Comma_Fork by (subst comma_symbolic_round_receipt.simps) (simp add: Let_def)
      show ?thesis using larger step.prems(3) result by simp
    next
      case (Comma_Landmine delta)
      have result: "fst (comma_symbolic_round_receipt p source)=?duration"
        using step.prems packet Comma_Landmine by (subst comma_symbolic_round_receipt.simps) (simp add: Let_def)
      show ?thesis using larger step.prems(3) result by simp
    next
      case Comma_Invalid
      have result: "fst (comma_symbolic_round_receipt p source)=?duration"
        using step.prems packet Comma_Invalid by (subst comma_symbolic_round_receipt.simps) (simp add: Let_def)
      show ?thesis using larger step.prems(3) result by simp
    qed
  qed
qed

ML \<open>
  val checked = @{thms comma_symbolic_round_sector_remainder
    comma_symbolic_round_sector_duration_bound comma_symbolic_round_cut_exact};
  val _ = if null (Thm_Deps.all_oracles checked) then () else error "Round cut used an oracle";
  val _ = if Thm_Deps.has_skip_proof checked then error "Round cut contains skipped proofs" else ();
  val _ = Comma_Proof_Dependency_Audit.require_paths @{context}
    "Round cut excludes legacy authority"
    ["comma_round_close", "comma_finite_macro", "comma_terminal_weight_decode",
     "comma_phase_class_survival_lengths", "comma_python_first_terminal_walk"] checked;
\<close>
end
