theory Comma_Symbolic_Round_Action
  imports Comma_Symbolic_Sector_Action
begin

text \<open>The round receipt proposes a composed physical duration and endpoint.
Its typed control is proved equal to the decisive source action below; physical
duration and endpoint refinement remain separate obligations. The recursive
argument is the strictly advancing decimal sector; no supplied fuel, numeric
rank, occurrence list or candidate terminal code is part of the receipt.\<close>

function comma_symbolic_round_receipt ::
    "nat \<Rightarrow> comma_finite_position \<Rightarrow>
      (nat \<times> comma_finite_position \<times> comma_round_result)" where
  "comma_symbolic_round_receipt p source =
    (if comma_round_admitted source then
       (let (target,event) = comma_decisive_endpoint_packet (p mod 924) source;
            elapsed = comma_symbolic_sector_duration p source
        in case event of
          Comma_Next successor \<Rightarrow>
            if comma_round_crossing target successor then
              (Suc elapsed, successor, Comma_Round_Cross successor)
            else (case comma_symbolic_round_receipt p successor of
                (tail,terminal,outcome) \<Rightarrow> (Suc elapsed + tail,terminal,outcome))
        | Comma_Fork a delta \<Rightarrow> (elapsed,target,Comma_Round_Fork a delta)
        | Comma_Landmine delta \<Rightarrow> (elapsed,target,Comma_Round_Landmine delta)
        | Comma_Invalid \<Rightarrow> (elapsed,target,Comma_Round_Invalid))
     else (0,source,Comma_Round_Invalid))"
  by pat_completeness auto
termination
  apply (relation "measure (\<lambda>(p,source). 9-comma_sector_number source)")
   apply simp
  apply (clarsimp simp: Let_def comma_decisive_endpoint_packet_def split: prod.splits)
  by (metis comma_decisive_endpoint_successor_decreases mod_mod_trivial)

declare comma_symbolic_round_receipt.simps [simp del]


lemma comma_symbolic_round_receipt_control:
  "snd (snd (comma_symbolic_round_receipt p source)) =
    comma_decisive_endpoint_round (p mod 924) source"
proof (induction p source rule: comma_symbolic_round_receipt.induct)
  case (1 p source)
  then show ?case
    by (subst comma_symbolic_round_receipt.simps;
        subst comma_decisive_endpoint_round.simps;
        auto simp: Let_def comma_decisive_endpoint_packet_def
          split: comma_finite_move.splits prod.splits if_splits)
qed

ML \<open>
  val checked = @{thms comma_symbolic_round_receipt.simps comma_symbolic_round_receipt_control};
  val _ = if null (Thm_Deps.all_oracles checked) then () else error "Round receipt used an oracle";
  val _ = if Thm_Deps.has_skip_proof checked then error "Round receipt contains skipped proofs" else ();
  val _ = Comma_Proof_Dependency_Audit.require_paths @{context}
    "Round receipt excludes legacy authority"
    ["comma_round_close", "comma_finite_macro", "comma_terminal_weight_decode",
     "comma_phase_class_survival_lengths", "comma_python_first_terminal_walk"] checked;
\<close>
end
