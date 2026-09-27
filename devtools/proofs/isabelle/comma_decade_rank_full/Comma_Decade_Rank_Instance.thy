theory Comma_Decade_Rank_Instance
  imports Comma_Decade_Rank_Check.Comma_Decade_Rank_Data
begin

text \<open>This acceptance instance checks every admitted state. Failure or a
resource timeout leaves the concrete rank obligation open. The candidate data
alone, or a successful smaller smoke batch, does not establish this theorem.\<close>

local_setup \<open>fn lthy =>
  let
    val (rank_lookup, lookup_stats) = Comma_Decade_Rank_Check.make_lookup lthy
      @{thm comma_decade_rank_codes_def} @{thm comma_decade_rank_candidate_def}
    val (rectangle, stats) = Comma_Decade_Rank_Check.check lthy
      {rank = @{term comma_decade_rank_candidate}, rank_lookup = rank_lookup,
       lookup_work = fn () => #elapsed_ms (lookup_stats ()),
       phases = 924, generation = getenv "NUMBER_COMPILER_PROOF_GENERATION"}
    val _ = warning ("Rank lookup work: " ^ @{make_string} (lookup_stats ()))
    val _ = warning ("Complete decade rank: " ^ @{make_string} stats)
  in #2 (Local_Theory.note
    ((Binding.name "comma_decade_rank_rectangle", []), [rectangle]) lthy) end\<close>

lemma comma_decade_rank_candidate_checked:
  "comma_decade_rank_check comma_decade_rank_candidate"
  by (rule comma_rank_complete_rectangle[OF comma_decade_rank_rectangle])

ML \<open>
  val _ = if null (Thm_Deps.all_oracles @{thms comma_decade_rank_candidate_checked})
    then () else error "Concrete decade rank has an oracle dependency";
\<close>
end
