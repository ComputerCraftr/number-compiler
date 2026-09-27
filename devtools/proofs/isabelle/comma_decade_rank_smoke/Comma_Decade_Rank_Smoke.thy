theory Comma_Decade_Rank_Smoke
  imports Comma_Decade_Rank_Check.Comma_Decade_Rank_Data
begin

text \<open>One phase validates the streamed checker and the rank-only candidate
lookup. This is not the complete rank instance or constructor totality.\<close>

local_setup \<open>fn lthy =>
  let
    val (rank_lookup, lookup_stats) = Comma_Decade_Rank_Check.make_lookup lthy
      @{thm comma_decade_rank_codes_def} @{thm comma_decade_rank_candidate_def}
    val one = @{term "Comma_Decade 1 49"}
    val successor_zero = @{term "Comma_Decade (Suc 0) 49"}
    val _ = if Comma_Decade_Rank_Check.canonical_term lthy one aconv
        Comma_Decade_Rank_Check.canonical_term lthy successor_zero then ()
      else error "Decade numeral canonicalization differs"
    val first = rank_lookup one
    val second = rank_lookup successor_zero
    val _ = if Thm.prop_of first aconv Thm.prop_of second andalso
        forall (fn th => Thm.nprems_of th = 0 andalso null (Thm.hyps_of th))
          [first, second] andalso null (Thm_Deps.all_oracles [first, second])
      then () else error "Decade numeral spellings do not share a closed rank equation"
    val (rectangle, stats) = Comma_Decade_Rank_Check.check lthy
      {rank = @{term comma_decade_rank_candidate}, rank_lookup = rank_lookup,
       lookup_work = fn () => #elapsed_ms (lookup_stats ()),
       phases = 1, generation = getenv "NUMBER_COMPILER_PROOF_GENERATION"}
    val _ = warning ("Rank lookup work: " ^ @{make_string} (lookup_stats ()))
    val _ = warning ("Decade rank smoke: " ^ @{make_string} stats)
  in #2 (Local_Theory.note
    ((Binding.name "comma_decade_rank_smoke", []), [rectangle]) lthy) end\<close>
ML \<open>
  val _ = if null (Thm_Deps.all_oracles @{thms comma_decade_rank_smoke})
    then () else error "Decade rank smoke depends on an oracle";
\<close>
end
