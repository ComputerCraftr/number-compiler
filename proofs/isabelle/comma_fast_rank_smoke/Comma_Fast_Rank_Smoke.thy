theory Comma_Fast_Rank_Smoke
  imports Comma_Fast_Rank_Check.Comma_Fast_Rank_Check
begin

text \<open>This first-phase check is a performance probe. It does not
establish the all-phase rank or authorize a production cutover.\<close>

local_setup \<open>fn lthy =>
  let
    val (lookup, lookup_stats) = Comma_Decade_Rank_Lookup.make_lookup
      {numeral_context = Comma_Entry_Arithmetic.numeral_context,
       natural_context = Comma_Entry_Arithmetic.natural_context} lthy
      @{thm comma_decade_rank_codes_def} @{thm comma_decade_rank_candidate_on_valid_def}
    val first = lookup @{term "Comma_Decade 1 49"}
    val before_alias = lookup_stats ()
    val alias = lookup @{term "Comma_Decade (Suc 0) 49"}
    val after_alias = lookup_stats ()
    val _ = if Thm.prop_of first aconv Thm.prop_of alias andalso
        #hits after_alias > #hits before_alias andalso
        #internal_publications after_alias = #internal_publications before_alias andalso
        forall (fn th => Thm.nprems_of th=0 andalso null (Thm.hyps_of th)) [first,alias]
        andalso null (Thm_Deps.all_oracles [first,alias]) then ()
      else error "Numeral aliases did not reuse the closed candidate lookup"
    val engine = Comma_Fast_Rank_Kernel.make lthy
    val checked = Comma_Fast_Rank_Kernel.range lthy engine (0,1)
    val numeral_alias = Goal.prove lthy [] []
      @{prop "comma_decade_rank_candidate_on_valid (Comma_Decade 1 49)=
        comma_decade_rank_candidate_on_valid (Comma_Decade (Suc 0) 49)"}
      (fn _ => simp_tac (#context engine) 1)
    fun prove proposition = Goal.prove lthy [] [] proposition
      (fn _ => simp_tac (#context engine) 1)
    val flat = prove @{prop "\<not> comma_fast_decade_rank_step (\<lambda>_. 0) (Comma_Decade 0 0)"}
    val bound = prove @{prop "\<not> comma_fast_decade_bounded_rank_step
      comma_decade_rank_candidate_on_valid 2 (Comma_Decade 0 0)"}
    fun note name fact context = #2 (Local_Theory.note
      ((Binding.name name, []), [fact]) context)
  in lthy
    |> note "comma_fast_rank_first_phase" checked
    |> note "comma_fast_rank_rejects_flat_candidate" flat
    |> note "comma_fast_rank_rejects_small_bound" bound
    |> note "comma_fast_rank_numeral_alias" numeral_alias end\<close>

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_fast_rank_first_phase comma_fast_rank_rejects_flat_candidate
      comma_fast_rank_rejects_small_bound comma_fast_rank_numeral_alias}) then ()
    else error "Fast rank dependency audit failed";
\<close>
end
