theory Comma_Decade_Layer_Smoke
  imports Comma_Decade_Layer_Check.Comma_Decade_Layer_Check
begin

text \<open>Small checked layers test memo ownership, phase wrap, rejection
and admission-before-work. This is not the all-state B5 acceptance instance.\<close>

local_setup \<open>fn lthy =>
  let
    val core = Comma_Fast_Kernel.make lthy
    fun count name report =
      let
        val prefix = name ^ "="
        val token = the (List.find (String.isPrefix prefix)
          (String.tokens (fn character => character = #" ") report))
      in the (Int.fromString (String.extract (token, size prefix, NONE))) end
    fun query phase source = Simplifier.rewrite (#context core)
      (Thm.cterm_of lthy (@{term comma_fast_sector_target} $
        HOLogic.mk_number @{typ nat} phase $ source))
    val near = @{term "Comma_Near 1 3 100"}
    val first = query 0 near
    val first_report = #stats core ()
    val transported = query 923 near
    val transported_report = #stats core ()
    val _ = if count "sector_target_misses" first_report = 1 andalso
        count "sector_target_misses" transported_report = 1 andalso
        count "sector_target_hits" transported_report >
          count "sector_target_hits" first_report andalso
        Thm.term_of (Thm.rhs_of first) aconv Thm.term_of (Thm.rhs_of transported) andalso
        Thm.term_of (Thm.lhs_of transported) aconv
          @{term "comma_fast_sector_target 923 (Comma_Near 1 3 100)"} then ()
      else error "Near phase transport rebuilt arithmetic or changed its source binding"
    val occurrence = query 923 @{term "Comma_Near 1 4 100"}
    val occurrence_report = #stats core ()
    val _ = if count "sector_target_misses" occurrence_report = 2 then ()
      else error "Near phase sharing removed occurrence delta from the cache key"
    val entry_first = query 0 @{term "Comma_Entry 1 3 0"}
    val entry_second = query 1 @{term "Comma_Entry 1 3 0"}
    val entry_report = #stats core ()
    val _ = if count "sector_target_misses" entry_report = 4 then ()
      else error "Entry sector cache incorrectly discarded its decimal phase"
    val facts = [first, transported, occurrence, entry_first, entry_second]
    val _ = if null (Thm_Deps.all_oracles facts) then ()
      else error "Near canonical cache smoke has an oracle"
    val _ = Comma_Fast_Kernel.report ("Near canonical cache smoke: " ^ entry_report)
  in #2 (Local_Theory.note ((Binding.name "comma_fast_near_cache_smoke", []), facts) lthy) end\<close>

local_setup \<open>fn lthy =>
  let
    fun rejects expected (Exn.Exn (ERROR actual)) = expected = actual
      | rejects _ _ = false
    val engine = Comma_Decade_Layer_Check.make lthy {max_layers = 128}
    val first = #construct engine (1, 0)
    val prior_stats = #stats engine ()
    val repeated = #construct engine (1, 0)
    val repeat_stats = #stats engine ()
    val _ = if #base_attempts prior_stats = #base_attempts repeat_stats andalso
        #square_attempts prior_stats = #square_attempts repeat_stats andalso
        #hits prior_stats < #hits repeat_stats andalso #value first aconv #value repeated then ()
      else error "Repeated layer request rebuilt arithmetic or changed its value"
    val wrapped = #construct engine (1, 923)
    val wrap_stats = #stats engine ()
    val _ = if #base_attempts wrap_stats = #base_attempts repeat_stats + 1 then ()
      else error "Wrapped phase failed to reuse phase-zero base"
    val invalid = Exn.capture (#construct engine) (0, 924)
    val invalid_stats = #stats engine ()
    val _ = if rejects "Layer request requires level 0..30 and phase 0..923" invalid andalso
        #base_attempts invalid_stats = #base_attempts wrap_stats andalso
        #square_attempts invalid_stats = #square_attempts wrap_stats andalso
        #failed_requests invalid_stats = #failed_requests wrap_stats + 1 then ()
      else error "Foreign phase reached arithmetic or escaped failed-work accounting"
    val incomplete = Exn.capture (fn () => #complete engine 1 0 26) ()
    val rejected_stats = #stats engine ()
    val _ = if rejects "Layer contains a live, invalid, or over-bound result" incomplete andalso
        #complete_failures rejected_stats = 1 andalso
        #failed_requests rejected_stats = #failed_requests invalid_stats + 1 then ()
      else error "A live D2 layer was accepted as complete or its failure was uncharged"
    val small = Comma_Decade_Layer_Check.make lthy {max_layers = 1}
    val refused = Exn.capture (#construct small) (1, 0)
    val small_stats = #stats small ()
    val _ = if rejects "Layer cache construction budget exhausted" refused andalso #base_attempts small_stats = 1 andalso
        #square_attempts small_stats = 0 andalso #retained_layers small_stats = 0 andalso
        #checked_base_atoms small_stats = 91 andalso #failed_requests small_stats = 1 then ()
      else error "Layer capacity was checked after arithmetic or failure leaked publications"
    val doubled = #construct engine (2, 0)
    val facts = [#correct first, #correct wrapped, #correct doubled]
    val _ = if null (Thm_Deps.all_oracles facts) then () else error "Layer smoke has an oracle"
    val _ = Comma_Fast_Kernel.report ("Layer smoke: " ^ #report engine ())
  in #2 (Local_Theory.note ((Binding.name "comma_D2_layer_smoke", []), facts) lthy) end\<close>

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_D2_layer_smoke comma_fast_near_cache_smoke}) then ()
    else error "Exported layer smoke depends on an oracle";
\<close>
end
