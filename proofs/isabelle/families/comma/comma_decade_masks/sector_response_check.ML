structure Comma_Sector_Response_Check =
struct
  type branch = {move: term, equation: thm}
  type period_result = {value: int, equation: thm}

  fun natural term =
    (case try HOLogic.dest_number term of
      SOME (typ, n) => typ = @{typ nat} andalso n >= 0
    | NONE => can HOLogic.dest_nat term)
  fun position term =
    (case strip_comb term of
      (Const (name, _), [f, d, x]) =>
        member (op =) [@{const_name Comma_Entry}, @{const_name Comma_Near}] name
          andalso forall natural [f, d, x]
    | _ => false)
  fun move term =
    (case strip_comb term of
      (Const (name, _), []) => name = @{const_name Comma_Invalid}
    | (Const (name, _), [target]) =>
        (name = @{const_name Comma_Next} andalso position target) orelse
        (name = @{const_name Comma_Landmine} andalso natural target)
    | (Const (name, _), [a, d]) =>
        name = @{const_name Comma_Fork} andalso natural a andalso natural d
    | _ => false)
  (* Shape and complete typed source identity are checked before certification
     and publication. This check has no cache authority of its own. *)
  fun validate_branch_equation expression equation =
    let
      val _ = if Thm.term_of (Thm.lhs_of equation) aconv expression then ()
        else error "Sector branch theorem does not bind its full source key"
      val _ = if Thm.nprems_of equation = 0 andalso null (Thm.hyps_of equation) then ()
        else error "Sector branch theorem has unproved premises or hypotheses"
      val result = Thm.term_of (Thm.rhs_of equation)
      val _ = if move result then ()
        else error "Sector branch did not normalize to a closed move"
    in {move = result, equation = equation}: branch end

  fun make ctxt {max_clauses} =
    let
      val _ = if 1 <= max_clauses andalso max_clauses <= 8192 then ()
        else error "Sector clause capacity must lie in 1..8192"
      val kernel = Comma_Fast_Kernel.make ctxt
      val (certify, certification) = Comma_Entry_Arithmetic.make_certifier ctxt
      val memo = Unsynchronized.ref (Termtab.empty: branch Termtab.table)
      val canonical_near = Unsynchronized.ref (Termtab.empty: branch Termtab.table)
      val canonical_near_lookups = Unsynchronized.ref 0
      val canonical_near_hits = Unsynchronized.ref 0
      val canonical_near_misses = Unsynchronized.ref 0
      val canonical_near_attempts = Unsynchronized.ref 0
      val canonical_near_failures = Unsynchronized.ref 0
      val period_memo = Unsynchronized.ref (Termtab.empty: period_result Termtab.table)
      val canonical_periods = Unsynchronized.ref (Termtab.empty: thm Termtab.table)
      val canonical_period_hits = Unsynchronized.ref 0
      val canonical_period_attempts = Unsynchronized.ref 0
      val period_attempts = Unsynchronized.ref 0
      val period_hits = Unsynchronized.ref 0
      val period_failures = Unsynchronized.ref 0
      val period_retained = Unsynchronized.ref 0
      val retained = Unsynchronized.ref 0
      val attempts = Unsynchronized.ref 0
      val lookups = Unsynchronized.ref 0
      val hits = Unsynchronized.ref 0
      val failures = Unsynchronized.ref 0
      val elapsed = Unsynchronized.ref Time.zeroTime
      fun nat n = HOLogic.mk_number @{typ nat} n
      fun evaluate expression =
        certify (Simplifier.rewrite (#context kernel) (Thm.cterm_of ctxt expression))
      (* Period proofs have their own explicit max_clauses cap. *)
      fun period f x =
        let
          val outcome = Exn.capture (fn () =>
            let
              val _ = if 1 <= f andalso f <= 9 andalso 0 <= x andalso x <= 98 then ()
                else error "Sector period requires f=1..9 and x=0..98"
              val expression = @{term comma_short_period} $
                (@{term comma_finite_period_fast} $ nat f $
                  (@{term "\<lambda>x::nat. x mod 10"} $ nat x))
            in case Termtab.lookup (!period_memo) expression of
              SOME answer => (period_hits := !period_hits + 1; answer)
            | NONE =>
              let
                val _ = if !period_retained < max_clauses then ()
                  else error "Sector period retention budget exhausted"
                val _ = period_attempts := !period_attempts + 1
                val digit_term = @{term "\<lambda>x::nat. x mod 10"} $ nat x
                val digit_equation = certify (Simplifier.rewrite
                  (Comma_Entry_Arithmetic.natural_context ctxt) (Thm.cterm_of ctxt digit_term))
                val prefix = @{term comma_finite_period_fast} $ nat f
                val binding = Thm.combination (Thm.reflexive (Thm.cterm_of ctxt @{term comma_short_period}))
                  (Thm.combination (Thm.reflexive (Thm.cterm_of ctxt prefix)) digit_equation)
                val canonical = Thm.term_of (Thm.rhs_of binding)
                val canonical_equation = (case Termtab.lookup (!canonical_periods) canonical of
                    SOME theorem => (canonical_period_hits := !canonical_period_hits + 1; theorem)
                  | NONE =>
                    let
                      val _ = if Termtab.size (!canonical_periods) < max_clauses then ()
                        else error "Canonical period retention budget exhausted"
                      val _ = canonical_period_attempts := !canonical_period_attempts + 1
                      val theorem = evaluate canonical
                      val (_, checked) = HOLogic.dest_number (Thm.term_of (Thm.rhs_of theorem))
                      val _ = if member (op =) [1,2,3,6,22,28] checked andalso
                          Thm.term_of (Thm.lhs_of theorem) aconv canonical then ()
                        else error "Canonical period did not produce a checked short period"
                      val _ = canonical_periods := Termtab.update (canonical,theorem) (!canonical_periods)
                    in theorem end)
                val equation = certify (Thm.transitive binding canonical_equation)
                val _ = if Thm.term_of (Thm.lhs_of equation) aconv expression then ()
                  else error "Canonical period lost its original source binding"
                val (_, value) = HOLogic.dest_number (Thm.term_of (Thm.rhs_of equation))
                val _ = if member (op =) [1,2,3,6,22,28] value then ()
                  else error "Sector period did not return the admitted short alphabet"
                val answer = {value = value, equation = equation}
                val _ = period_memo := Termtab.update (expression, answer) (!period_memo)
                val _ = period_retained := !period_retained + 1
              in answer end
            end) ()
          val _ = if Exn.is_exn outcome then period_failures := !period_failures + 1 else ()
        in Exn.release outcome end
      fun branch f x k =
        let
          val begin = Time.now ()
          val outcome = Exn.capture (fn () =>
            let
              val _ = if 1 <= f andalso f <= 9 andalso 0 <= x andalso x <= 98
                  andalso 0 <= k andalso k < 28 then ()
                else error "Sector branch requires f=1..9, x=0..98, k=0..27"
              val endpoint = @{term comma_entry_alphabet_endpoint} $ nat f $ nat x $ nat k
              val target = @{term Comma_Near} $ nat f $ nat 0 $ endpoint
              val expression = @{term comma_fast_step} $ nat 0 $ target
              val _ = lookups := !lookups + 1
            in
              case Termtab.lookup (!memo) expression of
                SOME result => (hits := !hits + 1; result)
              | NONE =>
                  let
                    val _ = if !retained < max_clauses then ()
                      else error "Sector clause retention budget exhausted"
                    val _ = attempts := !attempts + 1
                    val admitted_period = period f x
                    val _ = if k < #value admitted_period then ()
                      else error "Sector branch phase is outside its proved short period"
                    (* Normalize the Entry endpoint while it still carries its
                       complete source equation. Only then share the Near step. *)
                    val endpoint_equation = evaluate endpoint
                    val _ = if Thm.term_of (Thm.lhs_of endpoint_equation) aconv endpoint
                        andalso natural (Thm.term_of (Thm.rhs_of endpoint_equation)) then ()
                      else error "Entry endpoint did not produce a checked closed natural"
                    val prefix = @{term Comma_Near} $ nat f $ nat 0
                    val binding = certify (Thm.combination
                      (Thm.reflexive (Thm.cterm_of ctxt (@{term comma_fast_step} $ nat 0)))
                      (Thm.combination (Thm.reflexive (Thm.cterm_of ctxt prefix))
                        endpoint_equation))
                    val canonical = Thm.term_of (Thm.rhs_of binding)
                    val _ = canonical_near_lookups := !canonical_near_lookups + 1
                    val cached = Termtab.lookup (!canonical_near) canonical
                    val checked = (case cached of
                        SOME answer => (canonical_near_hits := !canonical_near_hits + 1; answer)
                      | NONE =>
                        let
                          val _ = canonical_near_misses := !canonical_near_misses + 1
                          val _ = if Termtab.size (!canonical_near) < max_clauses then ()
                            else error "Canonical Near retention budget exhausted"
                          val _ = canonical_near_attempts := !canonical_near_attempts + 1
                          val proof = Exn.capture (fn () =>
                            validate_branch_equation canonical (evaluate canonical)) ()
                          val _ = if Exn.is_exn proof then
                            canonical_near_failures := !canonical_near_failures + 1 else ()
                        in Exn.release proof end)
                    val equation = certify (Thm.transitive binding (#equation checked))
                    val entry = validate_branch_equation expression equation
                    (* Delay both publications until the rebound source proof
                       passes every check. Failed work publishes no Near result. *)
                    val _ = (case cached of SOME _ => () | NONE =>
                      canonical_near := Termtab.update (canonical, checked) (!canonical_near))
                    val _ = memo := Termtab.update (expression, entry) (!memo)
                    val _ = retained := !retained + 1
                  in entry end
            end) ()
          val _ = elapsed := Time.+ (!elapsed, Time.- (Time.now (), begin))
          val _ = if Exn.is_exn outcome then failures := !failures + 1 else ()
        in Exn.release outcome end
      fun stats () = {lookups = !lookups, hits = !hits, attempts = !attempts,
        failures = !failures, retained = !retained,
        canonical_near_lookups = !canonical_near_lookups,
        canonical_near_hits = !canonical_near_hits,
        canonical_near_misses = !canonical_near_misses,
        canonical_near_attempts = !canonical_near_attempts,
        canonical_near_failures = !canonical_near_failures,
        canonical_near_retained = Termtab.size (!canonical_near), period_attempts = !period_attempts,
        canonical_period_attempts = !canonical_period_attempts,
        canonical_period_hits = !canonical_period_hits,
        period_hits = !period_hits, period_failures = !period_failures, period_retained = !period_retained}
      fun report () = "sector_clause_lookups=" ^ Int.toString (!lookups) ^
        " sector_clause_hits=" ^ Int.toString (!hits) ^
        " sector_clause_attempts=" ^ Int.toString (!attempts) ^
        " sector_clause_failures=" ^ Int.toString (!failures) ^
        " sector_clause_retained=" ^ Int.toString (!retained) ^
        " canonical_near_lookups=" ^ Int.toString (!canonical_near_lookups) ^
        " canonical_near_hits=" ^ Int.toString (!canonical_near_hits) ^
        " canonical_near_misses=" ^ Int.toString (!canonical_near_misses) ^
        " canonical_near_attempts=" ^ Int.toString (!canonical_near_attempts) ^
        " canonical_near_failures=" ^ Int.toString (!canonical_near_failures) ^
        " canonical_near_retained=" ^ Int.toString (Termtab.size (!canonical_near)) ^
        " canonical_period_attempts=" ^ Int.toString (!canonical_period_attempts) ^
        " canonical_period_hits=" ^ Int.toString (!canonical_period_hits) ^
        " canonical_period_retained=" ^ Int.toString (Termtab.size (!canonical_periods)) ^
        " sector_period_attempts=" ^ Int.toString (!period_attempts) ^
        " sector_period_hits=" ^ Int.toString (!period_hits) ^
        " sector_period_failures=" ^ Int.toString (!period_failures) ^
        " sector_period_retained=" ^ Int.toString (!period_retained) ^
        " sector_clause_inclusive_ms=" ^ LargeInt.toString (Time.toMilliseconds (!elapsed))
    in {branch = branch, period = period, stats = stats, report = report,
      arithmetic_stats = #stats kernel, certification = certification} end
end
