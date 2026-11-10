(* Shared selection of untrusted candidate data. No transition evaluator is loaded. *)
structure Comma_Decade_Rank_Lookup =
struct
  fun canonical_term numeral_context ctxt term = Thm.term_of (Thm.rhs_of
    (Simplifier.rewrite (numeral_context ctxt) (Thm.cterm_of ctxt term)))

  fun timed elapsed failed f x =
    let
      val start = Time.now ()
      val result = Exn.capture f x
      val _ = elapsed := Time.+ (!elapsed, Time.- (Time.now (), start))
      val _ = if Exn.is_exn result then failed := !failed + 1 else ()
    in Exn.release result end

  (* Select before simplifying: normalizing the complete candidate list for
     every lookup would turn a constant-depth table into quadratic work. *)
  fun make_lookup {numeral_context, natural_context} ctxt codes_def rank_def =
    let
      val scalar = numeral_context ctxt
      val arithmetic = Simplifier.rewrite (natural_context ctxt)
      val root = if can Logic.dest_equals (Thm.prop_of codes_def)
        then codes_def else codes_def RS @{thm eq_reflection}
      val root_term = Thm.term_of (Thm.lhs_of root)
      val memo = Unsynchronized.ref (Termtab.empty: thm Termtab.table)
      val lookups = Unsynchronized.ref 0
      val hits = Unsynchronized.ref 0
      val internal_publications = Unsynchronized.ref 0
      val leaf_evaluations = Unsynchronized.ref 0
      val retained = Unsynchronized.ref 0
      val peak_retained = Unsynchronized.ref 0
      val evicted = Unsynchronized.ref 0
      val elapsed = Unsynchronized.ref Time.zeroTime
      val failed = Unsynchronized.ref 0
      fun nth ct =
        let
          val normalized = Conv.arg_conv arithmetic ct
          val equation = Conv.rewr_conv (@{thm nth_Cons'} RS @{thm eq_reflection}) (Thm.rhs_of normalized)
          val condition = Conv.fun_conv (Conv.fun_conv (Conv.arg_conv arithmetic))
            (Thm.rhs_of equation)
          val reduced = (Conv.rewr_conv (@{thm if_True} RS @{thm eq_reflection}) else_conv
            Conv.rewr_conv (@{thm if_False} RS @{thm eq_reflection})) (Thm.rhs_of condition)
          val first = Thm.transitive normalized
            (Thm.transitive equation (Thm.transitive condition reduced))
          val (head, _) = strip_comb (Thm.term_of (Thm.rhs_of first))
        in
          if (case head of Const (name, _) => name = @{const_name nth} | _ => false) then
            Thm.transitive first (nth (Thm.rhs_of first)) else first
        end
      fun lookup ct =
        let
          val key = Thm.term_of ct
          val _ = lookups := !lookups + 1
        in
          (case Termtab.lookup (!memo) key of
            SOME result => (hits := !hits + 1; result)
          | NONE =>
              let
                val result = if key aconv root_term then root else
                  let
                    val transported = Conv.fun_conv (Conv.arg_conv lookup) ct
                  in Thm.transitive transported (nth (Thm.rhs_of transported)) end
                val _ = if fastype_of key = @{typ nat} then
                    leaf_evaluations := !leaf_evaluations + 1
                  else
                    let
                      val _ = if !retained < 8192 then () else
                        (evicted := !evicted + !retained;
                         memo := Termtab.empty; retained := 0)
                      val _ = memo := Termtab.update (key, result) (!memo)
                      val _ = retained := !retained + 1
                      val _ = peak_retained := Int.max (!peak_retained, !retained)
                    in internal_publications := !internal_publications + 1 end
              in result end)
        end
      fun rank_unmeasured raw_state =
        let
          val state = canonical_term numeral_context ctxt raw_state
          val _ =
            (case strip_comb state of
              (Const (name, _), [phase, offset]) =>
                if name <> @{const_name Comma_Decade} then
                  error "Candidate lookup requires a decade state"
                else
                  (case (try HOLogic.dest_number phase, try HOLogic.dest_number offset) of
                    (SOME (phase_type, r), SOME (offset_type, x)) =>
                      if phase_type = @{typ nat} andalso offset_type = @{typ nat} andalso
                          0 <= r andalso r < 924 andalso 0 <= x andalso x <= 90
                        then () else error "Candidate lookup outside admitted decade domain"
                  | _ => error "Candidate lookup requires numeral phase and offset")
            | _ => error "Candidate lookup requires a concrete decade state")
          val rank_head = case HOLogic.dest_eq
              (HOLogic.dest_Trueprop (Thm.prop_of rank_def)) of
            (Const (name, _) $ _, _) => Const (name, fastype_of state --> @{typ nat})
          | _ => error "Expected unary candidate rank definition"
          val opened = Simplifier.rewrite
            (scalar |> Simplifier.add_simps [rank_def] |> Simplifier.add_simps
              @{thms comma_decade_state.case comma_decade_admitted.simps})
            (Thm.cterm_of ctxt (rank_head $ state))
          val indices = arithmetic (Thm.rhs_of opened)
          val selected = lookup (Thm.rhs_of indices)
        in Thm.transitive opened (Thm.transitive indices selected)
          RS @{thm meta_eq_to_obj_eq} end
      val rank = timed elapsed failed rank_unmeasured
      fun stats () = {lookups = !lookups, hits = !hits,
        internal_publications = !internal_publications,
        leaf_evaluations = !leaf_evaluations, retained_internal = !retained,
        peak_retained_internal = !peak_retained, evicted_internal = !evicted,
        retained_leaf_equations = 0, elapsed_ms = Time.toMilliseconds (!elapsed), failed_work = !failed}
    in (rank, stats) end

end
