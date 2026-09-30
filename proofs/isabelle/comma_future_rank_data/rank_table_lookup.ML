(* Proof-producing selected lookup for the untrusted future rank table. *)
structure Comma_Future_Rank_Lookup =
struct
  fun closed term = null (Term.add_frees term []) andalso
    null (Term.add_vars term []) andalso not (Term.is_open term)

  fun timed elapsed failures f x =
    let
      val start = Time.now ()
      val result = Exn.capture f x
      val _ = elapsed := Time.+ (!elapsed, Time.- (Time.now (), start))
      val _ = if Exn.is_exn result then failures := !failures + 1 else ()
    in Exn.release result end

  (* Keep the four-dimensional rank data opaque to the general simpset.  A
     lookup opens only the selected path, using the data definition and the
     kernel's list-nth equations. *)
  fun selected_table ctxt name codes_def =
    let
      val scalar = Comma_Entry_Arithmetic.natural_context ctxt
      val arithmetic = Simplifier.rewrite scalar
      val root = codes_def RS @{thm eq_reflection}
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
      val failures = Unsynchronized.ref 0

      fun nth ct =
        let
          val normalized = Conv.arg_conv arithmetic ct
          val equation = Conv.rewr_conv
            (@{thm nth_Cons'} RS @{thm eq_reflection}) (Thm.rhs_of normalized)
          val condition = Conv.fun_conv (Conv.fun_conv (Conv.arg_conv arithmetic))
            (Thm.rhs_of equation)
          val reduced =
            (Conv.rewr_conv (@{thm if_True} RS @{thm eq_reflection}) else_conv
             Conv.rewr_conv (@{thm if_False} RS @{thm eq_reflection}))
              (Thm.rhs_of condition)
          val first = Thm.transitive normalized
            (Thm.transitive equation (Thm.transitive condition reduced))
          val (head, _) = strip_comb (Thm.term_of (Thm.rhs_of first))
        in
          if (case head of Const (constant, _) => constant = @{const_name nth} | _ => false)
          then Thm.transitive first (nth (Thm.rhs_of first)) else first
        end

      fun lookup ct =
        let
          val key = Thm.term_of ct
          val _ = lookups := !lookups + 1
        in
          (case Termtab.lookup (!memo) key of
            SOME theorem => (hits := !hits + 1; theorem)
          | NONE =>
              let
                val theorem = if key aconv root_term then root else
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
                      val _ = memo := Termtab.update (key, theorem) (!memo)
                      val _ = retained := !retained + 1
                      val _ = peak_retained := Int.max (!peak_retained, !retained)
                    in internal_publications := !internal_publications + 1 end
              in theorem end)
        end

      fun convert ct =
        let val term = Thm.term_of ct in
          if not (closed term) then NONE else
            SOME (timed elapsed failures lookup ct)
        end
      val pattern = (case name of
          "N" => @{term "comma_rank_codes_N ! i"}
        | "Z" => @{term "comma_rank_codes_Z ! i"}
        | _ => error "Unknown future rank table")
        |> Term.map_aterms
          (fn Free (variable, typ) => Var ((variable, 0), typ) | atom => atom)
      val procedure = Simplifier.make_simproc ctxt
        {name = "comma_future_selected_" ^ name, kind = Simplifier.Simproc,
         lhss = [pattern], proc = fn _ => fn _ => convert, identifier = []}
      fun stats () = name ^ "_lookups=" ^ Int.toString (!lookups) ^
        " " ^ name ^ "_hits=" ^ Int.toString (!hits) ^
        " " ^ name ^ "_leaf_evaluations=" ^ Int.toString (!leaf_evaluations) ^
        " " ^ name ^ "_internal_publications=" ^
          Int.toString (!internal_publications) ^
        " " ^ name ^ "_internal_retained=" ^ Int.toString (!retained) ^
        " " ^ name ^ "_internal_peak=" ^ Int.toString (!peak_retained) ^
        " " ^ name ^ "_evicted=" ^ Int.toString (!evicted) ^
        " " ^ name ^ "_failed=" ^ Int.toString (!failures) ^
        " " ^ name ^ "_lookup_ms=" ^
          LargeInt.toString (Time.toMilliseconds (!elapsed))
    in (procedure, stats) end

end
