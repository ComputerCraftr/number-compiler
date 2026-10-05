(* Source-selected graph discovery.  Only local period slots are evaluated;
   exact source addresses bind an occurrence to an interned child-CID node. *)
structure Comma_Semantic_Graph_Constructor =
struct
  datatype edge = Goto of int | Live of int | Stop of int
  type node = {period: int, actions: edge list}
  type binding = {source: term, cid: int}
  type audit_binding = {source: term, cid: int, row: thm}
  type engine =
    {root: int -> int, compile: term -> int,
     nodes: unit -> (int * node) list, bindings: unit -> binding list,
     rows: unit -> thm list, stats: unit -> string}

  fun make_audit ctxt : engine =
    let
      val kernel = Comma_Fast_Kernel.make ctxt
      val endpoint = Comma_Decisive_Endpoint_Kernel.make ctxt (#context kernel)
      val evaluation = #context endpoint addsimps
        @{thms comma_source_continuation_action_of_packet.simps
          comma_source_continuation_base.simps comma_source_continuation_shift.simps
          comma_decisive_endpoint_packet_def comma_round_crossing_def
          comma_offset_orbit_def comma_digit_orbit_sum_def
          comma_offset_representatives_def comma_source_continuation_id_def
          list.map upt_rec power2_eq_square of_nat_numeral of_nat_0
          of_nat_1 zmod_zminus1_eq_if zmod_zminus2_eq_if Let_def}
      fun nat n = HOLogic.mk_number @{typ nat} n
      fun number term =
        let val (T, n) = HOLogic.dest_number term
        in if T = @{typ nat} andalso n >= 0 then n
          else error "Semantic graph expected a natural literal" end
      fun equation expression =
        let val theorem = Simplifier.full_rewrite evaluation (Thm.cterm_of ctxt expression)
        in if Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem) andalso
            Thm.term_of (Thm.lhs_of theorem) aconv expression then theorem
          else error "Semantic graph local equation lost source authority" end
      fun value expression = Thm.term_of (Thm.rhs_of (equation expression))
      val source_action_memo = Unsynchronized.ref (Termtab.empty: thm Termtab.table)
      val source_action_hits = Unsynchronized.ref 0
      val source_action_misses = Unsynchronized.ref 0
      fun exact_action request theorem =
        if Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem) andalso
            Thm.term_of (Thm.lhs_of theorem) aconv request then theorem
        else error "Semantic graph local action lost its checked source"
      fun source_action_data source =
        let
          val base = @{term comma_source_continuation_base} $ source
          (* Normalize the source address once, then use that literal at every
             local arithmetic boundary.  This keeps the cached action and
             period equations aligned with the arguments after the ID's base
             field is unfolded. *)
          val base_value = value base
          val period_request = @{term comma_decisive_sector_period} $ base_value
          val period_theorem = equation period_request
          val period = number (Thm.term_of (Thm.rhs_of period_theorem))
          val _ = if period > 0 andalso 924 mod period = 0 then ()
            else error "Semantic source period is not admitted"
          val action_of_packet = @{term comma_source_continuation_action_of_packet}
          fun action_request phase = action_of_packet $
            (@{term comma_decisive_endpoint_packet} $ nat phase $ base_value)
          fun checked_action phase =
            let
              val request = action_request phase
            in
              (case Termtab.lookup (!source_action_memo) request of
                SOME theorem =>
                  (source_action_hits := !source_action_hits + 1;
                   exact_action request theorem)
              | NONE =>
                  let
                    val _ = source_action_misses := !source_action_misses + 1
                    val theorem = equation request |> exact_action request
                    val _ = if Termtab.size (!source_action_memo) < 8192 then
                        source_action_memo := Termtab.update
                          (request, theorem) (!source_action_memo)
                      else ()
                  in theorem end)
            end
          val action_theorems = map checked_action (0 upto (period - 1))
          (* Arithmetic is checked once per local action above.  The row join
             only unfolds the source-ID definition, substitutes those closed
             action equations, and evaluates the bounded map/range. *)
        in (period, period_theorem, action_theorems) end
      fun source_row_equation source (period_theorem, action_theorems) =
        let
          val expression = @{term comma_source_continuation_id} $ source
          (* This complete-row certificate is an explicit audit path only.
             Production discovery consumes candidate data from local actions
             and never constructs or retains this physical-row theorem. *)
          val row_context = Comma_Entry_Arithmetic.natural_context ctxt addsimps
            ([period_theorem] @ action_theorems @
              @{thms comma_source_continuation_id_def
                comma_source_continuation_base.simps list.map upt_rec Let_def})
          val theorem = Simplifier.full_rewrite row_context
            (Thm.cterm_of ctxt expression)
        in
          if Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem) andalso
              Thm.term_of (Thm.lhs_of theorem) aconv expression then theorem
          else error "Semantic graph source-row join lost its exact request"
        end
      fun source_shape source =
        (case strip_comb source of
          (Const (name, _), [f, delta, coordinate]) =>
            if (name = @{const_name Comma_Entry} orelse name = @{const_name Comma_Near})
                andalso number delta = 0 then (name, number f, number coordinate)
            else error "Semantic source is not in its normalized chart"
        | _ => error "Semantic graph source is not a literal chart")
      val bindings = Unsynchronized.ref (Termtab.empty: binding Termtab.table)
      val audit_source_rows = Unsynchronized.ref (Termtab.empty: thm Termtab.table)
      val active = Unsynchronized.ref (Termtab.empty: unit Termtab.table)
      val nodes = Unsynchronized.ref (Inttab.empty: node Inttab.table)
      val signatures = Unsynchronized.ref (Termtab.empty: int Termtab.table)
      val local_slots = Unsynchronized.ref 0
      val reused = Unsynchronized.ref 0
      fun minimum_period actions =
        let val n = length actions
          fun matches p = n mod p = 0 andalso
            List.all (fn j => nth actions j = nth actions (j mod p)) (0 upto (n-1))
        in the (find_first matches (1 upto n)) end
      fun intern actions =
        let val p = minimum_period actions
          val node = {period = p, actions = take p actions}
          fun edge_key (Goto cid) = HOLogic.mk_prod (nat 0, nat cid)
            | edge_key (Live root) = HOLogic.mk_prod (nat 1, nat root)
            | edge_key (Stop j) = HOLogic.mk_prod (nat 2, nat j)
          val key = HOLogic.mk_list (HOLogic.mk_prodT (@{typ nat}, @{typ nat}))
            (map edge_key (#actions node))
        in case Termtab.lookup (!signatures) key of
          SOME cid => (reused := !reused + 1; cid)
        | NONE => let val cid = Inttab.size (!nodes)
            val _ = nodes := Inttab.update (cid, node) (!nodes)
            val _ = signatures := Termtab.update (key, cid) (!signatures)
          in cid end end
      fun compile source =
        (case Termtab.lookup (!bindings) source of
          SOME item => #cid item
        | NONE =>
          let
            val (_, sector, _) = source_shape source
            val _ = if Termtab.defined (!active) source then
              error "Semantic source graph contains a cycle" else ()
            val _ = active := Termtab.update (source, ()) (!active)
            fun build () =
              let
                val (period, period_theorem, action_theorems) =
                  source_action_data source
                val actions = map (Thm.term_of o Thm.rhs_of) action_theorems
                val _ = if period > 0 andalso 924 mod period = 0 andalso
                  length actions = period then ()
                  else error "Semantic source candidate period is not admitted"
                val theorem = source_row_equation source
                  (period_theorem, action_theorems)
                val expression = @{term comma_source_continuation_id} $ source
                val _ = if Thm.term_of (Thm.lhs_of theorem) aconv expression then ()
                  else error "Semantic audit row lost its exact source"
                val _ = audit_source_rows :=
                  Termtab.update (source, theorem) (!audit_source_rows)
                fun slot (phase, action) =
                  let
                    val _ = local_slots := !local_slots + 1
                    val edge = (case strip_comb action of
                      (Const (name, _), [next, shift]) =>
                        if name = @{const_name Comma_Continuation_Goto} then
                          let val (_, next_sector, _) = source_shape next
                            val _ = if number shift = 0 andalso sector < next_sector
                              then () else error "Goto fails strict sector progress"
                          in Goto (compile next) end
                        else if name = @{const_name Comma_Continuation_Exit} then
                          let val (kind, next_sector, offset) = source_shape next
                            val _ = if kind = @{const_name Comma_Entry} andalso
                              next_sector = 1 andalso number shift = 1 andalso offset <= 90
                              then () else error "Live result lost its root binding"
                            val root = number (value (@{term comma_offset_orbit} $ nat offset))
                          in if root < 46 then Live root else error "Live root out of range" end
                        else if name = @{const_name Comma_Continuation_Fork} then
                          let val a = number next
                          in if number shift = 0 andalso 2 <= a andalso a <= 9
                            then Stop (a-2) else error "Fork is outside its exact local band" end
                        else error "Unrecognized semantic continuation action"
                    | (Const (name, _), [shift]) =>
                        if name = @{const_name Comma_Continuation_Landmine} andalso
                          number shift = 0 then Stop 8
                        else error ("Unreduced local continuation: " ^
                          Syntax.string_of_term ctxt action ^ " from " ^
                          Syntax.string_of_term ctxt source ^ " phase=" ^ Int.toString phase)
                    | _ => error "Invalid or unevaluated semantic continuation action")
                  in edge end
                val slots = map slot (map_index I actions)
                val cid = intern slots
                val _ = bindings := Termtab.update
                  (source, {source=source, cid=cid}) (!bindings)
                val _ = if Termtab.size (!bindings) mod 32 = 0 then
                  Comma_Fast_Kernel.report ("semantic_sources=" ^
                    Int.toString (Termtab.size (!bindings)) ^ " slots=" ^
                    Int.toString (!local_slots) ^ " " ^ #stats endpoint ()) else ()
              in cid end
            val attempt = Exn.capture build ()
            val _ = active := Termtab.delete source (!active)
          in Exn.release attempt end)
      val reps = HOLogic.dest_list (value @{term comma_offset_representatives})
      fun root i =
        if 0 <= i andalso i < length reps then
          compile (@{term Comma_Entry} $ nat 1 $ nat 0 $ nth reps i)
        else error "Semantic root outside representative domain"
      fun stats () = "semantic_sources=" ^ Int.toString (Termtab.size (!bindings)) ^
        " semantic_nodes=" ^ Int.toString (Inttab.size (!nodes)) ^
        " semantic_local_slots=" ^ Int.toString (!local_slots) ^
        " semantic_intern_hits=" ^ Int.toString (!reused) ^
        " semantic_action_hits=" ^ Int.toString (!source_action_hits) ^
        " semantic_action_misses=" ^ Int.toString (!source_action_misses) ^
        " semantic_action_retained=" ^ Int.toString (Termtab.size (!source_action_memo)) ^
        " semantic_audit_rows=" ^ Int.toString (Termtab.size (!audit_source_rows)) ^
        " " ^ #stats endpoint ()
    in {root=root, compile=compile, nodes=fn () => Inttab.dest (!nodes),
      bindings=fn () => map #2 (Termtab.dest (!bindings)),
      rows=fn () => map #2 (Termtab.dest (!audit_source_rows)),
      stats=stats} end

  (* This constructor is exclusively the physical graph audit owner.
     Production B1 candidate discovery is performed from the source-level
     scoped-row transform and must not call this proof-producing traversal. *)
end
