(* Exact, bounded suffix sharing for the labelled cofactor map proofs. *)
structure Comma_Semantic_B1_Vector_Suffix_Cache =
struct
  structure Key = Table(type key = int * int val ord = prod_ord int_ord int_ord)
  datatype node = Node of
    {children: node Inttab.table Unsynchronized.ref,
     theorem: thm option Unsynchronized.ref}

  fun make ctxt
      {columnT = columnT, column_listT = column_listT,
       cofactor_const = cofactor_const, number = number,
       column_value = column_value, dag = dag, node_count = node_count,
       cofactor_transition = cofactor_transition, cache_limit = cache_limit,
       check_equation = check_equation, note_transition_edge = note_transition_edge} =
    let
      val natT = @{typ nat}
      val cache = Unsynchronized.ref (Key.empty: node Key.table)
      val nodes = Unsynchronized.ref 0
      val hits = Unsynchronized.ref 0
      val cons_saved = Unsynchronized.ref 0
      val cons_steps = Unsynchronized.ref 0
      val refusals = Unsynchronized.ref 0
      val alias_fixture = Unsynchronized.ref (NONE:
        (int * int * int list * (int * thm) Inttab.table * thm) option)
      val alias_runs = Unsynchronized.ref 0
      val alias_checked = Unsynchronized.ref false
      val alias_hits = Unsynchronized.ref 0
      val alias_saved = Unsynchronized.ref 0
      val alias_prefix_steps = Unsynchronized.ref 0
      val alias_warm_saved = Unsynchronized.ref 0
      fun literal_columns ids = HOLogic.mk_list columnT (map column_value ids)
      fun fresh () =
        (nodes := !nodes + 1;
         Node {children = Unsynchronized.ref Inttab.empty,
           theorem = Unsynchronized.ref NONE})

      fun prove level digit source_ids supplied_edges =
        let
          val map_nil = @{thm list.map(1)} RS @{thm eq_reflection}
          val map_cons = @{thm list.map(2)} RS @{thm eq_reflection}
          val fn_term = cofactor_const $ number level $ number digit
          val request = Const (@{const_name map},
            (columnT --> columnT) --> column_listT --> column_listT) $
              fn_term $ literal_columns source_ids
          val request_ct = Thm.cterm_of ctxt request
          val (map_fn_ct, source_ct) = Thm.dest_comb request_ct
          val (map_ct, fn_ct) = Thm.dest_comb map_fn_ct
          val _ = if (case Thm.term_of map_ct of Const (name, _) =>
                name = @{const_name map} | _ => false) andalso
              Thm.term_of fn_ct aconv fn_term then () else error
                "B1 vector cache request disagrees with its key"
          val n = length source_ids
          val edges = Unsynchronized.ref (the_default Inttab.empty supplied_edges:
            (int * thm) Inttab.table)
          val root = Key.lookup (!cache) (level, digit)
          val cursors = Array.array (n + 1, NONE: node option)
          val _ = Array.update (cursors, n, root)
          fun scan [] _ _ = ()
            | scan _ _ NONE = ()
            | scan (cid :: rest) i (SOME (Node {children, ...})) =
                let val child = Inttab.lookup (!children) cid
                    val _ = Array.update (cursors, i - 1, child)
                in scan rest (i - 1) child end
          val _ = scan (rev source_ids) n root
          fun put node theorem =
            let
              val _ = if Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem)
                  andalso null (Thm.tpairs_of theorem) then () else error
                "B1 vector suffix cache retained an open theorem"
              val Node {theorem = stored, ...} = node
            in case !stored of
              SOME _ => ()
            | NONE => stored := SOME theorem
            end
          fun root_for () =
            (case root of SOME node => SOME node
            | NONE => if !nodes < cache_limit then
                let val node = fresh ()
                    val _ = cache := Key.update ((level, digit), node) (!cache)
                in SOME node end
              else (refusals := !refusals + 1; NONE))
          fun child_for parent cid =
            (case parent of NONE => NONE
            | SOME (Node {children, ...}) =>
                (case Inttab.lookup (!children) cid of SOME node => SOME node
                | NONE => if !nodes < cache_limit then
                    let val node = fresh ()
                        val _ = children := Inttab.update (cid, node) (!children)
                    in SOME node end
                  else (refusals := !refusals + 1; NONE)))
          fun targets_of theorem =
            let
              val rhs = Thm.term_of (Thm.rhs_of theorem)
              fun target column =
                (case strip_comb column of
                  (Const (name, _), [owner, index]) =>
                    if name = @{const_name comma_semantic_b1_crt_column_at} andalso
                        owner aconv dag then
                      (case try HOLogic.dest_number index of
                        SOME (T, cid) => if T = natT andalso cid < node_count andalso
                            column aconv column_value cid then cid
                          else error "B1 cached vector has a foreign target CID"
                      | NONE => error "B1 cached vector has a symbolic target CID")
                    else error "B1 cached vector has a foreign target column"
                | _ => error "B1 cached vector has a malformed target column")
              val ids = map target (HOLogic.dest_list rhs)
              val _ = if literal_columns ids aconv rhs then () else error
                "B1 cached vector target list changed its exact columns"
            in ids end
          fun edge cid =
            (case Inttab.lookup (!edges) cid of SOME pair => pair
            | NONE =>
              let
                val {target_cid, theorem} = cofactor_transition (level, digit, cid)
                val _ = if target_cid >= 0 andalso target_cid < node_count then ()
                  else error "B1 labelled zipper edge produced a foreign CID"
                val _ = check_equation "column transition"
                  (cofactor_const $ number level $ number digit $ column_value cid)
                  (column_value target_cid) theorem
                val _ = edges := Inttab.update (cid, (target_cid, theorem)) (!edges)
                val _ = note_transition_edge ()
              in (target_cid, theorem) end)
          fun prove_at i ids source =
            let
              fun hit node theorem =
                let
                  val targets = targets_of theorem
                  val _ = if length targets = n - i then () else error
                    "B1 cached vector suffix changed occurrence count"
                  val _ = check_equation "cached vector suffix"
                    (Thm.term_of (Thm.apply map_fn_ct source))
                    (literal_columns targets) theorem
                  val saved = n - i
                  val _ = if saved > 0 then
                    (hits := !hits + 1; cons_saved := !cons_saved + saved) else ()
                in (targets, theorem, SOME node) end
              fun build () =
                if i = n then
                  (case Thm.term_of source of
                    Const (name, _) => if name = @{const_name Nil} then
                      let
                        val theorem = Conv.rewr_conv map_nil
                          (Thm.apply map_fn_ct source)
                        val _ = check_equation "empty vector map"
                          (Thm.term_of (Thm.apply map_fn_ct source))
                          (literal_columns []) theorem
                        val node = root_for ()
                        val _ = (case node of SOME item => put item theorem
                          | NONE => ())
                      in ([], theorem, node) end
                    else error "B1 vector fold ended before its source list"
                  | _ => error "B1 vector fold ended before its source list")
                else
                  (case ids of
                    [] => error "B1 vector fold ended before its source list"
                  | cid :: rest =>
                    let
                      val (cons_head, tail) = Thm.dest_comb source
                      val (cons_ct, head) = Thm.dest_comb cons_head
                      val _ = (case Thm.term_of cons_ct of
                        Const (name, _) => if name = @{const_name Cons} then ()
                          else error "B1 vector fold encountered a non-cons source"
                      | _ => error "B1 vector fold encountered a malformed source")
                      val _ = if Thm.term_of head aconv column_value cid then ()
                        else error "B1 vector fold source order changed"
                      val (tail_ids, tail_fact, tail_node) = prove_at (i + 1) rest tail
                      val (target_cid, edge_fact) = edge cid
                      val map_fact = Conv.rewr_conv map_cons
                        (Thm.apply map_fn_ct source)
                      val head_fact = Thm.combination (Thm.reflexive cons_ct) edge_fact
                      val theorem = Thm.transitive map_fact
                        (Thm.combination head_fact tail_fact)
                      val _ = cons_steps := !cons_steps + 1
                      val node = child_for tail_node cid
                      val _ = (case node of SOME item => put item theorem
                        | NONE => ())
                    in (target_cid :: tail_ids, theorem, node) end)
            in case Array.sub (cursors, i) of
              SOME (node as Node {theorem = stored, ...}) =>
                (case !stored of SOME theorem => hit node theorem | NONE => build ())
            | NONE => build ()
            end
          val (targets, theorem, _) = prove_at 0 source_ids source_ct
          val _ = check_equation "vector cofactor" request
            (literal_columns targets) theorem
          fun first_alias [] = NONE
            | first_alias [_] = NONE
            | first_alias (a :: b :: rest) =
                if a <> b then SOME (b :: a :: rest)
                else Option.map (fn tail => a :: tail) (first_alias (b :: rest))
          val complete = forall (fn cid => is_some (Inttab.lookup (!edges) cid))
            (distinct (op =) source_ids)
          val candidate = if n >= 4 andalso complete then
            Option.map (fn prefix => prefix @ [List.last source_ids])
              (first_alias (take (n - 1) source_ids))
            else NONE
          val _ = (case (!alias_fixture, candidate) of
            (NONE, SOME _) => alias_fixture :=
              SOME (level, digit, source_ids, !edges, theorem)
          | _ => ())
        in (targets, theorem) end

      fun check_alias_fixture () =
        if !alias_checked then ()
        else (case !alias_fixture of
          NONE => error "B1 vector cache did not capture an alias fixture"
        | SOME (level, digit, owner_ids, edge_facts, owner_theorem) =>
          let
            fun find_swap [] _ = NONE
              | find_swap [_] _ = NONE
              | find_swap (a :: b :: rest) i =
                  if a <> b then SOME (i, b :: a :: rest)
                  else Option.map (fn (j, tail) => (j, a :: tail))
                    (find_swap (b :: rest) (i + 1))
            val n = length owner_ids
            val (swap_at, alias_prefix) =
              (case find_swap (take (n - 1) owner_ids) 0 of
                SOME pair => pair
              | NONE => error "B1 vector alias fixture has no distinct prefix pair")
            val alias_ids = alias_prefix @ [List.last owner_ids]
            val _ = if owner_ids <> alias_ids andalso
                sort int_ord owner_ids = sort int_ord alias_ids then () else error
              "B1 vector alias fixture changed its multiset identity"
            val saved_cache = !cache
            val saved_nodes = !nodes
            val saved_hits = !hits
            val saved_cons_saved = !cons_saved
            val saved_cons_steps = !cons_steps
            val saved_refusals = !refusals
            val _ = cache := Key.empty
            val _ = nodes := 0
            val _ = hits := 0
            val _ = cons_saved := 0
            val _ = cons_steps := 0
            val _ = refusals := 0
            fun run () =
              let
                val (owner_targets, owner_fact) = prove level digit owner_ids
                  (SOME edge_facts)
                val owner_expected = Const (@{const_name map},
                  (columnT --> columnT) --> column_listT --> column_listT) $
                  (cofactor_const $ number level $ number digit) $
                  literal_columns owner_ids
                val owner_fact = check_equation "vector alias owner" owner_expected
                  (literal_columns owner_targets) owner_fact
                val _ = if Thm.prop_of owner_fact aconv Thm.prop_of owner_theorem andalso
                    Thm.nprems_of owner_fact = 0 then () else error
                  "B1 vector alias owner replay changed its theorem"
                val owner_steps = !cons_steps
                val hits_before = !hits
                val saved_before = !cons_saved
                val (alias_targets, alias_fact) = prove level digit alias_ids
                  (SOME edge_facts)
                val alias_expected = Const (@{const_name map},
                  (columnT --> columnT) --> column_listT --> column_listT) $
                  (cofactor_const $ number level $ number digit) $
                  literal_columns alias_ids
                val alias_fact = check_equation "permuted vector alias" alias_expected
                  (literal_columns alias_targets) alias_fact
                val prefix_steps = !cons_steps - owner_steps
                val alias_hits = !hits - hits_before
                val alias_saved = !cons_saved - saved_before
                val expected_saved = n - (swap_at + 2)
                val _ = if alias_hits > 0 andalso alias_saved >= expected_saved andalso
                    prefix_steps = swap_at + 2 then () else error
                  "B1 permuted vector alias missed its exact shared suffix"
                val warm_steps = !cons_steps
                val warm_hits = !hits
                val (warm_targets, warm_fact) = prove level digit alias_ids
                  (SOME edge_facts)
                val warm_fact = check_equation "warm permuted vector alias"
                  alias_expected (literal_columns warm_targets) warm_fact
                val warm_saved = !cons_saved - alias_saved - saved_before
                val _ = if Thm.prop_of warm_fact aconv Thm.prop_of alias_fact andalso
                    !cons_steps = warm_steps andalso !hits > warm_hits andalso
                    warm_saved >= n then () else error
                  "B1 warm vector alias rebuilt structural map work"
              in (alias_hits, alias_saved, prefix_steps, warm_saved) end
            val result = Exn.capture run ()
            val _ = cache := saved_cache
            val _ = nodes := saved_nodes
            val _ = hits := saved_hits
            val _ = cons_saved := saved_cons_saved
            val _ = cons_steps := saved_cons_steps
            val _ = refusals := saved_refusals
            val (h, s, p, w) = Exn.release result
            val _ = alias_hits := h
            val _ = alias_saved := s
            val _ = alias_prefix_steps := p
            val _ = alias_warm_saved := w
            val _ = alias_runs := !alias_runs + 1
            val _ = alias_checked := true
          in () end)
      fun stats () =
        " labelled_zip_vector_suffix_trie_nodes=" ^ Int.toString (!nodes) ^
        " labelled_zip_vector_suffix_hits=" ^ Int.toString (!hits) ^
        " labelled_zip_vector_suffix_cons_saved=" ^ Int.toString (!cons_saved) ^
        " labelled_zip_vector_map_cons_steps=" ^ Int.toString (!cons_steps) ^
        " labelled_zip_vector_suffix_refusals=" ^ Int.toString (!refusals) ^
        " labelled_zip_vector_alias_fixture_runs=" ^ Int.toString (!alias_runs) ^
        " labelled_zip_vector_alias_fixture_hits=" ^ Int.toString (!alias_hits) ^
        " labelled_zip_vector_alias_fixture_cons_saved=" ^ Int.toString (!alias_saved) ^
        " labelled_zip_vector_alias_fixture_prefix_cons=" ^
          Int.toString (!alias_prefix_steps) ^
        " labelled_zip_vector_alias_fixture_warm_cons_saved=" ^
          Int.toString (!alias_warm_saved)
    in {prove = prove, check_alias_fixture = check_alias_fixture, stats = stats} end
end
