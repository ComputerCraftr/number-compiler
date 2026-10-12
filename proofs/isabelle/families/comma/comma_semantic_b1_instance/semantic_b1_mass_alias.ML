(* Exact publication-boundary checks for the named sparse mass annotation. *)
structure Comma_Semantic_B1_Mass_Alias =
struct
  type alias = Comma_Semantic_B1_Occurrence_Publication.mass_annotation

  local
    fun validate_roots node_count body_table roots =
      let
        val _ = if node_count >= 2 then () else
          error "B1 mass annotation alias has an invalid DAG extent"
        fun add_root cid table =
          if Inttab.defined table cid then
            error "B1 mass annotation alias repeats a demanded root"
          else Inttab.update (cid, ()) table
        val _ = fold add_root roots Inttab.empty
        val _ = if forall (fn cid => cid >= 0 andalso cid < node_count andalso
            (cid < 2 orelse Inttab.defined body_table cid)) roots then () else
          error "B1 mass annotation alias carries a foreign demanded root"
      in () end
  in

  fun validate ctxt node_count
      ({constant, body, definition, cids, roots}: alias) =
    let
      val treeT = @{typ comma_semantic_b1_crt_mass_tree}
      val thy = Proof_Context.theory_of ctxt
      val name = Sign.intern_const thy
        "comma_semantic_b1_crt_mass_annotation_tree"
      val equation = Local_Defs.meta_rewrite_rule ctxt definition
      val left = Thm.term_of (Thm.lhs_of equation)
      val right = Thm.term_of (Thm.rhs_of equation)
      val _ = if (case constant of Const (actual, typ) =>
          actual = name andalso typ = treeT | _ => false) then () else
        error "B1 mass annotation alias has the wrong constant"
      val _ = if fastype_of body = treeT andalso
          Comma_Semantic_B1_Column_Conversion.closed body then () else
        error "B1 mass annotation alias body is open or ill-typed"
      val _ = if left aconv constant andalso right aconv body then () else
        error "B1 mass annotation alias definition changed its exact body"
      val _ = if Thm.nprems_of equation = 0 andalso null (Thm.hyps_of equation) andalso
          null (Thm.tpairs_of equation) andalso
          Context.subthy (Thm.theory_of_thm definition, thy) andalso
          null (Thm_Deps.all_oracles [definition]) then () else
        error "B1 mass annotation alias definition is not a clean local theorem"
      val body_cids = Comma_Semantic_B1_Mass_Candidate.tree_cids body
      val body_table = Inttab.make (map (fn cid => (cid, ())) body_cids)
      val _ = if body_cids = cids andalso
          forall (fn cid => cid >= 2 andalso cid < node_count) cids then () else
        error "B1 mass annotation alias carries a foreign or duplicate CID"
      (* False/True roots have independent checked mass equations and no
         annotation row. Only nonterminal roots require a retained row. *)
      val _ = validate_roots node_count body_table roots
    in (constant, body, equation, cids, roots) end

  fun check_fixtures ctxt node_count (annotation: alias) =
    let
      fun expect_error expected label operation =
        (case Exn.capture operation () of
          Exn.Exn (ERROR message) => if message = expected then ()
            else error (label ^ " failed for the wrong reason: " ^ message)
        | Exn.Exn exn => Exn.reraise exn
        | Exn.Res _ => error (label ^ " was unexpectedly accepted"))
      val _ = validate ctxt node_count annotation
      val terminals = {constant = #constant annotation, body = #body annotation,
        definition = #definition annotation, cids = #cids annotation,
        roots = [0, 1]}: alias
      val _ = validate ctxt node_count terminals
      val isolated_body = Inttab.make [(2, ())]
      val _ = validate_roots 4 isolated_body [0, 1, 2]
      fun expect_root_error expected label domain roots =
        (case Exn.capture (fn () => validate_roots domain isolated_body roots) () of
          Exn.Exn (ERROR message) => if message = expected then ()
            else error (label ^ " failed for the wrong reason: " ^ message)
        | Exn.Exn exn => Exn.reraise exn
        | Exn.Res _ => error (label ^ " was unexpectedly accepted"))
      val _ = expect_root_error
        "B1 mass annotation alias carries a foreign demanded root"
        "negative demanded root" 4 [~1]
      val _ = expect_root_error
        "B1 mass annotation alias carries a foreign demanded root"
        "missing nonterminal annotation root" 4 [3]
      val _ = expect_root_error
        "B1 mass annotation alias repeats a demanded root"
        "duplicate demanded root" 4 [0, 0]
      val _ = expect_root_error
        "B1 mass annotation alias has an invalid DAG extent"
        "undersized DAG extent" 1 []
      val wrong_constant =
        {constant = @{term True}, body = #body annotation,
         definition = #definition annotation, cids = #cids annotation,
         roots = #roots annotation}: alias
      val _ = expect_error "B1 mass annotation alias has the wrong constant"
        "wrong alias constant" (fn () => validate ctxt node_count wrong_constant)
      val wrong_body =
        {constant = #constant annotation,
         body = @{term Comma_B1_CRT_Mass_Tree_Empty},
         definition = #definition annotation, cids = #cids annotation,
         roots = #roots annotation}: alias
      val _ = expect_error "B1 mass annotation alias definition changed its exact body"
        "wrong alias body" (fn () => validate ctxt node_count wrong_body)
      val wrong_definition =
        {constant = #constant annotation, body = #body annotation,
         definition = Thm.reflexive (Thm.cterm_of ctxt (#constant annotation)),
         cids = #cids annotation, roots = #roots annotation}: alias
      val _ = expect_error "B1 mass annotation alias definition changed its exact body"
        "wrong alias definition"
        (fn () => validate ctxt node_count wrong_definition)
      val missing_cid =
        (case #cids annotation of
          [] => [2]
        | _ :: tail => tail)
      val missing = {constant = #constant annotation, body = #body annotation,
        definition = #definition annotation, cids = missing_cid,
        roots = #roots annotation}: alias
      val _ = expect_error "B1 mass annotation alias carries a foreign or duplicate CID"
        "missing alias CID" (fn () => validate ctxt node_count missing)
      val duplicate = {constant = #constant annotation, body = #body annotation,
        definition = #definition annotation,
        cids = (case #cids annotation of [] => [2, 2] |
          first :: _ => first :: (#cids annotation)),
        roots = #roots annotation}: alias
      val _ = expect_error "B1 mass annotation alias carries a foreign or duplicate CID"
        "duplicate alias CID" (fn () => validate ctxt node_count duplicate)
      val foreign = {constant = #constant annotation, body = #body annotation,
        definition = #definition annotation, cids = node_count :: (#cids annotation),
        roots = #roots annotation}: alias
      val _ = expect_error "B1 mass annotation alias carries a foreign or duplicate CID"
        "foreign alias CID" (fn () => validate ctxt node_count foreign)
      val foreign_root = {constant = #constant annotation, body = #body annotation,
        definition = #definition annotation, cids = #cids annotation,
        roots = node_count :: (#roots annotation)}: alias
      val _ = expect_error "B1 mass annotation alias carries a foreign demanded root"
        "foreign alias root" (fn () => validate ctxt node_count foreign_root)
    in () end
  end
end
