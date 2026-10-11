(*
  Proof-dependency checks for release-owned theorems.

  This uses Isabelle's kernel dependency walker rather than inspecting imported
  theory source files. Imported theories may contain an audit-only forest,
  fuel, candidate, or structural theorem without making it a dependency of
  the theorem being released. Conversely, a theorem is rejected when its
  proof term actually reaches one of those retired production authorities.
  The native release gate is intentionally strict. The narrower
  fuel/forest check below is only a diagnostic audit and must never certify a
  release endpoint.
*)

structure Comma_Proof_Dependency_Audit =
struct

  val fuel_forest_paths =
    ["Comma_Root_Forest",
     "comma_root_forest",
     "Comma_Forest_Legacy",
     "Comma_Branch_Termination",
     "comma_forest_certificate",
     "comma_finite_run",
     "comma_finite_macro",
     "comma_finite_children",
     "comma_finite_weighted_run",
     "comma_finite_weighted_macro",
     "comma_decisive_endpoint_round_refines_fast",
     "comma_fast_round_aux",
     "comma_fast_boundary_run",
     "comma_total_macro",
     "comma_total_weighted_macro"]

  val candidate_paths =
    ["comma_decade_rank_candidate",
     "comma_decade_terminal_candidate",
     "comma_decade_summary_candidate",
     "comma_rank_candidate",
     "comma_rank_code_at"]

  val structural_paths =
    ["Comma_Future_Structural_Check",
     "Comma_Future_Structural_Instance",
     "comma_future_structural_candidate",
     "comma_future_structural_witness",
     "comma_future_structural_defined",
     "comma_future_structural_descent",
     "comma_future_descent_check",
     "comma_future_descent_row",
     "comma_structural_loser_no_infinite_literal_path",
     "comma_structural_survivor_infinite_literal_path",
     "comma_source20_structural_infinite_path",
     "comma_source20_structural_first_choice_unique"]

  val native_paths = fuel_forest_paths @ candidate_paths @ structural_paths

  fun retired paths name =
    exists (fn path => String.isSubstring path name) paths

  (* Check oracle use while collecting the same transitive named-dependency
     graph.  The per-call serial table is deliberately local: each endpoint
     group keeps an independent reachability result. *)
  fun checked_names thy label thms =
    let
      fun add_oracles [] oracle_sets = oracle_sets
        | add_oracles oracles oracle_sets = oracles :: oracle_sets

      fun visit [] seen found oracle_sets = (seen, found, oracle_sets)
        | visit ((serial, node) :: pending) seen found oracle_sets =
            if Inttab.defined seen serial then
              visit pending seen found oracle_sets
            else
              let
                val seen' = Inttab.update (serial, ()) seen
                val name = Thm_Name.print (Proofterm.thm_node_name node)
                val node_name = Proofterm.thm_node_name node
                val found' =
                  if Thm_Name.is_empty node_name then found
                  else Symtab.update (name, ()) found
                val PBody {oracles, thms = children, ...} =
                  Future.join (Proofterm.thm_node_body node)
                val oracle_sets' = add_oracles oracles oracle_sets
                val _ = Proofterm.join_thms children
              in
                visit (children @ pending) seen' found' oracle_sets'
              end

      val transferred = map (Thm.transfer thy) thms
      val root_bodies = map Thm.proof_body_of transferred
      val roots = maps Thm.thm_deps transferred
      val root_oracles = maps (fn PBody {oracles, ...} => [oracles]) root_bodies
      val _ = Proofterm.join_thms roots
      val (_, found, oracle_sets) =
        visit roots Inttab.empty Symtab.empty root_oracles
      val oracles = Proofterm.unions_oracles oracle_sets
    in
      if null oracles then Symtab.keys found
      else error (label ^ " depends on an Isabelle oracle")
    end

  (* Resolve the caller's xstrings through the active context before comparing
     them with proof-term names.  This keeps namespace/index handling in
     Isabelle's fact resolver and leaves the final comparison exact. *)
  fun expected_names ctxt expected =
    maps (fn wanted =>
      let
        val resolved = Proof_Context.get_thms ctxt wanted
        val names = map (Thm_Name.print o Thm.derivation_name) resolved
      in
        if null names orelse exists (fn name => name = "") names then
          error ("expected authority is not a named theorem: " ^ wanted)
        else names
      end) expected
    |> distinct (op =)

  fun check_hypotheses label thms =
    if forall (null o Thm.hyps_of) thms then ()
    else error (label ^ " endpoint has hypotheses")

  fun check_premises label thms =
    if forall (fn thm => Thm.nprems_of thm = 0) thms then ()
    else error (label ^ " endpoint has theorem premises")

  fun check_expected_names ctxt label expected actual =
    let
      val _ = if null expected then
          error (label ^ " has no expected theorem authorities")
        else ()
      val required = expected_names ctxt expected
      val missing = filter (fn wanted => not (member (op =) actual wanted)) required
    in
      if null missing then ()
      else error (label ^ " is missing exact theorem authorities: " ^
        space_implode ", " missing)
    end

  fun check_paths label paths actual =
    let val bad = filter (retired paths) actual in
      if null bad then ()
      else error (label ^ " depends on retired production paths: " ^
        space_implode ", " bad)
    end

  fun require_paths ctxt label paths thms =
    let
      val thy = Proof_Context.theory_of ctxt
      val actual = checked_names thy label thms
    in
      check_paths label paths actual
    end

  fun require_native_clean ctxt label thms =
    require_paths ctxt label native_paths thms

  fun require_expected_paths ctxt label expected thms =
    let
      val thy = Proof_Context.theory_of ctxt
      val _ = if null expected then
          error (label ^ " has no expected theorem authorities")
        else ()
      val _ = if null thms then
          error (label ^ " has no endpoint theorems")
        else ()
      val _ = check_hypotheses label thms
      val actual = checked_names thy label thms
    in
      check_expected_names ctxt label expected actual
    end

  fun require_closed_expected_paths ctxt label expected thms =
    let
      val _ = require_expected_paths ctxt label expected thms
      val _ = check_premises label thms
    in () end

  (* One-pass endpoint gate for release theorems that must be closed, depend
     on named semantic authorities, and avoid every retired production path.
     The proof-term graph and oracle closure are each traversed exactly once. *)
  fun require_native_closed_expected_paths ctxt label expected thms =
    let
      val thy = Proof_Context.theory_of ctxt
      val _ = if null expected then
          error (label ^ " has no expected theorem authorities")
        else ()
      val _ = if null thms then
          error (label ^ " has no endpoint theorems")
        else ()
      val _ = check_hypotheses label thms
      val _ = check_premises label thms
      val actual = checked_names thy label thms
      val _ = check_paths label native_paths actual
    in
      check_expected_names ctxt label expected actual
    end

  fun audit_fuel_free_global ctxt label thms =
    require_paths ctxt label fuel_forest_paths thms

end
