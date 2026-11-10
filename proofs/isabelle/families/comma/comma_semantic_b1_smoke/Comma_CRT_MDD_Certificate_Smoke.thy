theory Comma_CRT_MDD_Certificate_Smoke
  imports Comma_Frontier24_Certificate_Smoke
begin

text \<open>Small executable authority and reuse regressions for the shared
MDD certificate API. These fixture tables are not production proof data.\<close>

lemma comma_mdd_boolean_leaf_false_maps_zero:
  "comma_crt_mdd_root_map_certificate [2]
      [Comma_CRT_MDD_Leaf False] [Comma_CRT_MDD_Leaf (0::nat)]
      (\<lambda>flag. if flag then 1 else 0) 0 0"
  by (rule comma_crt_mdd_root_map_certificate.map_leaf[where payload=False])
     simp_all

lemma comma_mdd_boolean_leaf_true_maps_one:
  "comma_crt_mdd_root_map_certificate [2]
      [Comma_CRT_MDD_Leaf True] [Comma_CRT_MDD_Leaf (1::nat)]
      (\<lambda>flag. if flag then 1 else 0) 0 0"
  by (rule comma_crt_mdd_root_map_certificate.map_leaf[where payload=True])
     simp_all

ML \<open>
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Boolean MDD leaf encoding maps False to zero and True to one"
    @{thms comma_mdd_boolean_leaf_false_maps_zero
      comma_mdd_boolean_leaf_true_maps_one};
\<close>

local_setup \<open>fn lthy =>
  let
    val arena = Comma_CRT_MDD_Arena.create [4,2]
    val low = Comma_CRT_MDD_Arena.boolean_false arena
    val high = Comma_CRT_MDD_Arena.boolean_true arena
    val root = Comma_CRT_MDD_Arena.boolean_branch arena 1 [low,high]
    val shifted = Comma_CRT_MDD_Arena.shift_boolean arena root 1
    val action = Comma_CRT_MDD_Arena.action_branch arena 0
      [Comma_CRT_MDD_Arena.action_some arena 0, Comma_CRT_MDD_Arena.action_none arena,
       Comma_CRT_MDD_Arena.action_some arena 0, Comma_CRT_MDD_Arena.action_none arena]
    val sharing_action = Comma_CRT_MDD_Arena.action_branch arena 0
      [Comma_CRT_MDD_Arena.action_some arena 0, Comma_CRT_MDD_Arena.action_some arena 1,
       Comma_CRT_MDD_Arena.action_some arena 0, Comma_CRT_MDD_Arena.action_some arena 1]
    val bound_root = Comma_CRT_MDD_Arena.bind_action_to_boolean arena action low [(0,root)]
    val reused_root = Comma_CRT_MDD_Arena.bind_action_to_boolean arena action low [(0,root)]
    val alias_root = Comma_CRT_MDD_Arena.bind_action_to_boolean arena action root [(0,root)]
    val _ = Comma_CRT_MDD_Arena.bind_action_to_boolean arena sharing_action low [(0,root)]
    val _ = Comma_CRT_MDD_Arena.bind_action_to_boolean arena sharing_action low [(1,root)]
    val _ = Comma_CRT_MDD_Arena.bind_action_to_boolean arena sharing_action low
      [(0,root),(1,shifted)]
    val _ = Comma_CRT_MDD_Arena.bind_action_to_boolean arena sharing_action root
      [(0,root),(1,shifted)]
    val _ = if Comma_CRT_MDD_Arena.boolean_index arena alias_root =
        Comma_CRT_MDD_Arena.boolean_index arena root then ()
      else error "MDD bind did not reduce a common branch child"
    val _ = if Comma_CRT_MDD_Arena.boolean_index arena bound_root =
        Comma_CRT_MDD_Arena.boolean_index arena reused_root then ()
      else error "MDD bind parent reuse changed its result"
    val _ = writeln "MDD certificate fixture: freezing store"
    val (store,lthy') = Comma_CRT_MDD_Certificate_Store.make
      "comma_mdd_certificate_example_nodes" arena lthy
      handle ERROR message => error ("MDD fixture store: " ^ message)
    val index = Comma_CRT_MDD_Certificate_Store.boolean_index store root
    val _ = Comma_CRT_MDD_Certificate_Store.lookup store index
    val shifted_index = Comma_CRT_MDD_Certificate_Store.boolean_index store shifted
    val bind_key = (Comma_CRT_MDD_Certificate_Store.action_index store action,
      Comma_CRT_MDD_Certificate_Store.boolean_index store low, [(1,index)])
    val witness = Comma_CRT_MDD_Certificate_Store.bind_witness store bind_key
    val _ = if #result witness =
        Comma_CRT_MDD_Certificate_Store.boolean_index store bound_root then ()
      else error "MDD bind witness changed the published result"
    val _ = writeln "MDD certificate fixture: checking shift"
    val replay = Comma_CRT_MDD_Operation_Replay.make store
    val shift_exact = Comma_CRT_MDD_Operation_Replay.shift_eval_phase
      replay 1 index shifted_index
      handle ERROR message => error ("MDD fixture shift: " ^ message)
    val shift_stats = Comma_CRT_MDD_Operation_Replay.statistics replay
    val _ = Comma_CRT_MDD_Operation_Replay.shift_eval_phase replay 1 index shifted_index
    val _ = if shift_stats = Comma_CRT_MDD_Operation_Replay.statistics replay then ()
      else error "MDD shift parent reuse reconstructed proof data"
    val _ = writeln "MDD certificate fixture: checking bind"
    val bind_replay = Comma_CRT_MDD_Bind_Replay.make store
    val bind_exact = Comma_CRT_MDD_Bind_Replay.bind_eval_phase bind_replay bind_key
      handle ERROR message => error ("MDD fixture bind: " ^ message)
    val alias_key = (Comma_CRT_MDD_Certificate_Store.action_index store action,
      index,[(1,index)])
    val alias_exact = Comma_CRT_MDD_Bind_Replay.bind_eval_phase bind_replay alias_key
    val bind_stats = Comma_CRT_MDD_Bind_Replay.statistics bind_replay
    val _ = Comma_CRT_MDD_Bind_Replay.bind_eval_phase bind_replay bind_key
    val _ = Comma_CRT_MDD_Bind_Replay.bind_eval_phase bind_replay alias_key
    val _ = if bind_stats = Comma_CRT_MDD_Bind_Replay.statistics bind_replay then ()
      else error "MDD bind parent reuse reconstructed proof data"
    fun statistic name report =
      let
        val prefix = name ^ "="
        val token = (case List.find (String.isPrefix prefix)
            (String.tokens (fn character => character = #" ") report) of
          SOME value => value
        | NONE => error ("MDD bind statistic is missing: " ^ name))
      in String.extract (token, String.size prefix, NONE) end
    val sharing_source = Comma_CRT_MDD_Certificate_Store.action_index store sharing_action
    val sharing_fallback = Comma_CRT_MDD_Certificate_Store.boolean_index store low
    val single_sharing_key_one = (sharing_source, sharing_fallback, [(1,index)])
    val single_sharing_key_two = (sharing_source, sharing_fallback, [(2,index)])
    val _ = Comma_CRT_MDD_Bind_Replay.certify_bind bind_replay single_sharing_key_one
    val single_sharing_stats_one = Comma_CRT_MDD_Bind_Replay.statistics bind_replay
    val _ = Comma_CRT_MDD_Bind_Replay.certify_bind bind_replay single_sharing_key_two
    val _ = Comma_CRT_MDD_Bind_Replay.bind_eval_phase bind_replay single_sharing_key_one
    val _ = Comma_CRT_MDD_Bind_Replay.bind_eval_phase bind_replay single_sharing_key_two
    val single_sharing_stats_two = Comma_CRT_MDD_Bind_Replay.statistics bind_replay
    val _ = if statistic "cofactor_family_builds" single_sharing_stats_one =
        statistic "cofactor_family_builds" single_sharing_stats_two then ()
      else error "Changing MDD mapping payloads rebuilt cofactor-family proofs"
    val sharing_mapping = [(1,index),(2,shifted_index)]
    val multi_root_key_one = (sharing_source, sharing_fallback, sharing_mapping)
    val multi_root_key_two = (sharing_source, index, sharing_mapping)
    val _ = Comma_CRT_MDD_Bind_Replay.certify_bind bind_replay multi_root_key_one
    val multi_root_stats_one = Comma_CRT_MDD_Bind_Replay.statistics bind_replay
    val _ = Comma_CRT_MDD_Bind_Replay.certify_bind bind_replay multi_root_key_two
    val _ = Comma_CRT_MDD_Bind_Replay.bind_eval_phase bind_replay multi_root_key_one
    val _ = Comma_CRT_MDD_Bind_Replay.bind_eval_phase bind_replay multi_root_key_two
    val multi_root_stats_two = Comma_CRT_MDD_Bind_Replay.statistics bind_replay
    val _ = if statistic "cofactor_family_builds" multi_root_stats_one =
        statistic "cofactor_family_builds" multi_root_stats_two then ()
      else error "Equivalent multi-root MDD operands rebuilt cofactor-family proofs"
    val _ = if statistic "mapping_family_builds" multi_root_stats_one =
        statistic "mapping_family_builds" multi_root_stats_two then ()
      else error "Warm MDD mapping rebuilt its root-family proof"
    fun rejected operation =
      (case Exn.capture operation () of
        Exn.Exn (ERROR _) => ()
      | Exn.Exn exn => Exn.reraise exn
      | Exn.Res _ => error "MDD certificate admitted an invalid root or operation")
    val leaf_index = Comma_CRT_MDD_Certificate_Store.boolean_index store low
    val leaf_phase = Comma_CRT_MDD_Certificate_Store.phase_leaf store leaf_index
    val phase = Free ("phase",@{typ nat})
    val phase_eval = Const (@{const_name comma_crt_mdd_eval_phase},
      @{typ "nat list"} --> @{typ "nat comma_crt_mdd_node list"} -->
        @{typ nat} --> @{typ nat} --> @{typ "nat option"}) $
      Comma_CRT_MDD_Certificate_Store.radices store $
      Comma_CRT_MDD_Certificate_Store.table store $ phase $
      HOLogic.mk_number @{typ nat} leaf_index
    val leaf_value = Const (@{const_name Some},
      @{typ nat} --> @{typ "nat option"}) $ HOLogic.mk_number @{typ nat} 0
    val expected_leaf_phase = Logic.all phase
      (HOLogic.mk_Trueprop (HOLogic.mk_eq (phase_eval,leaf_value)))
    val leaf_phase = Comma_CRT_MDD_Proof_Utils.exact_prop
      (Comma_CRT_MDD_Certificate_Store.context store)
      "MDD phase evaluation at a leaf" expected_leaf_phase leaf_phase
    val leaf_phase_stats = Comma_CRT_MDD_Certificate_Store.statistics store
    val _ = Comma_CRT_MDD_Certificate_Store.phase_leaf store leaf_index
    val _ = if leaf_phase_stats = Comma_CRT_MDD_Certificate_Store.statistics store then ()
      else error "MDD phase-leaf parent reuse reconstructed proof data"
    val _ = rejected (fn () => Comma_CRT_MDD_Certificate_Store.phase_leaf store index)
    val _ = rejected (fn () => Comma_CRT_MDD_Certificate_Store.phase_leaf store
      (Comma_CRT_MDD_Certificate_Store.node_count store))
    val _ = if leaf_phase_stats = Comma_CRT_MDD_Certificate_Store.statistics store then ()
      else error "Rejected MDD phase-leaf query changed the certificate cache"
    val _ = rejected (fn () =>
      Comma_CRT_MDD_Operation_Replay.certify_shift replay 1 index index)
    val _ = rejected (fn () => Comma_CRT_MDD_Bind_Replay.certify_bind bind_replay
      (Comma_CRT_MDD_Certificate_Store.action_index store action,
       Comma_CRT_MDD_Certificate_Store.boolean_index store low,[]))
    val foreign = Comma_CRT_MDD_Arena.create [2]
    val foreign_root = Comma_CRT_MDD_Arena.boolean_false foreign
    val _ = rejected (fn () =>
      Comma_CRT_MDD_Certificate_Store.boolean_index store foreign_root)
    val unpublished = Comma_CRT_MDD_Arena.boolean_branch arena 0
      [root,root,shifted,shifted]
    val _ = rejected (fn () =>
      Comma_CRT_MDD_Certificate_Store.boolean_index store unpublished)
    val _ = writeln "MDD certificate fixture: authority and reuse checks passed"
    val theorem = Comma_CRT_MDD_Certificate_Store.wellformed store
    fun note (name,fact) local_ctxt = #2 (Local_Theory.note
      ((Binding.name name,[]),[fact]) local_ctxt)
  in fold note
    [("comma_mdd_certificate_example_wellformed",theorem),
     ("comma_mdd_certificate_example_shift",shift_exact),
     ("comma_mdd_certificate_example_bind",bind_exact),
     ("comma_mdd_certificate_example_bind_branch_alias",alias_exact),
     ("comma_mdd_certificate_example_phase_leaf",leaf_phase)] lthy' end\<close>

text \<open>Source-owned Boolean guard tables may contain ordered aliases that
the shared arena reduces during import. Ordinary canonical seed/import APIs
remain strict, and the returned vector preserves every local row mapping.\<close>

local_setup \<open>fn lthy =>
  let
    val source_nodes =
      [Comma_CRT_MDD_Arena.Seed_Leaf 0,
       Comma_CRT_MDD_Arena.Seed_Leaf 1,
       Comma_CRT_MDD_Arena.Seed_Branch (0,[0,0]),
       Comma_CRT_MDD_Arena.Seed_Branch (0,[0,1])]
    val arena = Comma_CRT_MDD_Arena.create [2]
    val roots = Comma_CRT_MDD_Arena.import_boolean_guard_table_with_roots
      arena source_nodes
    val mapped = map (Comma_CRT_MDD_Arena.boolean_index arena) roots
    val _ = if mapped = [0,1,0,2] then ()
      else error "Ordered Boolean guard import lost its local-to-arena mapping"
    fun reject label action =
      (case Exn.capture action () of
        Exn.Exn (ERROR _) => ()
      | Exn.Exn exn => Exn.reraise exn
      | Exn.Res _ => error ("Canonical MDD import accepted " ^ label))
    val _ = reject "an unreduced branch"
      (fn () => ignore (Comma_CRT_MDD_Arena.import_boolean_table
        (Comma_CRT_MDD_Arena.create [2]) source_nodes 3))
    val _ = reject "an unreduced seed prefix"
      (fn () => ignore (Comma_CRT_MDD_Arena.seed_prefix
        (Comma_CRT_MDD_Arena.create [2]) source_nodes))
    val duplicate_leaves =
      [Comma_CRT_MDD_Arena.Seed_Leaf 0,
       Comma_CRT_MDD_Arena.Seed_Leaf 1,
       Comma_CRT_MDD_Arena.Seed_Leaf 0]
    val duplicate_arena = Comma_CRT_MDD_Arena.create [2]
    val duplicate_roots =
      Comma_CRT_MDD_Arena.import_boolean_guard_table_with_roots
        duplicate_arena duplicate_leaves
    val duplicate_mapping =
      map (Comma_CRT_MDD_Arena.boolean_index duplicate_arena) duplicate_roots
    val _ = if duplicate_mapping = [0,1,0] then ()
      else error "Ordered Boolean guard import lost duplicate-row mapping"
    val _ = reject "duplicate nodes in the canonical importer"
      (fn () => ignore (Comma_CRT_MDD_Arena.import_boolean_table
        (Comma_CRT_MDD_Arena.create [2]) duplicate_leaves 2))
  in lthy end\<close>

ML \<open>
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Indexed frozen-table certificate example; no source authority"
    @{thms comma_mdd_certificate_example_wellformed
      comma_mdd_certificate_example_shift
      comma_mdd_certificate_example_bind
      comma_mdd_certificate_example_bind_branch_alias
      comma_mdd_certificate_example_phase_leaf};
\<close>

text \<open>The frozen table crosses two publication-chunk boundaries, including
an unequal final chunk and a nested right segment. Leaf payloads and branch
children keep their original global row indices.\<close>

local_setup \<open>fn lthy =>
  let
    val arena = Comma_CRT_MDD_Arena.create [2,2]
    val leaves = Vector.tabulate (260, Comma_CRT_MDD_Arena.action_some arena)
    val inner = Comma_CRT_MDD_Arena.action_branch arena 1
      [Vector.sub (leaves,127),Vector.sub (leaves,128)]
    val later = Comma_CRT_MDD_Arena.action_branch arena 1
      [Vector.sub (leaves,255),Vector.sub (leaves,256)]
    val root = Comma_CRT_MDD_Arena.action_branch arena 0 [inner,later]
    val (store,lthy') = Comma_CRT_MDD_Certificate_Store.make "comma_mdd_chunk_boundary_nodes" arena lthy
    val ctxt = Comma_CRT_MDD_Certificate_Store.context store
    val _ = if Comma_CRT_MDD_Certificate_Store.node_count store = 263 then ()
      else error "MDD chunk fixture changed its global row domain"
    fun check_row (index,expected_node) =
      let
        val request = Const (@{const_name nth},
          @{typ "nat comma_crt_mdd_node list"} --> @{typ nat} -->
            @{typ "nat comma_crt_mdd_node"}) $
          Comma_CRT_MDD_Certificate_Store.table store $ HOLogic.mk_number @{typ nat} index
        val expected = Logic.mk_equals (request,Comma_CRT_MDD_Certificate_Store.node_term expected_node)
      in Comma_CRT_MDD_Proof_Utils.exact_prop ctxt
        "MDD chunk-boundary row" expected (Comma_CRT_MDD_Certificate_Store.lookup store index) end
    val rows = map check_row
      [(0,Comma_CRT_MDD_Certificate_Store.Leaf 1),
       (127,Comma_CRT_MDD_Certificate_Store.Leaf 128),
       (128,Comma_CRT_MDD_Certificate_Store.Leaf 129),
       (255,Comma_CRT_MDD_Certificate_Store.Leaf 256),
       (256,Comma_CRT_MDD_Certificate_Store.Leaf 257),
       (260,Comma_CRT_MDD_Certificate_Store.Branch (1,[127,128])),
       (261,Comma_CRT_MDD_Certificate_Store.Branch (1,[255,256])),
       (262,Comma_CRT_MDD_Certificate_Store.Branch (0,[260,261]))]
    val _ = if Comma_CRT_MDD_Certificate_Store.action_index store root = 262 then ()
      else error "MDD chunk publication changed the authenticated root"
    val _ = Comma_Proof_Dependency_Audit.require_native_clean ctxt
      "Balanced MDD table publication and cross-chunk child indices"
      (Comma_CRT_MDD_Certificate_Store.wellformed store :: rows)
  in snd (Local_Theory.note
    ((Binding.name "comma_mdd_chunk_boundary_wellformed",[]),
      [Comma_CRT_MDD_Certificate_Store.wellformed store]) lthy') end\<close>

text \<open>Nested selection preserves ragged row bounds even when the declared
maximum inner extent is larger than the selected row.\<close>

local_setup \<open>fn lthy =>
  let
    val ((local_table,(_,local_definition)),lthy') = Local_Theory.define
      ((Binding.name "comma_ragged_selector_fixture",NoSyn),
       ((Binding.name "comma_ragged_selector_fixture_def",[]),
        @{term "[[3,5],[7::nat]]"})) lthy
    val morphism = Local_Theory.target_morphism lthy'
    val table = Morphism.term morphism local_table
    val definition = Morphism.thm morphism local_definition
    val ctxt = Local_Theory.target_of lthy'
    val outer = Const (@{const_name nth},
      @{typ "nat list list"} --> @{typ nat} --> @{typ "nat list"})
    val inner = Const (@{const_name nth},
      @{typ "nat list"} --> @{typ nat} --> @{typ nat})
    fun table_request source row column = inner $ (outer $ source $ row) $ column
    val request = table_request table
    val aliases = Comma_Selected_List_Alias.make
      {ctxt=ctxt,root_definition=definition,
       validate_equation=Comma_Selected_List_Conversion.validate_equation}
    val named_request = Thm.cterm_of ctxt (request @{term "0::nat"} @{term "1::nat"})
    val named_lookup = #canonical_lookup aliases named_request
    val _ = if Thm.is_reflexive named_lookup then () else
      error "Named table lookup expanded its authenticated root"
    val selector = Comma_Selected_List_Conversion.make_nested
      {ctxt=ctxt,name="ragged_selector_fixture",root_definition=definition,
       table_pattern=request (Free ("row",@{typ nat}))
         (Free ("column",@{typ nat})),depth=2}
    val context = Comma_Entry_Arithmetic.natural_context ctxt
      |> Simplifier.add_proc (#procedure selector)
      |> Simplifier.add_proc (#post_procedure selector)
    fun numeral n = HOLogic.mk_number @{typ nat} n
    fun select row column = Simplifier.rewrite context
      (Thm.cterm_of ctxt (request (numeral row) (numeral column)))
    fun check (row,column,value) =
      Comma_CRT_MDD_Proof_Utils.exact_prop ctxt "Ragged selected row"
        (Logic.mk_equals
          (request (numeral row) (numeral column),numeral value))
        (select row column)
    val facts = map check [(0,0,3),(0,1,5),(1,0,7)]
    fun reject (row,column) =
      (case Exn.capture (fn () => select row column) () of
        Exn.Exn (ERROR _) => ()
      | Exn.Exn exn => Exn.reraise exn
      | Exn.Res _ => error "Nested selector admitted an out-of-row index")
    val _ = List.app reject [(1,1),(2,0),(0,2)]
    val _ = check (1,0,7)
    val literal = Thm.term_of (Thm.rhs_of definition)
    fun select_literal row column = Simplifier.rewrite context
      (Thm.cterm_of ctxt (table_request literal (numeral row) (numeral column)))
    val literal_fact = Comma_CRT_MDD_Proof_Utils.exact_prop ctxt
      "Authenticated literal alias selects the same row"
      (Logic.mk_equals (table_request literal (numeral 1) (numeral 0),numeral 7))
      (select_literal 1 0)
    val _ = (case Exn.capture (fn () => select_literal 1 1) () of
        Exn.Exn (ERROR _) => ()
      | Exn.Exn exn => Exn.reraise exn
      | Exn.Res _ => error "Literal alias admitted an out-of-row index")
    val _ = Comma_Proof_Dependency_Audit.require_native_clean ctxt
      "Ragged nested lookup and exact row bounds" (literal_fact::facts)
  in lthy' end\<close>


text \<open>Small negative fixtures for the checked action-output links.  They
exercise the exact source/full-shift payload and a direct postorder program
reference; no source oracle or admitted theorem is used.\<close>

ML \<open>
  val _ =
    let
      val require_distinct = Comma_Frontier24_Parametric_Runtime.require_distinct_terms
      fun reject label terms =
        (case Exn.capture (require_distinct label) terms of
          Exn.Exn (ERROR _) => ()
        | Exn.Exn exn => Exn.reraise exn
        | Exn.Res _ => error ("Canonical producer accepted duplicate " ^ label))
      val program = @{term "Comma_Near_Boundary_Program 1"}
      val exit = @{term "Comma_Continuation_Exit (Comma_Entry 1 0 12) 924"}
      val _ = reject "programs" [program,program]
      val _ = reject "actions" [exit,exit]
      val closure = @{term "(3::nat,924::nat)"}
      val _ = reject "closure keys" [closure,closure]
      val _ = require_distinct "full Exit shifts"
        [@{term "Comma_Continuation_Exit (Comma_Entry 1 0 12) 0"},exit]
      val _ = require_distinct "closure shifts"
        [@{term "(3::nat,0::nat)"},closure]
    in () end
\<close>

definition frontier24_fixture_exit_bundle ::
    "comma_frontier24_parametric_bundle" where
  "frontier24_fixture_exit_bundle =
    \<lparr>cf24_programs=[Comma_Near_Boundary_Program 1],
     cf24_selectors=[],
     cf24_action_tokens=[Comma_Continuation_Exit (Comma_Entry 1 0 0) 1],
     cf24_guard_entries=[], cf24_closures=[],
     cf24_class_program_refs=[], cf24_class_roots=[],
     cf24_radices=[2], cf24_nodes=[Comma_CRT_MDD_Leaf 1],
     cf24_zero_root=0\<rparr>"

definition frontier24_fixture_exit_closure ::
    "comma_frontier24_closure" where
  "frontier24_fixture_exit_closure =
    \<lparr>cf24_closure_program_ref=0, cf24_closure_full_shift=0,
     cf24_closure_cases=[], cf24_closure_near_token=None,
     cf24_closure_near_action_output_root=None,
     cf24_closure_near_child=None, cf24_closure_output_root=0\<rparr>"

lemma frontier24_fixture_exit_exact_full_shift_accepted:
  "comma_frontier24_action_output_linked
      frontier24_fixture_exit_bundle 0 frontier24_fixture_exit_closure
      0 0 None"
  unfolding frontier24_fixture_exit_bundle_def
      frontier24_fixture_exit_closure_def
      comma_frontier24_action_output_linked_def
      comma_parametric_exit_continue_code_def
  by code_simp

lemma frontier24_fixture_exit_wrong_full_shift_rejected:
  "\<not> comma_frontier24_action_output_linked
      frontier24_fixture_exit_bundle 0
      (frontier24_fixture_exit_closure\<lparr>cf24_closure_full_shift := 1\<rparr>)
      0 0 None"
  unfolding frontier24_fixture_exit_bundle_def
      frontier24_fixture_exit_closure_def
      comma_frontier24_action_output_linked_def
      comma_parametric_exit_continue_code_def
  by code_simp

definition frontier24_fixture_wrong_exit_leaf_bundle ::
    "comma_frontier24_parametric_bundle" where
  "frontier24_fixture_wrong_exit_leaf_bundle =
    frontier24_fixture_exit_bundle\<lparr>cf24_nodes := [Comma_CRT_MDD_Leaf 0]\<rparr>"

lemma frontier24_fixture_exit_wrong_leaf_payload_rejected:
  "\<not> comma_frontier24_action_output_linked
      frontier24_fixture_wrong_exit_leaf_bundle 0
      frontier24_fixture_exit_closure 0 0 None"
  unfolding frontier24_fixture_exit_bundle_def
      frontier24_fixture_wrong_exit_leaf_bundle_def
      frontier24_fixture_exit_closure_def
      comma_frontier24_action_output_linked_def
      comma_parametric_exit_continue_code_def
  by code_simp

definition frontier24_fixture_goto_bundle ::
    "comma_frontier24_parametric_bundle" where
  "frontier24_fixture_goto_bundle =
    \<lparr>cf24_programs=[Comma_Near_Boundary_Program 1,
                       Comma_Near_Boundary_Program 2],
     cf24_selectors=[],
     cf24_action_tokens=[Comma_Continuation_Goto (Comma_Near 2 0 1) 0],
     cf24_guard_entries=[],
     cf24_closures=[
       \<lparr>cf24_closure_program_ref=1, cf24_closure_full_shift=0,
        cf24_closure_cases=[], cf24_closure_near_token=None,
        cf24_closure_near_action_output_root=None,
        cf24_closure_near_child=None, cf24_closure_output_root=0\<rparr>,
       \<lparr>cf24_closure_program_ref=0, cf24_closure_full_shift=0,
        cf24_closure_cases=[], cf24_closure_near_token=None,
        cf24_closure_near_action_output_root=None,
        cf24_closure_near_child=None, cf24_closure_output_root=0\<rparr>],
     cf24_class_program_refs=[], cf24_class_roots=[],
     cf24_radices=[2], cf24_nodes=[Comma_CRT_MDD_Leaf 0],
     cf24_zero_root=0\<rparr>"

lemma frontier24_fixture_goto_exact_child_program_ref_accepted:
  "comma_frontier24_action_output_linked frontier24_fixture_goto_bundle
      1 (cf24_closures frontier24_fixture_goto_bundle ! 1) 0 0 (Some 0)"
  unfolding frontier24_fixture_goto_bundle_def
      comma_frontier24_action_output_linked_def
  by code_simp

definition frontier24_fixture_goto_wrong_program_ref_bundle ::
    "comma_frontier24_parametric_bundle" where
  "frontier24_fixture_goto_wrong_program_ref_bundle =
    frontier24_fixture_goto_bundle\<lparr>cf24_closures :=
      (cf24_closures frontier24_fixture_goto_bundle ! 0)\<lparr>
        cf24_closure_program_ref := 0\<rparr> #
      tl (cf24_closures frontier24_fixture_goto_bundle)\<rparr>"

lemma frontier24_fixture_goto_wrong_program_ref_rejected:
  "\<not> comma_frontier24_action_output_linked
      frontier24_fixture_goto_wrong_program_ref_bundle 1
      (cf24_closures frontier24_fixture_goto_wrong_program_ref_bundle ! 1)
      0 0 (Some 0)"
  unfolding frontier24_fixture_goto_bundle_def
      frontier24_fixture_goto_wrong_program_ref_bundle_def
      comma_frontier24_action_output_linked_def
  by code_simp

lemma frontier24_fixture_goto_out_of_bounds_child_rejected:
  "\<not> comma_frontier24_action_output_linked frontier24_fixture_goto_bundle
      1 (cf24_closures frontier24_fixture_goto_bundle ! 1) 0 0 (Some 2)"
  unfolding frontier24_fixture_goto_bundle_def
      comma_frontier24_action_output_linked_def
  by code_simp

lemma frontier24_fixture_goto_nonpostorder_child_rejected:
  "\<not> comma_frontier24_action_output_linked frontier24_fixture_goto_bundle
      1 (cf24_closures frontier24_fixture_goto_bundle ! 1) 0 0 (Some 1)"
  unfolding frontier24_fixture_goto_bundle_def
      comma_frontier24_action_output_linked_def
  by code_simp

ML \<open>
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Exact Exit and direct postorder Goto action-output links"
    @{thms frontier24_fixture_exit_exact_full_shift_accepted
      frontier24_fixture_exit_wrong_full_shift_rejected
      frontier24_fixture_exit_wrong_leaf_payload_rejected
      frontier24_fixture_goto_exact_child_program_ref_accepted
      frontier24_fixture_goto_wrong_program_ref_rejected
      frontier24_fixture_goto_out_of_bounds_child_rejected
      frontier24_fixture_goto_nonpostorder_child_rejected};
\<close>


end
