(* Focused regression fixtures for controlled column lookup and its bounded
   directory/block interval proof cache. *)
structure Comma_Semantic_B1_Column_Lookup_Regression =
struct
  structure Conversion = Comma_Semantic_B1_Column_Conversion

  fun require condition message = if condition then () else error message

  fun expect_error expected label operation =
    (case Exn.capture operation () of
      Exn.Exn (ERROR message) =>
        if message = expected then ()
        else error (label ^ " failed for the wrong reason: " ^ message)
    | Exn.Exn exn => Exn.reraise exn
    | Exn.Res _ => error (label ^ " was unexpectedly accepted"))

  fun clean_theorem theorem =
    Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem) andalso
    null (Thm.tpairs_of theorem) andalso
    null (Thm_Deps.all_oracles [theorem])

  fun check_controlled_lookup ctxt =
    let
      val natT = @{typ nat}
      val blockT = @{typ comma_semantic_b1_crt_column_block}
      val dagT = @{typ comma_semantic_b1_crt_column_dag}
      val payloadT = @{typ "nat \<times> nat list"}
      val resultT = @{typ "(nat \<times> nat list) option"}
      val empty_block = @{term Comma_B1_CRT_Column_Block_Empty}
      val block_node = Const (@{const_name Comma_B1_CRT_Column_Block_Node},
        natT --> natT --> HOLogic.listT natT --> blockT --> blockT --> blockT)
      fun nat n = HOLogic.mk_number natT n
      fun ids values = HOLogic.mk_list natT (map nat values)
      fun node cid level children left right = block_node $ nat cid $ nat level $
        ids children $ left $ right
      val left_rows = node 3 0 [1, 0, 1, 0]
        (node 2 0 [0, 1, 0, 1] empty_block empty_block) empty_block
      val right_rows = node 5 1 [1, 0, 1]
        (node 4 1 [0, 1, 0] empty_block empty_block) empty_block
      val block_constructor = Const (@{const_name Comma_B1_CRT_Column_DAG_Block},
        natT --> natT --> blockT --> dagT)
      val branch_constructor = Const (@{const_name Comma_B1_CRT_Column_DAG_Branch},
        natT --> dagT --> dagT --> dagT)
      fun block base extent rows = block_constructor $ nat base $ nat extent $ rows
      val left = block 2 2 left_rows
      val right = block 4 2 right_rows
      val directory = branch_constructor $ nat 4 $ left $ right
      val malformed_directory = branch_constructor $ nat 4 $ right $ left
      val lookup = Const (@{const_name comma_semantic_b1_crt_column_dag_lookup},
        dagT --> natT --> resultT)
      val lookup_rules = Conversion.normalize_lookup_rules ctxt
        @{thms comma_semantic_b1_crt_column_dag_lookup.simps
          comma_semantic_b1_crt_column_block_lookup.simps}
      val arithmetic = Comma_Entry_Arithmetic.natural_context ctxt
      val _ = expect_error "B1 lookup bound did not reduce to a closed truth"
        "false scalar interval bound" (fn () =>
          Comma_Semantic_B1_Column_Lookup_Cache.natural_bound ctxt arithmetic
            @{term "(2::nat)<1"})
      fun value level children =
        Const (@{const_name Some}, payloadT --> resultT) $
          HOLogic.mk_prod (nat level, ids children)
      fun run tree cid visits = Conversion.controlled_lookup ctxt arithmetic
          lookup_rules visits NONE
          (Thm.cterm_of ctxt (lookup $ tree $ nat cid))
      val visits = Unsynchronized.ref 0
      val below = run directory 2 visits
      val below_rhs = Thm.term_of (Thm.rhs_of below)
      val _ = require (below_rhs aconv value 0 [0, 1, 0, 1] andalso
          !visits = 4 andalso clean_theorem below)
        "B1 controlled lookup failed the selected-path/count fixture"
      val at_split_visits = Unsynchronized.ref 0
      val at_split = run directory 4 at_split_visits
      val _ = require (Thm.term_of (Thm.rhs_of at_split) aconv value 1 [0, 1, 0] andalso
          !at_split_visits = 4 andalso clean_theorem at_split)
        "B1 controlled lookup failed the right-branch fixture"
      val malformed_visits = Unsynchronized.ref 0
      val malformed = run malformed_directory 2 malformed_visits
      val _ = require (not (Thm.term_of (Thm.rhs_of malformed) aconv
          value 0 [0, 1, 0, 1]) andalso !malformed_visits <= 4 andalso
          clean_theorem malformed)
        "B1 controlled lookup accepted a reordered directory branch"
    in () end

  fun check_mixed_directory_shape ctxt =
    let
      val natT = @{typ nat}
      val blockT = @{typ comma_semantic_b1_crt_column_block}
      val dagT = @{typ comma_semantic_b1_crt_column_dag}
      fun nat n = HOLogic.mk_number natT n
      val empty = @{term Comma_B1_CRT_Column_Block_Empty}
      val node = Const (@{const_name Comma_B1_CRT_Column_Block_Node},
        natT --> natT --> HOLogic.listT natT --> blockT --> blockT --> blockT)
      val rows = node $ nat 3 $ nat 0 $ HOLogic.mk_list natT [nat 0, nat 1] $
        empty $ empty
      val block_constructor = Const (@{const_name Comma_B1_CRT_Column_DAG_Block},
        natT --> natT --> blockT --> dagT)
      val branch_constructor = Const (@{const_name Comma_B1_CRT_Column_DAG_Branch},
        natT --> dagT --> dagT --> dagT)
      fun leaf base = block_constructor $ nat base $ nat 1 $ rows
      val directory = branch_constructor $ nat 2 $ leaf 2 $ leaf 3
      val checked_directory = Thm.term_of (Thm.cterm_of ctxt directory)
      fun natural term = #2 (HOLogic.dest_number term)
      fun block_range term =
        (case Comma_Semantic_B1_Column_Catalog.directory_shape term of
          SOME (Comma_Semantic_B1_Column_Catalog.Directory_Block (base, extent, _)) =>
            SOME (natural base, natural extent)
        | _ => NONE)
      val decoded =
        (case Comma_Semantic_B1_Column_Catalog.directory_shape checked_directory of
          SOME (Comma_Semantic_B1_Column_Catalog.Directory_Branch (split, left, right)) =>
            SOME (natural split, block_range left, block_range right)
        | _ => NONE)
    in
      require (decoded = SOME (2, SOME (2, 1), SOME (3, 1)))
        "B1 directory decoder confused a branch with its same-arity block leaves"
    end

  fun check_directory_interval_cache ctxt definitions dag_definition =
    let
      val natT = @{typ nat}
      val dagT = @{typ comma_semantic_b1_crt_column_dag}
      val blockT = @{typ comma_semantic_b1_crt_column_block}
      val resultT = @{typ "(nat \<times> nat list) option"}
      val arithmetic = Comma_Entry_Arithmetic.natural_context ctxt
      fun nat n = HOLogic.mk_number natT n
      val dag_equation = Local_Defs.meta_rewrite_rule ctxt dag_definition
      val dag_constant = Thm.term_of (Thm.lhs_of dag_equation)
      val blocks = maps (fn theorem =>
        let
          val equation = Local_Defs.meta_rewrite_rule ctxt theorem
          val constant = Thm.term_of (Thm.lhs_of equation)
        in
          (case constant of
            Const (name, _) =>
              (case Comma_Semantic_B1_Column_Catalog.parse_block_index name of
                SOME index => [(index, equation, constant)]
              | NONE => [])
          | _ => [])
        end) definitions
      fun selected_block index =
        (case List.find (fn (actual, _, _) => actual = index) blocks of
          SOME (_, equation, constant) => (equation, constant)
        | NONE => error ("B1 directory cache fixture has no block " ^
            Int.toString index))
      val (block0_definition, block0_constant) = selected_block 0
      val (block1_definition, block1_constant) = selected_block 1
      val block0_extent = length (Comma_Semantic_B1_Column_Catalog.parse_block_tree
        2 (Thm.term_of (Thm.rhs_of block0_definition)))
      val _ = require (block0_extent = Comma_Semantic_B1_Column_Catalog.block_size)
        "B1 directory cache fixture needs a full first block"
      val cache = Comma_Semantic_B1_Column_Lookup_Cache.make_directory
        ctxt arithmetic 8192 dag_constant dag_equation
      val lookup = Const (@{const_name comma_semantic_b1_crt_column_dag_lookup},
        dagT --> natT --> resultT)
      val block_lookup = Const (@{const_name comma_semantic_b1_crt_column_block_lookup},
        blockT --> natT --> resultT)
      fun request cid = lookup $ dag_constant $ nat cid
      fun point cid = #lookup cache block0_constant block0_definition
        2 block0_extent cid (Thm.cterm_of ctxt (request cid))
      fun check_point cid theorem =
        require (Thm.term_of (Thm.lhs_of theorem) aconv request cid andalso
            Thm.term_of (Thm.rhs_of theorem) aconv
              (block_lookup $ block0_constant $ nat cid) andalso
            clean_theorem theorem)
          "B1 directory interval cache returned another point equation"
      val first = point 2
      val _ = check_point 2 first
      val {hits = first_hits, misses = first_misses, retained = first_retained,
        capacity_misses = first_capacity_misses, directory_nodes = first_nodes} =
          #stats cache ()
      val _ = require (first_hits = 0 andalso first_misses = 1 andalso
          first_retained = 1 andalso first_capacity_misses = 0 andalso first_nodes > 0)
        "B1 directory interval cache did not publish its first block proof"
      val second = point 3
      val _ = check_point 3 second
      val {hits = second_hits, misses = second_misses, retained = second_retained,
        capacity_misses = second_capacity_misses, directory_nodes = second_nodes} =
          #stats cache ()
      val _ = require (second_hits = 1 andalso second_misses = first_misses andalso
          second_retained = first_retained andalso
          second_capacity_misses = first_capacity_misses andalso
          second_nodes = first_nodes)
        "B1 directory interval cache rebuilt a proof for a repeated block"
      val foreign_root = Const ("Regression.foreign_column_dag", dagT)
      val _ = expect_error "B1 directory cache received another DAG definition"
        "foreign DAG directory cache authority" (fn () =>
          Comma_Semantic_B1_Column_Lookup_Cache.make_directory
            ctxt arithmetic 8192 foreign_root dag_equation)
      val _ = expect_error "B1 directory leaf differs from selected block authority"
        "changed directory block authority" (fn () =>
          #lookup cache block1_constant block1_definition 2 block0_extent 2
            (Thm.cterm_of ctxt (request 2)))
      val _ = expect_error "B1 directory leaf differs from selected block authority"
        "changed directory block interval" (fn () =>
          #lookup cache block0_constant block0_definition 3 (block0_extent - 1) 3
            (Thm.cterm_of ctxt (request 3)))
      val {hits = final_hits, misses = final_misses, retained = final_retained,
        capacity_misses = _, directory_nodes = _} = #stats cache ()
      val _ = require (final_hits = 1 andalso final_misses = 3 andalso
          final_retained = 1)
        "B1 directory cache retained a failed authority or interval request"
    in () end

end
