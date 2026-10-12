(* Publish the online CRT templates and occurrence descriptors as HOL data.
   Candidate construction is untrusted; the importing theory certifies the
   published values with the structural CRT checker. *)
structure Comma_Semantic_B1_Occurrence_Publication =
struct

  structure Candidate = Comma_Semantic_B1_Template_Constructor

  type mass_annotation =
    {constant: term, body: term, definition: thm, cids: int list, roots: int list}

  structure Mass_Annotation_Data = Theory_Data
  (
    type T = mass_annotation option
    val empty = NONE
    fun same (left: mass_annotation) (right: mass_annotation) =
      #constant left aconv #constant right andalso
      #body left aconv #body right andalso
      #cids left = #cids right andalso #roots left = #roots right andalso
      Thm.prop_of (#definition left) aconv Thm.prop_of (#definition right)
    fun merge (NONE, right) = right
      | merge (left, NONE) = left
      | merge (SOME left, SOME right) =
          if same left right then SOME left
          else error "B1 mass annotation theory data diverged"
  )

  fun get_mass_annotation ctxt =
    (case Mass_Annotation_Data.get (Proof_Context.theory_of ctxt) of
      SOME annotation => annotation
    | NONE => error "B1 mass annotation was not published in this theory")

  fun get_demanded_root_cids ctxt = #roots (get_mass_annotation ctxt)

  (* Keep executable constructor fixtures with the publication boundary; the
     candidate fold itself contains only production construction logic. *)
  fun check_candidate_examples () =
    let
      val even_one = Candidate.MDD_Node (0, [Candidate.MDD_False,
        Candidate.MDD_True, Candidate.MDD_False, Candidate.MDD_False])
      val slot_two = Candidate.scope_column_key [(4, 2)]
      val shifted = Candidate.lift_template_slot 4 2 3 [even_one]
      val _ = if length shifted = 1 andalso
          Candidate.mdd_eval_phase (hd shifted) 2 andalso
          not (Candidate.mdd_eval_phase (hd shifted) 1) then ()
        else error "B1 occurrence lift has the wrong positive net-shift sign"
      val _ = if slot_two = hd shifted then ()
        else error "B1 slot lift did not intersect the shifted child geometry"
      val phase_one = Candidate.MDD_Node (0, [Candidate.MDD_False,
        Candidate.MDD_True, Candidate.MDD_False, Candidate.MDD_False])
      val phase_two = Candidate.MDD_Node (0, [Candidate.MDD_False,
        Candidate.MDD_False, Candidate.MDD_True, Candidate.MDD_False])
      val geometry = sort Candidate.compare_mdd [phase_one, phase_two]
      val first_binding = Candidate.binding_outputs geometry [phase_one, phase_two]
        [Candidate.Live 7, Candidate.Stop 3]
      val swapped_binding = Candidate.binding_outputs geometry [phase_two, phase_one]
        [Candidate.Live 7, Candidate.Stop 3]
      val (full, full_cardinalities) = Candidate.check_mdd_partition
        Candidate.mdd_cardinality [(Candidate.Live 0, Candidate.MDD_True)]
      val half = Candidate.MDD_Node (0, [Candidate.MDD_True, Candidate.MDD_True,
        Candidate.MDD_False, Candidate.MDD_False])
      val other_half = Candidate.MDD_Node (0, [Candidate.MDD_False,
        Candidate.MDD_False, Candidate.MDD_True, Candidate.MDD_True])
      val (complementary, complementary_cardinalities) =
        Candidate.check_mdd_partition Candidate.mdd_cardinality
        [(Candidate.Live 0, half), (Candidate.Stop 1, other_half)]
      fun rejected expected columns =
        (case Exn.capture (fn () => Candidate.check_mdd_partition
            Candidate.mdd_cardinality columns) () of
          Exn.Exn (ERROR message) => message = expected
        | Exn.Exn exn => Exn.reraise exn
        | Exn.Res _ => false)
      val overlap = rejected "B1 symbolic source columns overlap"
        [(Candidate.Live 0, half), (Candidate.Stop 1, half)]
      val missing = rejected "B1 symbolic source table does not cover the clock"
        [(Candidate.Stop 0, Candidate.MDD_False)]
      val _ = if first_binding = [Candidate.Stop 3, Candidate.Live 7] andalso
          swapped_binding = [Candidate.Live 7, Candidate.Stop 3] andalso
          first_binding <> swapped_binding andalso full = [Candidate.MDD_True] andalso
          full_cardinalities = [(Candidate.MDD_True, Candidate.clock_size)] andalso
          complementary = [half, other_half] andalso
          complementary_cardinalities =
            [(half, Candidate.clock_size div 2),
             (other_half, Candidate.clock_size div 2)] andalso overlap andalso missing then ()
        else error "B1 compact geometry/binding or partition regression failed"
    in () end

  type column_dag =
    {node_keys: Candidate.mdd list, cid: Candidate.mdd -> int}

  fun make_column_dag_with_sources sources =
    let
      val started = Time.now ()
      val root_count = fold (fn (_, roots) => fn count => count + length roots)
        sources 0
      val next_cid = Unsynchronized.ref 2
      val unique_by_source = Unsynchronized.ref Symtab.empty
      fun add_unique source =
        unique_by_source := Symtab.map_default (source, 0) (fn count => count + 1)
          (!unique_by_source)
      val source_counts = map (fn (source, roots) =>
        source ^ "_roots=" ^ Int.toString (length roots)) sources
      val _ = Comma_Proof_Profile.report
        ("B1 publication stage=column-dag-root-collection-start roots=" ^
          Int.toString root_count ^ " " ^ String.concatWith " " source_counts)
      fun collect source key (known, reverse_nodes) =
        (case key of
          Candidate.MDD_False => (known, reverse_nodes)
        | Candidate.MDD_True => (known, reverse_nodes)
        | Candidate.MDD_Node (_, children) =>
            if Candidate.MDDtab.defined known key then (known, reverse_nodes)
            else
              let
                val (with_children, child_order) =
                  fold (collect source) children (known, reverse_nodes)
                val cid = !next_cid
                val _ = next_cid := cid + 1
                val _ = add_unique source
                val with_key = Candidate.MDDtab.update (key, cid) with_children
              in (with_key, key :: child_order) end)
      val (node_indexes, reverse_nodes) =
        fold (fn (source, roots) => fn state =>
          fold (collect source) roots state) sources (Candidate.MDDtab.empty, [])
      val node_keys = rev reverse_nodes
      val _ = if !next_cid = length node_keys + 2 then ()
        else error "B1 global column DAG assigned a noncontiguous CID range"
      val unique_counts = Symtab.dest (!unique_by_source)
        |> map (fn (source, count) => source ^ "_unique=" ^ Int.toString count)
      val _ = Comma_Proof_Profile.report
        ("B1 publication stage=column-dag-root-collection-complete roots=" ^
          Int.toString root_count ^ " unique_nodes=" ^ Int.toString (length node_keys) ^
          " " ^ String.concatWith " " unique_counts ^ " elapsed_ms=" ^
          Comma_Proof_Profile.elapsed_ms started)
      fun cid Candidate.MDD_False = 0
        | cid Candidate.MDD_True = 1
        | cid key =
            (case Candidate.MDDtab.lookup node_indexes key of
              SOME index => index
            | NONE => error "B1 global column DAG omitted an MDD root")
    in {node_keys = node_keys, cid = cid}: column_dag end

  fun make_column_dag roots = make_column_dag_with_sources [("all", roots)]

  fun construction_piece_key (Candidate.Terminal_Piece (_, _, _, key)) = key
    | construction_piece_key (Candidate.Goto_Piece (_, _, _, _, _, _, key)) = key

  fun artifact_column_dag (artifact: Candidate.artifact) =
    let
      val template_roots = maps I (#template_keys artifact)
      val lift_roots = maps I (#lift_column_keys artifact)
      val piece_roots = maps (maps (map construction_piece_key))
        (#construction_piece_refs artifact)
      val _ = Comma_Proof_Profile.report
        ("B1 publication stage=column-dag-root-sources templates=" ^
          Int.toString (length template_roots) ^ " lifts=" ^
          Int.toString (length lift_roots) ^ " pieces=" ^
          Int.toString (length piece_roots) ^ " total=" ^
          Int.toString (length template_roots + length lift_roots +
            length piece_roots))
    in make_column_dag_with_sources
      [("templates", template_roots), ("lifts", lift_roots),
       ("pieces", piece_roots)] end

  fun serialize_column_ids (dag: column_dag) rows =
    HOLogic.mk_list (HOLogic.listT Candidate.natT)
      (map (fn row => HOLogic.mk_list Candidate.natT
        (map (Candidate.nat o #cid dag) row)) rows)

  (* A small candidate fixture makes the sharing contract explicit: two
     shallow parents point to the same named child CID, while swapping child
     order produces a distinct parent CID.  The proof layer sees these IDs,
     never the recursive MDD keys used to construct this example. *)
  fun check_shared_column_dag_example () =
    let
      val shared = Candidate.MDD_Node (3,
        map (fn digit => if digit = 0 then Candidate.MDD_True
          else Candidate.MDD_False) (0 upto 10))
      val false_key = Candidate.MDD_False
      val parent = Candidate.MDD_Node (2, shared :: replicate 6 false_key)
      val sibling = Candidate.MDD_Node (2,
        false_key :: false_key :: shared :: replicate 4 false_key)
      val swapped = Candidate.MDD_Node (2,
        false_key :: shared :: replicate 5 false_key)
      val dag = make_column_dag [parent, sibling, swapped]
      fun shared_child key =
        (case key of Candidate.MDD_Node (_, children) =>
          exists (fn child => #cid dag child = #cid dag shared) children
        | _ => false)
      val encoded = serialize_column_ids dag [[parent, sibling, swapped]]
      val encoded_rows = HOLogic.dest_list encoded
      val encoded_ids = (case encoded_rows of
          [row] => map (fn term => #2 (HOLogic.dest_number term))
            (HOLogic.dest_list row)
        | _ => error "B1 shared-column fixture did not serialize one row")
      val shared_cid = #cid dag shared
    in
      if shared_child parent andalso shared_child sibling andalso
          #cid dag parent <> #cid dag swapped andalso
          #cid dag parent <> shared_cid andalso #cid dag sibling <> shared_cid andalso
          encoded_ids = [#cid dag parent, #cid dag sibling, #cid dag swapped] andalso
          length (distinct (op =) encoded_ids) = length encoded_ids then ()
      else error "B1 global column DAG lost sharing or accepted swapped children"
    end

  fun serialize_construction_piece (dag: column_dag) piece =
    let
      val natT = Candidate.natT
      val refT = @{typ comma_semantic_b1_crt_piece_ref}
      fun make name arity arguments =
        let
          val argument_types = replicate arity natT
          val constructor = Const (name,
            fold_rev (fn argumentT => fn resultT => argumentT --> resultT)
              argument_types refT)
        in fold (fn argument => fn term => term $ Candidate.nat argument)
            arguments constructor end
    in
      (case piece of
        Candidate.Terminal_Piece (period, slot, parent_column, key) =>
          make @{const_name Comma_B1_Piece_Terminal} 4
            [period, slot, #cid dag key, parent_column]
      | Candidate.Goto_Piece
          (period, slot, child_source, child_column, lift_cid,
           parent_column, key) =>
          make @{const_name Comma_B1_Piece_Goto} 7
            [period, slot, child_source, child_column, lift_cid,
             #cid dag key, parent_column])
    end

  type global_definition =
    {name: string, T: typ, rhs: term Symtab.table -> term}
  type defined_global = {name: string, constant: term, theorem: thm}

  fun lookup_global_constant owner constants name =
    (case Symtab.lookup constants name of
      SOME constant => constant
    | NONE => error ("B1 " ^ owner ^ " omitted declared constant " ^ name))

  val construction_piece_source_block_size = 32
  val construction_piece_source_block_prefix =
    "comma_semantic_b1_crt_construction_piece_source_block_"
  val construction_piece_source_blocks_name =
    "comma_semantic_b1_crt_construction_piece_source_blocks"

  fun construction_piece_source_block_name index =
    construction_piece_source_block_prefix ^ Int.toString index

  fun serialize_construction_piece_source (dag: column_dag) rows =
    let
      val pieceT = @{typ comma_semantic_b1_crt_piece_ref}
      val rowT = HOLogic.listT pieceT
    in
      HOLogic.mk_list rowT
        (map (fn pieces => HOLogic.mk_list pieceT
          (map (serialize_construction_piece dag) pieces)) rows)
    end

  fun split_source_blocks values = chop_groups construction_piece_source_block_size values

  fun serialize_construction_piece_source_blocks
      (dag: column_dag) occurrences : global_definition list =
    let
      val pieceT = @{typ comma_semantic_b1_crt_piece_ref}
      val sourceT = HOLogic.listT (HOLogic.listT pieceT)
      val blockT = HOLogic.listT sourceT
    in
      map_index (fn (index, sources) =>
          {name = construction_piece_source_block_name index, T = blockT,
           rhs = (fn _ => HOLogic.mk_list sourceT
             (map (serialize_construction_piece_source dag) sources))}:
             global_definition) (split_source_blocks occurrences)
    end

  fun construction_piece_source_blocks_definition occurrences : global_definition =
    let
      val pieceT = @{typ comma_semantic_b1_crt_piece_ref}
      val sourceT = HOLogic.listT (HOLogic.listT pieceT)
      val blockT = HOLogic.listT sourceT
      val directoryT = HOLogic.listT blockT
      val names = map_index (fn (index, _) =>
        construction_piece_source_block_name index) (split_source_blocks occurrences)
    in
      {name = construction_piece_source_blocks_name, T = directoryT,
       rhs = (fn constants => HOLogic.mk_list blockT
         (map (lookup_global_constant "piece-source block batch" constants) names))}:
           global_definition
    end

  fun construction_piece_refs_definition occurrences : global_definition =
    let
      val pieceT = @{typ comma_semantic_b1_crt_piece_ref}
      val sourceT = HOLogic.listT (HOLogic.listT pieceT)
      val rootT = HOLogic.listT sourceT
      val blockT = HOLogic.listT sourceT
      val directoryT = HOLogic.listT blockT
      val concatenate = Const (@{const_name concat}, directoryT --> rootT)
    in
      {name = "comma_semantic_b1_crt_construction_piece_refs", T = rootT,
       rhs = (fn constants => concatenate $
         lookup_global_constant "piece-source directory" constants
           construction_piece_source_blocks_name)}:
           global_definition
    end

  val lift_column_id_block_size = 64
  val lift_column_id_block_prefix = "comma_semantic_b1_crt_lift_column_id_block_"
  val lift_column_id_blocks_name = "comma_semantic_b1_crt_lift_column_id_blocks"

  val column_block_size = 512

  fun column_rows (dag: column_dag) =
    let
      fun row (index, key) =
        (case key of
          Candidate.MDD_Node (level, children) =>
            (index + 2, level, map (#cid dag) children)
        | _ => error "B1 global column node table contains a Boolean leaf")
    in map_index row (#node_keys dag) end

  val mass_annotation_name = "comma_semantic_b1_crt_mass_annotation_tree"

  fun chunks size values =
    if null values then []
    else let val block = take size values
         in block :: chunks size (drop size values) end

  fun lift_column_id_block_name index =
    lift_column_id_block_prefix ^ Int.toString index

  fun serialize_lift_column_id_block_definitions (dag: column_dag) rows :
      global_definition list =
    let
      val rowT = HOLogic.listT Candidate.natT
      val blockT = HOLogic.listT rowT
      val blocks = chunks lift_column_id_block_size rows
    in
      map_index (fn (index, block_rows) =>
        {name = lift_column_id_block_name index, T = blockT,
         rhs = (fn _ => serialize_column_ids dag block_rows)}:
           global_definition) blocks
    end

  fun lift_column_id_blocks_definition block_count : global_definition =
    let
      val rowT = HOLogic.listT Candidate.natT
      val blockT = HOLogic.listT rowT
      val blocksT = HOLogic.listT blockT
      val names = map lift_column_id_block_name (0 upto (block_count - 1))
    in
      {name = lift_column_id_blocks_name, T = blocksT,
       rhs = (fn constants => HOLogic.mk_list blockT
         (map (lookup_global_constant "lift-column-id block batch" constants) names))}:
           global_definition
    end

  val lift_column_ids_definition : global_definition =
    let
      val rowT = HOLogic.listT Candidate.natT
      val blockT = HOLogic.listT rowT
      val blocksT = HOLogic.listT blockT
      val rootT = HOLogic.listT rowT
      val concatenate = Const (@{const_name concat}, blocksT --> rootT)
    in
      {name = "comma_semantic_b1_crt_lift_column_ids", T = rootT,
       rhs = (fn constants => concatenate $
         lookup_global_constant "lift-column root" constants
           lift_column_id_blocks_name)}: global_definition
    end

  fun define_global_definitions stage (definitions: global_definition list) lthy =
    let
      val started = Time.now ()
      val names = map #name definitions
      val _ = if length (distinct (op =) names) = length names then ()
        else error "B1 publication batch contains duplicate definition names"
      fun closed term = not (Term.is_open term) andalso
        null (Term.add_frees term []) andalso null (Term.add_vars term [])
      fun declare ({name, T, ...}: global_definition) (constants, thy) =
        let
          val (constant, next) = Sign.declare_const_global
            ((Binding.name name, T), NoSyn) thy
        in (Symtab.update (name, constant) constants, next) end
      fun define constants ({name, T, rhs}: global_definition) (reverse, thy) =
        let
          val item_started = Time.now ()
          val constant = lookup_global_constant "publication batch" constants name
          val body = rhs constants
          val _ = if fastype_of constant = T then ()
            else error ("B1 publication batch declared the wrong type for " ^ name)
          val _ = if fastype_of body = T then ()
            else error ("B1 publication batch body has the wrong type for " ^ name)
          val _ = if closed constant andalso closed body then ()
            else error ("B1 publication batch has an open body for " ^ name)
          val (theorem, next) = Global_Theory.add_def
            ((Binding.name (name ^ "_def"), Logic.mk_equals (constant, body))) thy
          val _ = Comma_Proof_Profile.report
            ("B1 publication stage=" ^ stage ^ "-item-complete name=" ^ name ^
              " elapsed_ms=" ^ Comma_Proof_Profile.elapsed_ms item_started)
          val result: defined_global = {name = name, constant = constant,
            theorem = theorem}
        in (result :: reverse, next) end
      val _ = Comma_Proof_Profile.report
        ("B1 publication stage=" ^ stage ^ "-start definitions=" ^
          Int.toString (length definitions))
      val (reverse_results, next_lthy) = Local_Theory.background_theory_result
        (fn thy =>
          let
            val (constants, thy') = fold declare definitions (Symtab.empty, thy)
            val (reverse, thy'') = fold (define constants) definitions ([], thy')
          in (reverse, thy'') end) lthy
      val results = rev reverse_results
      val _ = Comma_Proof_Profile.report
        ("B1 publication stage=" ^ stage ^ "-complete definitions=" ^
          Int.toString (length results) ^ " elapsed_ms=" ^
          Comma_Proof_Profile.elapsed_ms started)
    in (results, next_lthy) end

  fun serialize_column_block rows =
    let
      val natT = Candidate.natT
      val child_idsT = HOLogic.listT natT
      val blockT = @{typ comma_semantic_b1_crt_column_block}
      val empty = @{term Comma_B1_CRT_Column_Block_Empty}
      val constructor = Const (@{const_name Comma_B1_CRT_Column_Block_Node},
        natT --> natT --> child_idsT --> blockT --> blockT --> blockT)
      val row_vector = Vector.fromList rows
      val row_count = Vector.length row_vector
      fun build lower upper =
        if lower >= upper then empty
        else
          let
            val middle = lower + (upper - lower) div 2
            val (cid, level, children) = Vector.sub (row_vector, middle)
            val arguments =
              [Candidate.nat cid, Candidate.nat level,
               HOLogic.mk_list natT (map Candidate.nat children),
               build lower middle, build (middle + 1) upper]
          in fold (fn argument => fn term => term $ argument)
            arguments constructor end
    in build 0 row_count end

  fun define_column_blocks (dag: column_dag) node_rows lthy =
    let
      val started = Time.now ()
      val row_blocks = chunks column_block_size node_rows
      val preparation_started = Time.now ()
      val _ = Comma_Proof_Profile.report
        ("B1 publication stage=column-block-batch-preparation-start nodes=" ^
          Int.toString (length node_rows) ^ " blocks=" ^
          Int.toString (length row_blocks) ^ " max_rows=" ^
          Int.toString column_block_size)
      val prepared = map_index (fn (index, rows) =>
        let
          val base = 2 + index * column_block_size
          val tree = serialize_column_block rows
          val name = "comma_semantic_b1_crt_column_block_" ^ Int.toString index
        in (index, base, rows, name, tree) end) row_blocks
      val _ = Comma_Proof_Profile.report
        ("B1 publication stage=column-block-batch-preparation-complete blocks=" ^
          Int.toString (length prepared) ^ " elapsed_ms=" ^
          Comma_Proof_Profile.elapsed_ms preparation_started)
      val blockT = @{typ comma_semantic_b1_crt_column_block}
      val block_declarations = map (fn (_, _, _, name, tree) =>
        {name = name, T = blockT, rhs = (fn _ => tree)}: global_definition) prepared
      val (block_results, blocks_lthy) = define_global_definitions
        "column-block-batch-definitions" block_declarations lthy
      val blocks = map_index (fn (position, (index, base, rows, name, _)) =>
        let
          val result = nth block_results position
          val _ = if #name result = name then ()
            else error "B1 publication batch changed canonical block order"
        in {index = index, base = base, extent = length rows,
          constant = #constant result, theorem = #theorem result} end) prepared
      val block_vector = Vector.fromList blocks
      val block_count = Vector.length block_vector
      val dagT = @{typ comma_semantic_b1_crt_column_dag}
      val blockT = @{typ comma_semantic_b1_crt_column_block}
      val empty = @{term Comma_B1_CRT_Column_DAG_Empty}
      val block_constructor = Const
        (@{const_name Comma_B1_CRT_Column_DAG_Block},
         Candidate.natT --> Candidate.natT --> blockT --> dagT)
      val branch_constructor = Const
        (@{const_name Comma_B1_CRT_Column_DAG_Branch},
         Candidate.natT --> dagT --> dagT --> dagT)
      fun build lower upper =
        if lower >= upper then empty
        else if upper - lower = 1 then
          let val {base, extent, constant, ...} = Vector.sub (block_vector, lower)
          in fold (fn argument => fn term => term $ argument)
            [Candidate.nat base, Candidate.nat extent, constant] block_constructor end
        else
          let
            val middle = lower + (upper - lower) div 2
            val {base = split, ...} = Vector.sub (block_vector, middle)
          in fold (fn argument => fn term => term $ argument)
            [Candidate.nat split, build lower middle, build middle upper]
            branch_constructor end
      val directory = build 0 block_count
      val _ = Comma_Proof_Profile.report
        ("B1 publication stage=column-block-serialization-complete nodes=" ^
          Int.toString (length node_rows) ^ " blocks=" ^
          Int.toString block_count ^ " elapsed_ms=" ^
          Comma_Proof_Profile.elapsed_ms started)
    in {blocks = blocks, directory = directory, lthy = blocks_lthy} end

  fun column_value dag_constant cid =
    let
      val dagT = @{typ comma_semantic_b1_crt_column_dag}
      val makeT = dagT --> Candidate.natT --> Candidate.columnT
      val make = Const (@{const_name comma_semantic_b1_crt_column_at}, makeT)
    in make $ dag_constant $ Candidate.nat cid end

  fun define_column_data (dag: column_dag) node_rows lthy =
    let
      val started = Time.now ()
      val dagT = @{typ comma_semantic_b1_crt_column_dag}
      val node_count = length (#node_keys dag)
      val column_count = node_count + 2
      val _ = Comma_Proof_Profile.report
        ("B1 publication stage=column-block-definition-preparation-start nodes=" ^
          Int.toString node_count)
      val {blocks, directory, lthy = blocks_lthy} =
        define_column_blocks dag node_rows lthy
      val dag_started = Time.now ()
      val _ = Comma_Proof_Profile.report
        ("B1 publication stage=column-directory-definition-start blocks=" ^
          Int.toString (length blocks))
      val ((_, (_, dag_definition)), dag_lthy) = Local_Theory.define
        ((Binding.name "comma_semantic_b1_crt_column_node_dag", NoSyn),
         ((Binding.name "comma_semantic_b1_crt_column_node_dag_def", []), directory))
        blocks_lthy
      val dag_context = Local_Theory.target_of dag_lthy
      val dag_constant = Const
        (Sign.intern_const (Proof_Context.theory_of dag_context)
          "comma_semantic_b1_crt_column_node_dag", dagT)
      val _ = Comma_Proof_Profile.report
        ("B1 publication stage=column-directory-definition-complete blocks=" ^
          Int.toString (length blocks) ^ " elapsed_ms=" ^
          Comma_Proof_Profile.elapsed_ms dag_started)
      val _ = Comma_Proof_Profile.report
        ("B1 publication stage=column-block-theorem-bundle-skipped blocks=" ^
          Int.toString (length blocks))
      val count_started = Time.now ()
      val _ = Comma_Proof_Profile.report
        "B1 publication stage=compact-count-definition-start"
      val ((count_constant, (_, count_definition)), count_lthy) =
        Local_Theory.define
          ((Binding.name "comma_semantic_b1_crt_column_count", NoSyn),
           ((Binding.name "comma_semantic_b1_crt_column_count_def", []),
            Candidate.nat column_count)) dag_lthy
      val _ = Comma_Proof_Profile.report
        ("B1 publication stage=compact-count-definition-complete elapsed_ms=" ^
          Comma_Proof_Profile.elapsed_ms count_started)
      val columns_forT = @{typ comma_semantic_b1_crt_column_dag} -->
        Candidate.natT --> HOLogic.listT Candidate.columnT
      val columns_for = Const
        (@{const_name comma_semantic_b1_crt_columns_for}, columns_forT)
      val columns_body = columns_for $ dag_constant $ count_constant
      val columns_started = Time.now ()
      val _ = Comma_Proof_Profile.report
        ("B1 publication stage=compact-columns-definition-start count=" ^
          Int.toString column_count)
      val ((columns_constant, (_, columns_definition)), columns_lthy) =
        Local_Theory.define
          ((Binding.name "comma_semantic_b1_crt_columns", NoSyn),
           ((Binding.name "comma_semantic_b1_crt_columns_def", []), columns_body))
          count_lthy
      val _ = Comma_Proof_Profile.report
        ("B1 publication stage=compact-columns-definition-complete count=" ^
          Int.toString column_count ^ " elapsed_ms=" ^
          Comma_Proof_Profile.elapsed_ms columns_started)
      val columns_note_started = Time.now ()
      val _ = Comma_Proof_Profile.report
        "B1 publication stage=compact-columns-theorem-note-start"
      val (_, final_lthy) = Local_Theory.note
        ((Binding.name "comma_semantic_b1_crt_compact_definitions", []),
         [count_definition, columns_definition]) columns_lthy
      val _ = Comma_Proof_Profile.report
        ("B1 publication stage=compact-columns-theorem-note-complete elapsed_ms=" ^
          Comma_Proof_Profile.elapsed_ms columns_note_started)
      val _ = Comma_Proof_Profile.report
        ("B1 publication stage=column-block-definition-preparation-complete nodes=" ^
          Int.toString node_count ^ " blocks=" ^ Int.toString (length blocks) ^
          " elapsed_ms=" ^ Comma_Proof_Profile.elapsed_ms started)
    in
      {dag_constant = dag_constant, column_count = count_constant,
       columns = columns_constant, lthy = final_lthy}
    end

  fun get_definitions ctxt =
    let
      val thy = Proof_Context.theory_of ctxt
      val dag_definition = Proof_Context.get_thm ctxt
        "comma_semantic_b1_crt_column_node_dag_def"
      val equation = Local_Defs.meta_rewrite_rule ctxt dag_definition
      val left = Thm.term_of (Thm.lhs_of equation)
      val directory = Thm.term_of (Thm.rhs_of equation)
      val dag_name = Sign.intern_const thy "comma_semantic_b1_crt_column_node_dag"
      val block_size = Comma_Semantic_B1_Column_Catalog.block_size
      val _ = if (case left of Const (name, _) => name = dag_name | _ => false) andalso
          fastype_of left = Comma_Semantic_B1_Column_Catalog.dagT andalso
          fastype_of directory = Comma_Semantic_B1_Column_Catalog.dagT andalso
          Comma_Semantic_B1_Column_Conversion.closed left andalso
          Comma_Semantic_B1_Column_Conversion.closed directory andalso
          Thm.nprems_of equation = 0 andalso null (Thm.hyps_of equation) andalso
          null (Thm.tpairs_of equation) andalso null (Thm_Deps.all_oracles [equation])
        then () else error "B1 column DAG definition catalogue has invalid authority"
      fun parse value =
        (case Comma_Semantic_B1_Column_Catalog.directory_shape value of
          SOME Comma_Semantic_B1_Column_Catalog.Directory_Empty => ([], 0)
        | SOME (Comma_Semantic_B1_Column_Catalog.Directory_Block
            (base_term, extent_term, block_term)) =>
              let
                val base = Comma_Semantic_B1_Column_Catalog.dest_nat base_term
                val extent = Comma_Semantic_B1_Column_Catalog.dest_nat extent_term
                val (block_constant, block_long_name) =
                  (case block_term of Const (n, _) => (block_term, n)
                  | _ => error "B1 column DAG leaf does not name a block")
                val index = (case Comma_Semantic_B1_Column_Catalog.parse_block_index
                    block_long_name of
                    SOME i => i | NONE => error "B1 column DAG leaf has a foreign block")
                val _ = if Comma_Semantic_B1_Column_Catalog.canonical_block_name
                    thy index block_long_name andalso
                    fastype_of block_constant = @{typ comma_semantic_b1_crt_column_block} andalso
                    base = 2 + index * block_size andalso
                    extent > 0 andalso extent <= block_size then ()
                  else error "B1 column DAG leaf has a noncanonical block range"
              in ([index], 1) end
        | SOME (Comma_Semantic_B1_Column_Catalog.Directory_Branch
            (split_term, left_term, right_term)) =>
              let
                val split = Comma_Semantic_B1_Column_Catalog.dest_nat split_term
                val (left_indices, left_height) = parse left_term
                val (right_indices, right_height) = parse right_term
                val _ = if not (null left_indices) andalso not (null right_indices) andalso
                    split = 2 + hd right_indices * block_size andalso
                    List.last left_indices < hd right_indices andalso
                    Int.abs (left_height - right_height) <= 1 then ()
                  else error "B1 column DAG directory has a noncanonical branch"
              in (left_indices @ right_indices,
                  1 + Int.max (left_height, right_height)) end
        | NONE => error "B1 column DAG definition catalogue is malformed")
      val (indices, _) = parse directory
      val expected = 0 upto (length indices - 1)
      val _ = if not (null indices) andalso indices = expected then ()
        else error "B1 column DAG definition catalogue omits or reorders blocks"
      val block_definitions = map (fn index => Proof_Context.get_thm ctxt
        (Comma_Semantic_B1_Column_Catalog.block_prefix ^ Int.toString index ^ "_def"))
        indices
    in dag_definition :: block_definitions end

  type lift_column_id_block_catalogue =
    {root_definition: thm, directory_definition: thm,
     child_definitions: thm list, child_row_extents: int list,
     row_count: int}

  fun get_lift_column_id_block_definitions ctxt =
    let
      val thy = Proof_Context.theory_of ctxt
      val natT = Candidate.natT
      val rowT = HOLogic.listT natT
      val rootT = HOLogic.listT rowT
      val blockT = HOLogic.listT rowT
      val blocksT = HOLogic.listT blockT
      val descriptorT = @{typ comma_semantic_b1_crt_lift_descriptor}
      fun exact_equation name expectedT theorem =
        let
          val equation = Local_Defs.meta_rewrite_rule ctxt theorem
          val lhs = Thm.term_of (Thm.lhs_of equation)
          val rhs = Thm.term_of (Thm.rhs_of equation)
          val expected_name = Sign.intern_const thy name
          val actual_name =
            (case lhs of Const (constant, _) => constant | _ => "")
          val _ = if actual_name = expected_name andalso
              fastype_of lhs = expectedT andalso fastype_of rhs = expectedT andalso
              Comma_Semantic_B1_Column_Conversion.closed lhs andalso
              Comma_Semantic_B1_Column_Conversion.closed rhs andalso
              Thm.nprems_of equation = 0 andalso null (Thm.hyps_of equation) andalso
              null (Thm.tpairs_of equation)
            then () else error ("B1 lift-column definition has invalid shape: " ^ name)
        in equation end
      val root_name = "comma_semantic_b1_crt_lift_column_ids"
      val descriptor_name = "comma_semantic_b1_crt_lift_descriptors"
      val root_definition = Proof_Context.get_thm ctxt (root_name ^ "_def")
      val root_equation = exact_equation root_name rootT root_definition
      val root_body = Thm.term_of (Thm.rhs_of root_equation)
      val (concat_head, concat_arguments) = strip_comb root_body
      val blocks_constant =
        (case (concat_head, concat_arguments) of
          (Const (constant, _), [directory]) =>
            if constant = @{const_name concat} then directory
            else error "B1 lift-column root is not an authenticated block concatenation"
        | _ => error "B1 lift-column root is not an authenticated block concatenation")
      val expected_directory = Sign.intern_const thy lift_column_id_blocks_name
      val _ = (case blocks_constant of
        Const (constant, T) => if constant = expected_directory andalso T = blocksT then ()
          else error "B1 lift-column root names a foreign block directory"
      | _ => error "B1 lift-column root names a malformed block directory")
      val directory_definition = Proof_Context.get_thm ctxt
        (lift_column_id_blocks_name ^ "_def")
      val directory_equation = exact_equation lift_column_id_blocks_name
        blocksT directory_definition
      val descriptor_equation = exact_equation descriptor_name
        (HOLogic.listT descriptorT)
        (Proof_Context.get_thm ctxt (descriptor_name ^ "_def"))
      val descriptor_count = length
        (HOLogic.dest_list (Thm.term_of (Thm.rhs_of descriptor_equation)))
      val root_children = HOLogic.dest_list
        (Thm.term_of (Thm.rhs_of directory_equation))
      val expected_block_count =
        (descriptor_count + lift_column_id_block_size - 1) div lift_column_id_block_size
      val _ = if length root_children = expected_block_count then ()
        else error "B1 lift-column block directory has the wrong extent"
      fun child_name index = lift_column_id_block_name index
      fun child_constant_matches (index, term) =
        (case term of
          Const (constant, T) => T = blockT andalso
            constant = Sign.intern_const thy (child_name index)
        | _ => false)
      val _ = if forall child_constant_matches (map_index (fn item => item) root_children)
        then () else error "B1 lift-column block directory is foreign, missing, or reordered"
      val child_definitions = map_index (fn (index, _) =>
        Proof_Context.get_thm ctxt (child_name index ^ "_def")) root_children
      val child_equations = map_index (fn (index, theorem) =>
        exact_equation (child_name index) blockT theorem) child_definitions
      fun child_extent (index, equation) =
        let
          val rows = HOLogic.dest_list (Thm.term_of (Thm.rhs_of equation))
          val extent = length rows
          val expected_extent = if index + 1 < length child_equations then
              lift_column_id_block_size
            else descriptor_count - index * lift_column_id_block_size
          val _ = if extent = expected_extent andalso extent > 0 then ()
            else error "B1 lift-column block has a malformed row extent"
          val _ = if forall (fn row => fastype_of row = rowT) rows then ()
            else error "B1 lift-column block contains a malformed CID row"
        in extent end
      val child_row_extents = map_index child_extent child_equations
      val row_count = fold (fn extent => fn total => extent + total)
        child_row_extents 0
      val _ = if row_count = descriptor_count then ()
        else error "B1 lift-column blocks do not cover the descriptor rows"
      val all_definitions = root_equation :: directory_equation ::
        descriptor_equation :: child_equations
      val _ = if null (Thm_Deps.all_oracles all_definitions) then ()
        else error "B1 lift-column definitions depend on an oracle"
      val _ = Comma_Proof_Profile.report
        ("B1 publication stage=lift-column-id-block-catalogue rows=" ^
          Int.toString row_count ^ " blocks=" ^
          Int.toString (length child_definitions))
    in
      (* Keep the public field names for existing consumers, but publish the
         validated meta equations rather than the raw local definitions. *)
      {root_definition = root_equation,
       directory_definition = directory_equation,
       child_definitions = child_equations,
       child_row_extents = child_row_extents,
       row_count = row_count}: lift_column_id_block_catalogue
    end

  fun template_projection dag_constant template_ids_constant =
    let
      val natT = Candidate.natT
      val columnT = Candidate.columnT
      val dagT = @{typ comma_semantic_b1_crt_column_dag}
      val id_rowT = HOLogic.listT natT
      val id_rowsT = HOLogic.listT id_rowT
      val column_rowT = HOLogic.listT columnT
      val column_rowsT = HOLogic.listT column_rowT
      val column_at = Const (@{const_name comma_semantic_b1_crt_column_at},
        dagT --> natT --> columnT)
      val map_column_row = Const (@{const_name map},
        (natT --> columnT) --> id_rowT --> column_rowT) $
        (column_at $ dag_constant)
      val map_column_rows = Const (@{const_name map},
        (id_rowT --> column_rowT) --> id_rowsT --> column_rowsT)
    in map_column_rows $ map_column_row $ template_ids_constant end

  fun serialize_lift_ref reference =
    let
      val natT = @{typ nat}
      val refT = @{typ comma_semantic_b1_crt_lift_ref}
    in
      (case reference of
        Candidate.Terminal_Ref (slot, parent) =>
          Const (@{const_name Comma_B1_Lift_Terminal_Ref}, natT --> natT --> refT) $
            Candidate.nat slot $ Candidate.nat parent
      | Candidate.Goto_Ref (slot, child, lift_cid) =>
          Const (@{const_name Comma_B1_Lift_Goto_Ref},
            natT --> natT --> natT --> refT) $
            Candidate.nat slot $ Candidate.nat child $ Candidate.nat lift_cid)
    end

  fun serialize_lift_refs rows =
    let
      val refT = @{typ comma_semantic_b1_crt_lift_ref}
    in
      HOLogic.mk_list (HOLogic.listT refT)
        (map (fn refs => HOLogic.mk_list refT (map serialize_lift_ref refs)) rows)
    end

  fun serialize_lift_descriptor
      ({period, slot, template_cid, net_shift}: Candidate.lift_descriptor) =
    let
      val natT = @{typ nat}
      val descriptorT = @{typ comma_semantic_b1_crt_lift_descriptor}
      val makeT = natT --> natT --> natT --> natT --> descriptorT
      val make = Const
        (@{const_name comma_semantic_b1_crt_lift_descriptor.make}, makeT)
    in
      make $ Candidate.nat period $ Candidate.nat slot $
        Candidate.nat template_cid $ Candidate.nat net_shift
    end

  fun serialize_lift_descriptors descriptors =
    HOLogic.mk_list @{typ comma_semantic_b1_crt_lift_descriptor}
      (map serialize_lift_descriptor descriptors)

  fun publish lthy =
    let
      val _ = check_shared_column_dag_example ()
      val (artifact, generated_lthy) =
        Comma_Semantic_B1_Template_Constructor.make lthy
      val lift_descriptors_term =
        serialize_lift_descriptors (#lift_descriptors artifact)
      val lift_refs_term = serialize_lift_refs (#lift_refs artifact)
      val column_dag = artifact_column_dag artifact
      val descriptor_terms = HOLogic.dest_list (#occurrence_descriptors_term artifact)
      fun descriptor_template_cid descriptor =
        let
          val (cid_term, _) = HOLogic.dest_prod descriptor
        in
          (case HOLogic.dest_number cid_term of
            (typ, cid) => if typ = Candidate.natT andalso cid >= 0 then cid
              else error "B1 descriptor mass root has a non-natural CID")
        end
      fun remember_template cid (seen, reversed) =
        if Inttab.defined seen cid then (seen, reversed)
        else (Inttab.update (cid, ()) seen, cid :: reversed)
      val (_, reversed_template_cids) = fold remember_template
        (map descriptor_template_cid descriptor_terms) (Inttab.empty, [])
      val template_cids = rev reversed_template_cids
      val root_keys = maps (fn cid =>
        (case try List.nth (#template_keys artifact, cid) of
          SOME keys => keys
        | NONE => error "B1 descriptor references a foreign template CID"))
        template_cids
      fun remember_root cid (seen, reversed) =
        if Inttab.defined seen cid then (seen, reversed)
        else (Inttab.update (cid, ()) seen, cid :: reversed)
      val (_, reversed_root_cids) = fold remember_root
        (map (fn key => #cid column_dag key) root_keys) (Inttab.empty, [])
      val root_cids = rev reversed_root_cids
      val column_node_rows = column_rows column_dag
      val mass_rows = map (fn (cid, level, children) =>
        {cid = cid, level = level, children = children}:
          Comma_Semantic_B1_Mass_Candidate.node_row) column_node_rows
      val (mass_annotation_body, mass_annotation_cids) =
        Comma_Semantic_B1_Mass_Candidate.make_annotation_from_rows
          (length (#node_keys column_dag) + 2)
          (fn level => Vector.sub (Comma_Semantic_B1_Column_Catalog.periods, level))
          root_cids mass_rows
      val mass_annotation_definition : global_definition =
        {name = mass_annotation_name,
         T = fastype_of mass_annotation_body,
         rhs = (fn _ => mass_annotation_body)}
      val template_column_ids_term =
        serialize_column_ids column_dag (#template_keys artifact)
      val lift_column_id_block_definitions = serialize_lift_column_id_block_definitions
        column_dag (#lift_column_keys artifact)
      val lift_column_id_blocks_root_definition = lift_column_id_blocks_definition
        (length lift_column_id_block_definitions)
      val lift_column_ids_root_definition = lift_column_ids_definition
      val _ = Comma_Proof_Profile.report
        ("B1 publication stage=lift-column-id-block-batch rows=" ^
          Int.toString (length (#lift_column_keys artifact)) ^ " blocks=" ^
          Int.toString (length lift_column_id_block_definitions))
      val piece_sources = #construction_piece_refs artifact
      val piece_source_count = length piece_sources
      val source_count = length (HOLogic.dest_list (#normalized_sources_term artifact))
      val _ = if piece_source_count = source_count then ()
        else error "B1 construction pieces lost source-index alignment"
      val piece_source_definitions = serialize_construction_piece_source_blocks
        column_dag piece_sources
      val piece_source_directory_definition =
        construction_piece_source_blocks_definition piece_sources
      val _ = Comma_Proof_Profile.report
        ("B1 publication stage=construction-piece-source-batch sources=" ^
         Int.toString piece_source_count)
      val _ = if getenv "COMMA_PROFILE_LOG" = "" then ()
        else Comma_Proof_Profile.report
          ("B1 compact lift artifact " ^ #stats artifact ())
      val node_started = Time.now ()
      val _ = Comma_Proof_Profile.report
        "B1 publication stage=global-column-dag-data-start"
      val {dag_constant, lthy = columns_lthy, ...} =
        define_column_data column_dag column_node_rows generated_lthy
      val _ = Comma_Proof_Profile.report
        ("B1 publication stage=global-column-dag-data-complete cids=" ^
          Int.toString (length (#node_keys column_dag) + 2) ^ " templates=" ^
          Int.toString (length (#template_keys artifact)) ^ " lifts=" ^
          Int.toString (length (#lift_column_keys artifact)) ^
          " elapsed_ms=" ^
          Comma_Proof_Profile.elapsed_ms node_started)
      val _ = Comma_Proof_Profile.report "B1 publication artifact ready"
      val template_ids_name = "comma_semantic_b1_crt_template_column_ids"
      val template_columns_type = HOLogic.listT
        (HOLogic.listT @{typ comma_crt_column})
      fun data name T term : global_definition =
        {name = name, T = T, rhs = (fn _ => term)}
      val artifact_definitions =
        [data template_ids_name (fastype_of template_column_ids_term)
           template_column_ids_term] @ lift_column_id_block_definitions @
        [lift_column_id_blocks_root_definition, lift_column_ids_root_definition] @
        piece_source_definitions @
        [piece_source_directory_definition,
         construction_piece_refs_definition piece_sources,
         {name = "comma_semantic_b1_crt_templates", T = template_columns_type,
          rhs = (fn constants => template_projection dag_constant
            (lookup_global_constant "artifact batch" constants template_ids_name))},
         data "comma_semantic_b1_crt_descriptors"
           (fastype_of (#occurrence_descriptors_term artifact))
           (#occurrence_descriptors_term artifact),
         data "comma_semantic_b1_crt_sources"
           (fastype_of (#normalized_sources_term artifact))
           (#normalized_sources_term artifact),
         data "comma_semantic_b1_crt_root_occurrence_indices"
           (fastype_of (#root_occurrence_indices_term artifact))
           (#root_occurrence_indices_term artifact),
         data "comma_semantic_b1_crt_lift_descriptors"
           (fastype_of lift_descriptors_term) lift_descriptors_term,
         data "comma_semantic_b1_crt_lift_refs"
           (fastype_of lift_refs_term) lift_refs_term,
         mass_annotation_definition]
      val (defined_artifacts, next) = define_global_definitions "artifact-data-batch"
        artifact_definitions columns_lthy
      val defined_mass_annotation =
        (case get_first (fn (defined: defined_global) =>
            if #name defined = mass_annotation_name then SOME defined else NONE)
            defined_artifacts of
          SOME defined => defined
        | NONE => error "B1 publication omitted the mass annotation definition")
      val mass_annotation : mass_annotation =
        {constant = #constant defined_mass_annotation,
         body = mass_annotation_body,
         definition = #theorem defined_mass_annotation,
         cids = mass_annotation_cids, roots = root_cids}
      val next_with_mass_annotation = Local_Theory.background_theory
        (fn thy => Mass_Annotation_Data.put (SOME mass_annotation) thy) next
    in next_with_mass_annotation end

end
