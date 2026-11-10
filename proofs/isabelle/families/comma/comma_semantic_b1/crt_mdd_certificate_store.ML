(* One immutable semantic table and one wellformedness proof per frozen arena.
   A single nested chunk constant backs its balanced root; bounded indexed
   conversion avoids per-chunk definitions and full-table flattening. *)
signature COMMA_CRT_MDD_CERTIFICATE_STORE =
sig
  type store
  datatype node = Leaf of int | Branch of int * int list
  val make: string -> Comma_CRT_MDD_Arena.arena -> local_theory -> store * local_theory
  val context: store -> Proof.context
  val table: store -> term
  val radices: store -> term
  val wellformed: store -> thm
  val node_count: store -> int
  val node: store -> int -> node
  val node_term: node -> term
  val lookup: store -> int -> thm
  val phase_leaf: store -> int -> thm
  val bound: store -> int -> thm
  val action_index: store -> Comma_CRT_MDD_Arena.action_root -> int
  val boolean_index: store -> Comma_CRT_MDD_Arena.boolean_root -> int
  val bind_witness: store -> Comma_CRT_MDD_Arena.bind_key -> Comma_CRT_MDD_Arena.bind_witness
  val statistics: store -> string
end

structure Comma_CRT_MDD_Certificate_Store :> COMMA_CRT_MDD_CERTIFICATE_STORE =
struct
  structure Arena = Comma_CRT_MDD_Arena
  structure Proof_Utils = Comma_CRT_MDD_Proof_Utils
  datatype node = Leaf of int | Branch of int * int list
  val natT = @{typ nat}
  val natOptionT = Type (@{type_name option}, [natT])
  val nodeT = @{typ "nat comma_crt_mdd_node"}
  val nodesT = HOLogic.listT nodeT
  fun nat n = HOLogic.mk_number natT n
  fun nth nodes index = Const (@{const_name nth}, nodesT --> natT --> nodeT) $
    nodes $ nat index
  fun length_term nodes = Const (@{const_name size}, nodesT --> natT) $ nodes
  val closed = Proof_Utils.closed
  val natural = Proof_Utils.dest_nat "MDD node" natT

  fun parse_node term =
    (case Term.strip_comb term of
      (Const (name,_),[payload]) =>
        if name = @{const_name Comma_CRT_MDD_Leaf} then Leaf (natural payload)
        else error "MDD node has an unknown leaf constructor"
    | (Const (name,_),[axis,children]) =>
        if name = @{const_name Comma_CRT_MDD_Branch} then
          Branch (natural axis,map natural (HOLogic.dest_list children))
        else error "MDD node has an unknown branch constructor"
    | _ => error "MDD node is not a literal constructor")

  fun node_term (Leaf payload) =
        Const (@{const_name Comma_CRT_MDD_Leaf},natT --> nodeT) $ nat payload
    | node_term (Branch (axis,children)) =
        Const (@{const_name Comma_CRT_MDD_Branch},
          natT --> @{typ "nat list"} --> nodeT) $ nat axis $
          HOLogic.mk_list natT (map nat children)

  datatype store = Store of
    {arena: Arena.arena, ctxt: Proof.context, table: term, radices: term,
     count: int, nodes: node Vector.vector,
     wellformed: thm, lookup: int -> thm, bound: int -> thm,
     phase_leaf_cache: thm Inttab.table Unsynchronized.ref,
     statistics: unit -> string}

  fun context (Store data) = #ctxt data
  fun table (Store data) = #table data
  fun radices (Store data) = #radices data
  fun wellformed (Store data) = #wellformed data
  fun node_count (Store data) = #count data
  fun statistics (Store data) = #statistics data ()
  fun check_index (Store data) index =
    if 0 <= index andalso index < #count data then index
    else error "MDD root is outside its frozen certificate table"
  fun lookup (store as Store data) index = #lookup data (check_index store index)
  fun node (store as Store data) index =
    Vector.sub (#nodes data,check_index store index)
  fun bound (store as Store data) index = #bound data (check_index store index)
  fun phase_leaf (store as Store data) index =
    let
      val index = check_index store index
      val payload = (case Vector.sub (#nodes data,index) of
        Leaf value => value
      | Branch _ => error "MDD phase-leaf request names a branch")
    in
      (case Inttab.lookup (!(#phase_leaf_cache data)) index of
        SOME theorem => theorem
      | NONE =>
          let
            val ctxt = #ctxt data
            val phase = Free ("mdd_phase_leaf_phase",natT)
            val root = nat index
            val eval = Const (@{const_name comma_crt_mdd_eval_phase},
              @{typ "nat list"} --> nodesT --> natT --> natT --> natOptionT) $
              #radices data $ #table data $ phase $ root
            val some = Const (@{const_name Some},natT --> natOptionT) $ nat payload
            val body = HOLogic.mk_Trueprop (HOLogic.mk_eq (eval,some))
            val expected = Logic.all phase body
            val expected_lookup = Logic.mk_equals
              (nth (#table data) index,node_term (Leaf payload))
            val leaf_lookup = Proof_Utils.exact_prop ctxt
              "Frozen MDD phase-leaf row" expected_lookup (#lookup data index)
            val theorem = @{thm comma_crt_mdd_eval_phase_leaf} OF
              [#wellformed data,#bound data index,
               leaf_lookup RS @{thm meta_eq_to_obj_eq}]
            val pointwise = Drule.infer_instantiate ctxt
              [(("phase",0),Thm.cterm_of ctxt phase)] theorem
            val generalized = Thm.forall_intr (Thm.cterm_of ctxt phase) pointwise
            val theorem = Proof_Utils.exact_prop ctxt
              "Frozen MDD phase leaf evaluation" expected generalized
            val _ = #phase_leaf_cache data :=
              Inttab.update (index,theorem) (!(#phase_leaf_cache data))
          in theorem end)
    end
  fun action_index (store as Store data) root =
    check_index store (Arena.action_index (#arena data) root)
  fun boolean_index (store as Store data) root =
    check_index store (Arena.boolean_index (#arena data) root)
  fun bind_witness (store as Store data) key =
    let
      fun check_key (source,fallback,mapping) =
        List.app (fn id => ignore (check_index store id))
          (source :: fallback :: map #2 mapping)
      val _ = check_key key
      val witness = Arena.bind_witness (#arena data) key
      val _ = check_key (#key witness)
      val _ = check_index store (#result witness)
      val _ = (case #step witness of
        Arena.Bind_Leaf _ => ()
      | Arena.Bind_Branch (_,children) => List.app check_key children)
    in witness end

  fun exact_closed expected theorem =
    if Thm.prop_of theorem aconv expected andalso Thm.nprems_of theorem = 0
        andalso null (Thm.hyps_of theorem) andalso null (Thm.tpairs_of theorem)
        andalso closed expected
    then theorem else error "MDD certificate has an unexpected or open proposition"

  fun specialize_object_all ctxt argument theorem =
    let
      val body = HOLogic.dest_Trueprop (Thm.prop_of theorem)
      val abstraction =
        (case Term.strip_comb body of
          (Const (name,_),[abs as Abs (_,domainT,_)]) =>
            if name = @{const_name All} andalso domainT = fastype_of argument then abs
            else error "MDD segment specialization has another quantified type"
        | _ => error "MDD segment specialization expects one HOL universal")
      val (_,quantified_ct) = Thm.dest_comb (Thm.cprop_of theorem)
      val (_,predicate_ct) = Thm.dest_comb quantified_ct
      val rule = Drule.infer_instantiate' ctxt
        [SOME predicate_ct,SOME (Thm.cterm_of ctxt argument)] @{thm spec}
      val specialized = Thm.implies_elim rule theorem
      val expected = HOLogic.mk_Trueprop
        (Envir.beta_eta_contract (abstraction $ argument))
    in Proof_Utils.exact_prop ctxt "MDD segment specialization" expected specialized end

  type table_piece = {term: term, count: int, size: thm}

  fun make name arena lthy =
    let
      val leaf_capacity = 128
      fun checkpoint stage = Comma_Proof_Profile.report
        ("MDD Store " ^ name ^ " stage=" ^ stage)
      val count = Arena.node_count arena
      val _ = if count > 0 andalso count <= 65536 then () else
        error "MDD certificate table exceeds the indexed publication bound"
      val _ = checkpoint ("table-term-start count=" ^ Int.toString count)
      val nodes = Arena.table_term arena
      val _ = if fastype_of nodes = nodesT andalso closed nodes then () else
        error "MDD certificate needs a closed natural-payload table"
      val original_rows = HOLogic.dest_list nodes
      val _ = if length original_rows = count then () else
        error "MDD arena node count disagrees with its frozen row vector"
      val node_views = Vector.fromList (map parse_node original_rows)
      val radix_term = HOLogic.mk_list natT (map nat (Arena.radices arena))
      val _ = checkpoint "table-definition-start"
      val append_term = Const (@{const_name append}, nodesT --> nodesT --> nodesT)
      val size_const = Const (@{const_name size}, nodesT --> natT)
      fun list_size term = Const (@{const_name size},fastype_of term --> natT) $ term
      fun object_size_fact ctxt label term expected_count theorem =
        let
          val expected = HOLogic.mk_Trueprop
            (HOLogic.mk_eq (list_size term,nat expected_count))
        in Proof_Utils.exact_prop ctxt label expected theorem end
      fun literal_size ctxt term expected_count =
        let
          val spine = Comma_Selected_List_Conversion.literal_length_conversion
            (fn () => ()) (Thm.cterm_of ctxt (list_size term))
          val scalar_context = Comma_Entry_Arithmetic.natural_context ctxt
          val scalar = Simplifier.rewrite scalar_context (Thm.rhs_of spine)
          val meta = Thm.transitive spine scalar
          val theorem = meta RS @{thm meta_eq_to_obj_eq}
        in object_size_fact ctxt "MDD literal chunk length" term expected_count theorem end
      fun append_size ctxt left right expected_count left_size right_size =
        let
          val joined = append_term $ left $ right
          val request = Thm.cterm_of ctxt (list_size joined)
          val append_rule = @{thm length_append} RS @{thm eq_reflection}
          val split = Conv.rewr_conv append_rule request
          val plus_const = Const (@{const_name plus},natT --> natT --> natT)
          val left_meta = left_size RS @{thm eq_reflection}
          val right_meta = right_size RS @{thm eq_reflection}
          val left_application = Thm.combination
            (Thm.reflexive (Thm.cterm_of ctxt plus_const)) left_meta
          val child_sum = Thm.combination left_application right_meta
          val after_children = Thm.transitive split child_sum
          val arithmetic = Simplifier.rewrite
            (Comma_Entry_Arithmetic.natural_context ctxt) (Thm.rhs_of after_children)
          val meta = Thm.transitive after_children arithmetic
          val theorem = meta RS @{thm meta_eq_to_obj_eq}
        in object_size_fact ctxt "MDD append chunk length" joined expected_count theorem end

      val leaf_count = (count + leaf_capacity - 1) div leaf_capacity
      val input_chunks =
        let
          fun number [] _ acc = rev acc
            | number (rows::rest) offset acc =
                number rest (offset + length rows) ((offset,rows)::acc)
        in number (chop_groups leaf_capacity original_rows) 0 [] end
      val _ = if length input_chunks = leaf_count andalso
          List.all (fn (_,rows) => not (null rows) andalso
            length rows <= leaf_capacity)
            input_chunks
        then () else error "MDD balanced publication has malformed leaf chunks"
      val _ =
        let
          fun check_chunks [] expected = expected
            | check_chunks ((offset,rows)::rest) expected =
                if offset = expected then
                  check_chunks rest (expected + length rows)
                else error "MDD balanced publication changed chunk order"
          val total = check_chunks input_chunks 0
        in if total = count then () else
          error "MDD balanced publication dropped frozen rows" end
      val chunkT = HOLogic.listT nodeT
      val chunksT = HOLogic.listT chunkT
      val chunk_literals = map (fn (_,rows) => HOLogic.mk_list nodeT rows) input_chunks
      val chunks_rhs = HOLogic.mk_list chunkT chunk_literals
      val _ = if fastype_of chunks_rhs = chunksT andalso closed chunks_rhs then ()
        else error "MDD bounded chunk table is not a closed nested list"
      val _ = checkpoint "chunk-table-define-start"
      val ((local_chunks,(_,local_chunks_definition)),lthy_chunks) = Local_Theory.define
        ((Binding.name (name ^ "_chunks"),NoSyn),
         ((Binding.name (name ^ "_chunks_def"),[]),chunks_rhs)) lthy
      val chunks_morphism = Local_Theory.target_morphism lthy_chunks
      val chunks = Morphism.term chunks_morphism local_chunks
      val chunks_definition = Morphism.thm chunks_morphism local_chunks_definition
      val _ = exact_closed (Logic.mk_equals (chunks,chunks_rhs)) chunks_definition
      val chunk_ctxt = Local_Theory.target_of lthy_chunks
      val _ = checkpoint "chunk-table-define-complete"
      fun chunk_at index =
        Const (@{const_name nth},chunksT --> natT --> chunkT) $ chunks $ index
      fun row_at chunk_index local_index =
        Const (@{const_name nth},chunkT --> natT --> nodeT) $
          chunk_at chunk_index $ local_index
      val _ = checkpoint "chunk-selector-start"
      val chunk_index = Free ("mdd_chunk_index",natT)
      val chunk_request = chunk_at chunk_index
      val chunk_selector = Comma_Selected_List_Conversion.make
        {ctxt=chunk_ctxt,name=name ^ "_chunk_selector",
         root_definition=chunks_definition,table_pattern=chunk_request,
         extents=[leaf_count]}
      val chunk_selector_context = Comma_Entry_Arithmetic.natural_context chunk_ctxt
        |> Simplifier.add_proc (#procedure chunk_selector)
        |> Simplifier.add_proc (#post_procedure chunk_selector)
      val _ = checkpoint "chunk-selector-complete"
      val _ = checkpoint "row-selector-start"
      val nested_chunk_index = Free ("mdd_nested_chunk_index",natT)
      val nested_row_index = Free ("mdd_nested_row_index",natT)
      val nested_row_request = row_at nested_chunk_index nested_row_index
      val row_selector = Comma_Selected_List_Conversion.make_nested
        {ctxt=chunk_ctxt,name=name ^ "_row_selector",
         root_definition=chunks_definition,table_pattern=nested_row_request,depth=2}
      val row_selector_context = Comma_Entry_Arithmetic.natural_context chunk_ctxt
        |> Simplifier.add_proc (#procedure row_selector)
        |> Simplifier.add_proc (#post_procedure row_selector)
      val _ = checkpoint "row-selector-complete"
      val _ = checkpoint ("balanced-leaf-start leaves=" ^ Int.toString leaf_count)
      val piece_facts = Unsynchronized.ref (Termtab.empty:
        {count:int,size:thm} Termtab.table)
      fun remember_piece term count size =
        (case Termtab.lookup (!piece_facts) term of
          NONE => piece_facts := Termtab.update (term,{count=count,size=size}) (!piece_facts)
        | SOME old => if #count old = count andalso
              Thm.prop_of (#size old) aconv Thm.prop_of size then ()
            else error "Balanced MDD table reused a term with conflicting size data")
      val indexed_chunks = map_index I input_chunks
      fun make_leaf (chunk_index, (input_offset,rows)) : table_piece =
        let
          val literal = HOLogic.mk_list nodeT rows
          val chunk_term = chunk_at (nat chunk_index)
          val selected_chunk = Simplifier.rewrite chunk_selector_context
            (Thm.cterm_of chunk_ctxt chunk_term)
          val chunk_equation = exact_closed (Logic.mk_equals (chunk_term,literal)) selected_chunk
          val literal_size_fact = literal_size chunk_ctxt literal (length rows)
          val chunk_size_const = Const (@{const_name size},chunkT --> natT)
          val lifted_chunk = Thm.combination
            (Thm.reflexive (Thm.cterm_of chunk_ctxt chunk_size_const)) chunk_equation
          val chunk_size_meta = Thm.transitive lifted_chunk
            (literal_size_fact RS @{thm eq_reflection})
          val leaf_size = object_size_fact chunk_ctxt "MDD selected chunk length"
            chunk_term (length rows) (chunk_size_meta RS @{thm meta_eq_to_obj_eq})
          val _ = if input_offset = chunk_index * leaf_capacity then () else
            error "MDD chunk index disagrees with its checked source offset"
          val _ = remember_piece chunk_term (length rows) leaf_size
        in {term=chunk_term, count=length rows, size=leaf_size} end
      val leaves = map make_leaf indexed_chunks
      val _ = checkpoint "balanced-leaf-complete"
      val piece_children = Unsynchronized.ref (Termtab.empty:
        (table_piece * table_piece) Termtab.table)

      fun append_pieces (left: table_piece, right: table_piece): table_piece =
        let
          val left_term = #term left
          val right_term = #term right
          val count_left = #count left
          val count_right = #count right
          val joined = append_term $ left_term $ right_term
          val total = count_left + count_right
          val joined_size = append_size chunk_ctxt left_term right_term total
            (#size left) (#size right)
          val piece = {term=joined, count=total, size=joined_size}
          val _ = remember_piece joined total joined_size
          val _ = piece_children := Termtab.update (joined,(left,right)) (!piece_children)
        in piece end
      val root_piece = Balanced_Tree.make append_pieces leaves
      val root_expression = #term root_piece
      val _ = if #count root_piece = count then () else
        error "Balanced MDD publication changed the frozen node count"
      val _ = if fastype_of root_expression = nodesT andalso
          closed root_expression then () else
        error "Balanced MDD append expression is not a closed node table"
      val _ = checkpoint "balanced-append-assembly-complete"
      val _ = checkpoint "local-theory-define-start"
      val ((local_table, (_, local_definition)), lthy') = Local_Theory.define
        ((Binding.name name, NoSyn),
         ((Binding.name (name ^ "_def"), []), root_expression)) lthy_chunks
      val _ = checkpoint "local-theory-define-complete"
      val morphism = Local_Theory.target_morphism lthy'
      val table = Morphism.term morphism local_table
      val definition = Morphism.thm morphism local_definition
      val _ = exact_closed (Logic.mk_equals (table,root_expression)) definition
      val ctxt = Local_Theory.target_of lthy'
      val root_size_expected = HOLogic.mk_Trueprop
        (HOLogic.mk_eq (length_term table, nat count))
      val definition_equality = exact_closed
        (Logic.mk_equals (table,root_expression)) definition
      val size_application = Thm.combination (Thm.reflexive (Thm.cterm_of ctxt size_const))
        definition_equality
      val root_size_meta = Thm.transitive size_application
        (#size root_piece RS @{thm eq_reflection})
      val root_size = exact_closed root_size_expected
        (root_size_meta RS @{thm meta_eq_to_obj_eq})
      val _ = checkpoint "root-size-transport-complete"
      val definition_context = Comma_Entry_Arithmetic.natural_context ctxt
        |> Simplifier.add_simps [root_size]
      val _ = checkpoint "balanced-table-definition-complete"

      fun segment_term source index =
        Const (@{const_name nth},fastype_of source --> natT --> nodeT) $
          source $ index
      val add_nat = Const (@{const_name plus},natT --> natT --> natT)
      fun plus_nat left right = add_nat $ left $ right
      fun segment_proposition source offset =
        let
          val index = Free ("mdd_segment_index",natT)
          val body = HOLogic.mk_imp
            (HOLogic.mk_binrel @{const_name less} (index,list_size source),
             HOLogic.mk_eq
              (segment_term table (plus_nat offset index),segment_term source index))
        in HOLogic.mk_Trueprop (HOLogic.mk_all ("mdd_segment_index",natT,body)) end
      val _ = checkpoint "root-segment-start"
      val zero = HOLogic.mk_number natT 0
      val root_segment_expected = segment_proposition root_expression zero
      val root_rows = definition RS @{thm meta_eq_to_obj_eq}
      val root_segment = @{thm comma_crt_mdd_segment_root} OF [root_rows]
      val root_segment = Proof_Utils.exact_prop ctxt
        "MDD named table root segment" root_segment_expected root_segment
      val _ = checkpoint "root-segment-complete"

      type leaf_segment =
        {offset:term, offset_value:int, term:term, count:int, segment:thm}
      fun children_of source =
        (case Term.strip_comb source of
          (Const (constant,_),[left,right]) =>
            if constant = @{const_name append} then SOME (left,right) else NONE
        | _ => NONE)
      fun piece_info source =
        (case Termtab.lookup (!piece_facts) source of
          SOME info => info
        | NONE => error "Balanced MDD segment lost its size metadata")
      fun child_pieces parent left right =
        (case Termtab.lookup (!piece_children) parent of
          SOME (left_piece,right_piece) =>
            if #term left_piece aconv left andalso #term right_piece aconv right then
              (left_piece,right_piece)
            else error "Balanced MDD append metadata changed child order"
        | NONE => error "Balanced MDD append node has no recorded children")
      fun derive_children parent_segment parent left right offset offset_value =
        let
          val (left_piece,right_piece) = child_pieces parent left right
          val left_segment = @{thm comma_crt_mdd_segment_left_sized} OF [parent_segment]
          val _ = Proof_Utils.exact_prop ctxt "MDD left child segment"
            (segment_proposition left offset) left_segment
          val right_offset_value = offset_value + #count left_piece
          val right_offset = nat right_offset_value
          val rebase_prop = HOLogic.mk_Trueprop (HOLogic.mk_eq
            (plus_nat offset (list_size left),right_offset))
          val rebase_context = Comma_Entry_Arithmetic.natural_context ctxt
            |> Simplifier.add_simps [#size left_piece]
          val rebase = Proof_Utils.prove_exact ctxt "MDD right segment offset"
            rebase_prop (fn proof_ctxt =>
              Simplifier.asm_full_simp_tac rebase_context 1)
          val right_segment =
            @{thm comma_crt_mdd_segment_right_sized} OF [parent_segment,rebase]
          val _ = Proof_Utils.exact_prop ctxt "MDD right child segment"
            (segment_proposition right right_offset) right_segment
          val _ = if #count left_piece = #count (piece_info left) andalso
              #count right_piece = #count (piece_info right) then ()
            else error "Balanced MDD child count metadata is inconsistent"
        in (left_segment,right_segment,right_offset,right_offset_value) end
      val _ = checkpoint "segment-propagation-start"
      fun collect_segments source offset offset_value segment acc =
        (case children_of source of
          NONE =>
            let
              val info = piece_info source
              val _ = if #count info > 0 andalso #count info <= leaf_capacity then ()
                else error "MDD selected segment is outside bounded leaf size"
              val _ = Proof_Utils.exact_prop ctxt "MDD leaf segment"
                (segment_proposition source offset) segment
            in ({offset=offset,offset_value=offset_value,term=source,
              count= #count info,segment=segment} :: acc) end
        | SOME (left,right) =>
            let
              val (left_segment,right_segment,right_offset,right_offset_value) =
                derive_children segment source left right offset offset_value
              val after_left = collect_segments left offset offset_value left_segment acc
            in collect_segments right right_offset right_offset_value right_segment after_left end)
      val leaf_segments = rev (collect_segments root_expression zero 0 root_segment [])
      val leaf_layout_ok = length leaf_segments = leaf_count andalso
        ListPair.allEq (fn (leaf,(chunk_index,(input_offset,rows))) =>
          #offset_value leaf = input_offset andalso
          #count leaf = length rows andalso
          #term leaf aconv chunk_at (nat chunk_index))
          (leaf_segments,indexed_chunks)
      val _ = if leaf_layout_ok then () else
        error "MDD balanced segment propagation changed literal chunk order"
      val _ = checkpoint "segment-propagation-complete"
      val _ = checkpoint "leaf-selector-start"
      val arithmetic_context = Comma_Entry_Arithmetic.natural_context ctxt
      fun make_leaf_bound_context (leaf:leaf_segment) =
        let
          val bound_context = arithmetic_context
            |> Simplifier.add_simps [#size (piece_info (#term leaf))]
        in (leaf,bound_context) end
      val leaf_bound_contexts = Vector.fromList (map make_leaf_bound_context leaf_segments)
      val _ = checkpoint "leaf-bound-context-complete"
      val selected_elapsed = Unsynchronized.ref Time.zeroTime
      val segment_elapsed = Unsynchronized.ref Time.zeroTime
      val bound_elapsed = Unsynchronized.ref Time.zeroTime
      val offset_elapsed = Unsynchronized.ref Time.zeroTime
      val ordered_elapsed = Unsynchronized.ref Time.zeroTime
      fun timed elapsed action =
        let
          val started = Time.now ()
          val result = action ()
          val _ = elapsed := Time.+ (!elapsed,Time.- (Time.now (),started))
        in result end
      fun elapsed_ms elapsed = LargeInt.toString (Time.toMilliseconds (!elapsed))
      fun find_leaf index =
        let
          val leaf_index = index div leaf_capacity
          val selected = (Vector.sub (leaf_bound_contexts,leaf_index)
            handle Subscript => error "MDD node lookup has no bounded literal segment")
          val (leaf,_) = selected
          val _ = if #offset_value leaf = leaf_index * leaf_capacity andalso
              index >= #offset_value leaf andalso
              index < #offset_value leaf + #count leaf then ()
            else error "MDD bounded chunk routing disagrees with certified segments"
        in selected end
      val lookup_cache = Unsynchronized.ref (Inttab.empty: thm Inttab.table)
      fun lookup index =
        (case Inttab.lookup (!lookup_cache) index of
          SOME theorem => theorem
        | NONE =>
            let
              val (leaf,bound_context) = find_leaf index
              val local_index = index - #offset_value leaf
              val local_term = nat local_index
              val chunk_number = nat (#offset_value leaf div leaf_capacity)
              val leaf_request = row_at chunk_number local_term
              val selected_equation = timed selected_elapsed (fn () =>
                Simplifier.rewrite row_selector_context (Thm.cterm_of chunk_ctxt leaf_request))
              val selected_expected = Logic.mk_equals
                (leaf_request,node_term (Vector.sub (node_views,index)))
              val selected_equation = exact_closed selected_expected selected_equation
              val segment_imp = timed segment_elapsed (fn () =>
                specialize_object_all ctxt local_term (#segment leaf))
              val bound_prop = HOLogic.mk_Trueprop (HOLogic.mk_binrel @{const_name less}
                (local_term,list_size (#term leaf)))
              val bound = timed bound_elapsed (fn () =>
                Proof_Utils.prove_exact ctxt "MDD local chunk index bound"
                  bound_prop (fn proof_ctxt =>
                    Simplifier.asm_full_simp_tac bound_context 1))
              val segment_at = @{thm mp} OF [segment_imp,bound]
              val offset_expression = plus_nat (#offset leaf) local_term
              val offset_equation = timed offset_elapsed (fn () =>
                Simplifier.rewrite arithmetic_context (Thm.cterm_of ctxt offset_expression))
              val _ = exact_closed (Logic.mk_equals (offset_expression,nat index)) offset_equation
              val nth_table = Const (@{const_name nth},nodesT --> natT --> nodeT) $ table
              val offset_applied = Thm.combination
                (Thm.reflexive (Thm.cterm_of ctxt nth_table)) offset_equation
              val segment_meta = segment_at RS @{thm eq_reflection}
              val lookup_meta = Thm.transitive (Thm.symmetric offset_applied)
                (Thm.transitive segment_meta selected_equation)
              val request = nth table index
              val expected = Logic.mk_equals
                (request,node_term (Vector.sub (node_views,index)))
              val theorem = exact_closed expected lookup_meta
              val _ = lookup_cache := Inttab.update (index,theorem) (!lookup_cache)
            in theorem end)

      val axis_cache = Unsynchronized.ref (Inttab.empty: thm Inttab.table)
      val axis_context = put_simpset HOL_basic_ss ctxt
        |> Simplifier.add_simps @{thms comma_crt_mdd_node_axis.simps}
      fun axis_value (Leaf _) = Const (@{const_name None},natOptionT)
        | axis_value (Branch (axis,_)) =
            Const (@{const_name Some},natT --> natOptionT) $ nat axis
      fun axis_lookup index =
        (case Inttab.lookup (!axis_cache) index of
          SOME theorem => theorem
        | NONE =>
            let
              val node_lookup = lookup index
              val axis_const = Const (@{const_name comma_crt_mdd_node_axis},
                nodeT --> natOptionT)
              val request = axis_const $ nth table index
              val applied = Thm.combination
                (Thm.reflexive (Thm.cterm_of ctxt axis_const)) node_lookup
              val reduced = Simplifier.rewrite axis_context (Thm.rhs_of applied)
              val theorem = Thm.transitive applied reduced
              val expected = Logic.mk_equals
                (request,axis_value (Vector.sub (node_views,index)))
              val theorem = exact_closed expected theorem
              val _ = axis_cache := Inttab.update (index,theorem) (!axis_cache)
            in theorem end)

      val node_context = definition_context |> Simplifier.add_simps
        @{thms list.simps list.size list_all_Cons_iff list_all_Nil_iff
          option.simps nth_Cons_0 nth_Cons_Suc nth_Cons'}
      val predicate = Const (@{const_name comma_crt_mdd_node_ordered},
        @{typ "nat list"} --> nodesT --> natT --> @{typ bool}) $ radix_term $ table
      fun checked_true label context proposition =
        let
          val expected = HOLogic.mk_Trueprop proposition
          val conversion = Simplifier.rewrite context
            (Thm.cterm_of ctxt proposition)
          val reduced = Thm.term_of (Thm.rhs_of conversion)
          val _ = if reduced aconv @{term True} then ()
            else error (label ^ " did not reduce to True")
          val theorem = conversion RS @{thm meta_eq_to_obj_eq} RS @{thm eqTrueE}
        in exact_closed expected theorem end
      fun checked_conjuncts label context propositions =
        let
          fun conjunction [] = error "Cannot certify an empty MDD fact conjunction"
            | conjunction [proposition] = proposition
            | conjunction (proposition::rest) =
                HOLogic.mk_conj (proposition,conjunction rest)
          val theorem = checked_true label context (conjunction propositions)
          fun project [_] theorem = [theorem]
            | project (_::rest) theorem =
                (theorem RS @{thm conjunct1}) ::
                  project rest (theorem RS @{thm conjunct2})
            | project [] _ = error "MDD fact projection lost its proposition list"
        in project propositions theorem end
      fun less left right = HOLogic.mk_binrel @{const_name less} (left,right)
      fun unique_ids ids =
        let
          fun add id (seen, kept) =
            if Inttab.defined seen id then (seen, kept)
            else (Inttab.update (id, ()) seen, id::kept)
          val (_, reversed) = fold add ids (Inttab.empty, [])
        in rev reversed end
      fun prove_item index =
        let
          val _ = if index mod 256 = 0 then checkpoint
            ("node-start index=" ^ Int.toString index ^
             " selected_ms=" ^ elapsed_ms selected_elapsed ^
             " segment_ms=" ^ elapsed_ms segment_elapsed ^
             " bound_ms=" ^ elapsed_ms bound_elapsed ^
             " offset_ms=" ^ elapsed_ms offset_elapsed ^
             " ordered_ms=" ^ elapsed_ms ordered_elapsed) else ()
          val expected = HOLogic.mk_Trueprop (predicate $ nat index)
          val node_lookup = lookup index
          val node_view = Vector.sub (node_views,index)
          val children = (case node_view of Leaf _ => [] | Branch (_,ids) => ids)
          val child_facts = map axis_lookup (unique_ids children)
          val item_context = node_context
            |> Simplifier.add_simps
              (node_lookup :: child_facts)
          val theorem = timed ordered_elapsed (fn () =>
            let
              val node_binding = node_lookup RS @{thm meta_eq_to_obj_eq}
            in case node_view of
              Leaf _ =>
                let
                  val root_bound = checked_true "MDD ordered-row root bound"
                    item_context (less (nat index) (length_term table))
                in
                (Drule.infer_instantiate ctxt
                  [(("radices",0),Thm.cterm_of ctxt radix_term)]
                  @{thm comma_crt_mdd_node_ordered_leaf_intro}) OF
                  [root_bound,node_binding]
                end
            | Branch (axis,children) =>
                let
                  val radix_at = Const (@{const_name nth},
                    @{typ "nat list"} --> natT --> natT) $ radix_term $ nat axis
                  val axis_bound = less (nat axis) (list_size radix_term)
                  val positive = less (nat 0) radix_at
                  val children_term = HOLogic.mk_list natT (map nat children)
                  val width = HOLogic.mk_eq (list_size children_term,radix_at)
                  val child = Free ("mdd_ordered_child",natT)
                  val child_node = Const (@{const_name nth},nodesT --> natT --> nodeT) $
                    table $ child
                  val child_axis = Const (@{const_name comma_crt_mdd_node_axis},
                    nodeT --> natOptionT) $ child_node
                  val child_axis_guard = Const (@{const_name case_option},
                    @{typ "bool => (nat => bool) => nat option => bool"}) $
                      @{term True} $
                      Term.lambda (Free ("mdd_ordered_child_axis",natT))
                        (less (nat axis) (Free ("mdd_ordered_child_axis",natT))) $
                      child_axis
                  val child_property = Term.lambda child
                    (HOLogic.mk_conj (less child (nat index),child_axis_guard))
                  val child_list_all = Const (@{const_name list_all},
                    fastype_of child_property --> @{typ "nat list"} --> @{typ bool}) $
                      child_property $ children_term
                  val facts = checked_conjuncts "MDD ordered-row branch premises"
                    item_context [less (nat index) (length_term table),axis_bound,
                      positive,width,child_list_all]
                in (case facts of
                  [root_bound,axis_bound',positive',width',child_order] =>
                    @{thm comma_crt_mdd_node_ordered_branch_intro} OF
                      [root_bound,node_binding,axis_bound',positive',width',child_order]
                | _ => error "MDD ordered-row branch fact tuple changed shape")
                end
            end)
          val _ = if index mod 256 = 255 then checkpoint
            ("node-complete index=" ^ Int.toString index ^
             " selected_ms=" ^ elapsed_ms selected_elapsed ^
             " segment_ms=" ^ elapsed_ms segment_elapsed ^
             " bound_ms=" ^ elapsed_ms bound_elapsed ^
             " offset_ms=" ^ elapsed_ms offset_elapsed ^
             " ordered_ms=" ^ elapsed_ms ordered_elapsed) else ()
        in exact_closed expected theorem end
      val successors = Comma_Selected_List_Conversion.make_successor_cache ctxt count
      val _ = checkpoint "indexed-wellformedness-start"
      val all_nodes = Comma_Selected_List_Conversion.prove_indexed_list_all
        {ctxt=ctxt, predicate=predicate, bound=count, prove_item=prove_item,
         zero_fact= @{thm comma_indexed_all_zero},
         step_fact= @{thm comma_indexed_all_Suc}, successor_equation= #equation successors}
      val _ = checkpoint "indexed-wellformedness-complete"
      val wf_rule = Drule.infer_instantiate ctxt
        [( ("radices",0), Thm.cterm_of ctxt radix_term),
         ( ("nodes",0), Thm.cterm_of ctxt table)]
        @{thm comma_frontier24_table_wellformed_iff_list_all}
      val length_context = Comma_Entry_Arithmetic.natural_context ctxt
        |> Simplifier.add_simps [root_size]
      val normalized_rule = Simplifier.full_simplify length_context wf_rule
      val wellformed = @{thm iffD2} OF [normalized_rule, all_nodes]
      val expected_wf = HOLogic.mk_Trueprop
        (Const (@{const_name comma_crt_mdd_table_wellformed},
          @{typ "nat list"} --> nodesT --> @{typ bool}) $ radix_term $ table)
      val wellformed = exact_closed expected_wf wellformed
      val _ = checkpoint "native-audit-start"
      val _ = Comma_Proof_Dependency_Audit.require_native_clean ctxt
        "One frozen MDD arena wellformedness certificate" [wellformed]
      val _ = checkpoint "native-audit-complete"
      val bounds = Unsynchronized.ref (Inttab.empty: thm Inttab.table)
      fun bound index =
        (case Inttab.lookup (!bounds) index of
          SOME theorem => theorem
        | NONE =>
            let
              val expected = HOLogic.mk_Trueprop
                (HOLogic.mk_binrel @{const_name less} (nat index, length_term table))
              val theorem = exact_closed expected
                (Goal.prove ctxt [] [] expected (fn _ =>
                  Simplifier.asm_full_simp_tac length_context 1))
              val _ = bounds := Inttab.update (index,theorem) (!bounds)
            in theorem end)
      val phase_leaf_cache = Unsynchronized.ref (Inttab.empty: thm Inttab.table)
      val store = Store {arena=arena, ctxt=ctxt, table=table,
        radices=radix_term, count=count, nodes=node_views, wellformed=wellformed,
        lookup=lookup, bound=bound,
        phase_leaf_cache=phase_leaf_cache,
        statistics=fn () => "balanced_leaves=" ^ Int.toString leaf_count ^
          " balanced_appends=" ^ Int.toString
            (if leaf_count = 1 then 0 else leaf_count - 1) ^
          " row_selector=" ^ #stats row_selector () ^
          " chunk_selector=" ^ #stats chunk_selector () ^
          " lookup_selected_ms=" ^ elapsed_ms selected_elapsed ^
          " lookup_segment_ms=" ^ elapsed_ms segment_elapsed ^
          " lookup_bound_ms=" ^ elapsed_ms bound_elapsed ^
          " lookup_offset_ms=" ^ elapsed_ms offset_elapsed ^
          " ordered_item_ms=" ^ elapsed_ms ordered_elapsed ^
          " node_axis_equations=" ^ Int.toString (Inttab.size (!axis_cache)) ^
          " phase_leaf_certificates=" ^
            Int.toString (Inttab.size (!phase_leaf_cache))}
    in (store,lthy') end
end
