(* Checked publisher for Frontier24.  All ML
   values are candidates; only Store/Replay/Import theorems enter the final
   bundle certificate. *)
structure Comma_Frontier24_Bundle_Publisher =
struct
  structure Arena = Comma_CRT_MDD_Arena
  structure Store = Comma_CRT_MDD_Certificate_Store
  structure Operation = Comma_CRT_MDD_Operation_Replay
  structure Bind = Comma_CRT_MDD_Bind_Replay
  structure Import = Comma_Frontier24_MDD_Import_Certificates
  structure Compiler = Comma_Frontier24_Parametric_Compiler
  structure Runtime = Comma_Frontier24_Parametric_Runtime
  structure Selected_Table = Comma_Frontier24_Selected_Table_Plan
  structure Utils = Comma_CRT_MDD_Proof_Utils

  structure Shift_Request_Table = Table(
    type key = int * int * int
    val ord = fn ((a,b,c),(x,y,z)) =>
      prod_ord int_ord (prod_ord int_ord int_ord)
        ((a,(b,c)),(x,(y,z))))
  structure Bind_Key_Table = Table(
    type key = Arena.bind_key
    val ord = fn ((source,fallback,mapping),(source',fallback',mapping')) =>
      prod_ord int_ord (prod_ord int_ord
        (list_ord (prod_ord int_ord int_ord)))
        ((source,(fallback,mapping)),(source',(fallback',mapping'))))

  val natT = @{typ nat}
  val boolT = HOLogic.boolT
  val programT = @{typ comma_semantic_port_program}
  val selectorT = @{typ comma_frontier24_selector_recipe}
  val actionT = @{typ comma_source_continuation_action}
  val closureT = @{typ comma_frontier24_closure}
  val closure_caseT = @{typ comma_frontier24_closure_case}
  val bundleT = @{typ comma_frontier24_parametric_bundle}
  val nat_listT = HOLogic.listT natT
  val nat_pairT = HOLogic.mk_prodT (natT,natT)
  val nat_pair_listT = HOLogic.listT nat_pairT
  val shift_requestT = HOLogic.mk_prodT
    (natT,HOLogic.mk_prodT (natT,natT))
  val bind_requestT = HOLogic.mk_prodT
    (nat_pair_listT,HOLogic.mk_prodT (natT,HOLogic.mk_prodT (natT,natT)))

  fun nat n = HOLogic.mk_number natT n
  fun pair x y = HOLogic.mk_prod (x,y)
  fun list T xs = HOLogic.mk_list T xs
  fun unique_ints xs =
    map #1 (Inttab.dest (fold (fn index => Inttab.update (index,())) xs Inttab.empty))
  fun list_type T = Type (@{type_name list},[T])
  fun map_term domain range function values =
    Const (@{const_name map},(domain --> range) --> list_type domain --> list_type range)
      $ function $ values
  fun concat_term T values =
    Const (@{const_name concat},list_type (list_type T) --> list_type T) $ values
  fun const name T args =
    list_comb (Const (name,fold_rev (curry (op -->)) (map fastype_of args) T),args)

  fun bundle_pred name bundle =
    const name boolT [bundle]

  (* Consume the already proved finite core-parameter equations before the
     evaluator unfolds gcd.  This is a proof-rule index, not a memo: an input
     is accepted only when its normalized argument is one of the exact
     catalogue period numerals and an existing closed theorem has precisely
     the requested lhs.  Unsupported inputs fall through to the ordinary
     code evaluator. *)
  fun core_parameter_conversion_plan ctxt =
    let
      val scalar = Comma_Selected_List_Conversion.make_natural_normalizer ctxt
      val codec = Comma_Selected_List_Alias.make_codec
        {ctxt=ctxt,validate_equation=Comma_Selected_List_Conversion.validate_equation}
      val primary_name = @{const_name comma_core_primary}
      val modulus_name = @{const_name comma_core_modulus}
      val hits = Unsynchronized.ref 0
      fun is_parameter name term =
        (case strip_comb term of
          (Const (actual, _), [_]) => actual = name
        | _ => false)
      fun parameter_facts name =
        fold (fn theorem => fn table =>
          if Thm.nprems_of theorem <> 0 orelse not (null (Thm.hyps_of theorem)) orelse
              not (null (Thm.tpairs_of theorem)) then table
          else
            let
              val theorem = theorem RS @{thm eq_reflection}
              val lhs = Thm.term_of (Thm.lhs_of theorem)
              val rhs = Thm.term_of (Thm.rhs_of theorem)
              val _ = Utils.exact_prop ctxt "Closed core parameter fact"
                (Logic.mk_equals (lhs,rhs)) theorem
            in
              if is_parameter name lhs andalso
                  (case try HOLogic.dest_number rhs of
                    SOME (typ, value) => typ = natT andalso value >= 0
                  | NONE => false) then
                (case Termtab.lookup table lhs of
                  NONE => Termtab.update (lhs, theorem) table
                | SOME prior =>
                    if Thm.prop_of prior aconv Thm.prop_of theorem then table
                    else error "Core parameter theorem lhs has conflicting facts")
              else table
            end) @{thms comma_core_lift_parameters} Termtab.empty
      val primary_facts = parameter_facts primary_name
      val modulus_facts = parameter_facts modulus_name
      val _ = if not (Termtab.is_empty primary_facts) andalso
          not (Termtab.is_empty modulus_facts) then ()
        else error "Core parameter theorem collection is empty"
      fun canonical_nat term =
        (case try HOLogic.dest_number term of
          SOME (typ, value) => typ = natT andalso value >= 0
        | NONE => false)
      fun convert active_ctxt cterm =
        let
          val request = Thm.term_of cterm
          val (head, args) = strip_comb request
          val table = (case head of
              Const (name, _) =>
                if name = primary_name then SOME primary_facts
                else if name = modulus_name then SOME modulus_facts
                else NONE
            | _ => NONE)
        in if not (Utils.closed request) orelse Term.size_of_term request>512
        then NONE else
          case (args, table) of
            ([argument], SOME facts) =>
              let
                val normalized = #convert scalar active_ctxt
                  (Thm.cterm_of active_ctxt argument)
                val numeral = Thm.term_of (Thm.rhs_of normalized)
              in
                if not (canonical_nat numeral) then NONE
                else
                  let
                    val selected_lhs = head $ numeral
                  in
                    (case Termtab.lookup facts selected_lhs of
                      NONE => NONE
                    | SOME fact =>
                        let
                          val lifted = Thm.combination
                            (Thm.reflexive (Thm.cterm_of active_ctxt head)) normalized
                          val result = Thm.transitive lifted fact
                          val _ = Utils.exact_prop active_ctxt
                            "Frontier24 core parameter equation"
                            (Logic.mk_equals (request,
                              Thm.term_of (Thm.rhs_of fact))) result
                          val _ = hits := !hits + 1
                        in SOME (#encode_equation codec result) end)
                  end
              end
          | _ => NONE
        end
      val pattern_primary = Comma_Selected_List_Conversion.schematize
        @{term "comma_core_primary (p::nat)"}
      val pattern_modulus = Comma_Selected_List_Conversion.schematize
        @{term "comma_core_modulus (p::nat)"}
      val procedure = Simplifier.make_simproc ctxt
        {name="frontier24_exact_core_parameter_facts",kind=Simplifier.Congproc true,
         lhss=[pattern_primary,pattern_modulus],proc=fn _ => convert,identifier=[]}
    in {procedure=procedure,hits=fn () => !hits} end

  (* `Code_Simp.dynamic_conv` returns a kernel conversion theorem.  This is
     intentionally not `Code_Evaluation.dynamic_value`/`dynamic_holds_conv`. *)
  fun code_equation ctxt label request expected =
    let
      val conversion = Code_Simp.dynamic_conv ctxt (Thm.cterm_of ctxt request)
      val _ = Utils.exact_prop ctxt label (Logic.mk_equals (request,expected)) conversion
    in conversion end

  fun code_true ctxt label head facts procedures predicate =
    let
      val _ = if fastype_of predicate = boolT andalso Utils.closed predicate then ()
        else error (label ^ " is not a closed Boolean check")
      fun scalar_reflexivity T =
        Drule.infer_instantiate ctxt
          [(("x",0),Thm.cterm_of ctxt (Var (("scalar_value",0),T)))]
          @{thm equal_refl}
        |> Axclass.unoverload ctxt
      val literal_lists = Simplifier.make_simproc ctxt
        {name="frontier24_literal_list_constructor",kind=Simplifier.Congproc false,
         lhss=map Comma_Selected_List_Conversion.schematize
           [@{term "Cons (h::comma_semantic_port_program) t"},
            @{term "Cons (h::comma_frontier24_selector_recipe) t"},
            @{term "Cons (h::comma_frontier24_selector_case) t"},
            @{term "Cons (h::comma_frontier24_closure) t"}],
         proc=fn _ => fn context => fn ct => SOME
           (Conv.fun_conv (Conv.arg_conv (Simplifier.rewrite context)) ct),
         identifier=[]}
      val local_ctxt = Comma_Entry_Arithmetic.natural_context ctxt
        |> Simplifier.add_proc literal_lists
        |> Simplifier.add_cong @{thm conj_left_cong}
        |> Simplifier.add_cong @{thm disj_left_cong}
        |> Simplifier.add_cong @{thm bind_option_cong_code}
        |> Simplifier.add_cong @{thm comma_frontier24_list_all2_weak_cong}
        |> Simplifier.add_cong @{thm comma_frontier24_list_all_weak_cong}
        |> Simplifier.add_cong @{thm comma_frontier24_selector_recipe_weak_cong}
        |> Simplifier.add_cong @{thm comma_frontier24_selector_case_action_weak_cong}
        |> Simplifier.add_simp @{thm equal_refl}
        |> Simplifier.add_simps (map scalar_reflexivity [natT,@{typ integer}])
        |> Simplifier.add_simps facts
        |> fold (fn procedure => Simplifier.add_proc procedure) procedures
      val core_parameters = core_parameter_conversion_plan local_ctxt
      val local_ctxt = local_ctxt
        |> Simplifier.add_proc (#procedure core_parameters)
      val simpset = Simplifier.simpset_of local_ctxt
      val consts = Code_Thingol.read_const_exprs local_ctxt [head]
      val started = Time.now ()
      val evaluator = Code_Simp.static_conv
        {ctxt=local_ctxt,simpset=SOME simpset,
         consts=consts} local_ctxt
      val _ = if Comma_Proof_Profile.enabled () then
          Comma_Proof_Profile.report ("Frontier24 evaluator " ^ label ^
            " stage=prepared elapsed_ms=" ^ Comma_Proof_Profile.elapsed_ms started)
        else ()
      val evaluated = evaluator (Thm.cterm_of local_ctxt predicate)
      val _ = if Comma_Proof_Profile.enabled () then
          Comma_Proof_Profile.report
            ("Frontier24 core_parameter_rewrites=" ^
              Int.toString (#hits core_parameters ())) else ()
      (* Like Code_Simp.static_tac, conclude after its code postprocessor
         restores ordinary HOL operators. This cannot evaluate family code. *)
      val conclusion = Simplifier.rewrite
        (put_simpset HOL_basic_ss local_ctxt
          |> Simplifier.add_simps @{thms simp_thms}) (Thm.rhs_of evaluated)
      val conversion = Thm.transitive evaluated conclusion
      val right = Thm.term_of (Thm.rhs_of conversion)
      val _ = if right aconv @{term True} then ()
        else error (label ^ " did not reduce to True: " ^
          (if Term.size_of_term right <= 512
           then Syntax.string_of_term (Config.put show_types true local_ctxt) right
           else "residual head " ^ Syntax.string_of_term local_ctxt (Term.head_of right) ^
             ", nodes=" ^ Int.toString (Term.size_of_term right)) ^
          "\nConstants: " ^ commas (take 24 (Term.add_const_names right [])))
      val proof = conversion RS @{thm meta_eq_to_obj_eq} RS @{thm eqTrueE}
    in Utils.exact_prop local_ctxt label (HOLogic.mk_Trueprop predicate) proof end

  fun small_product_simpset ctxt =
    put_simpset HOL_basic_ss ctxt
    |> Simplifier.add_simps @{thms case_prod_unfold case_prod_beta
      case_prod_beta' prod.collapse
      comma_frontier24_closure.select_convs
      comma_frontier24_closure_case.select_convs
      comma_frontier24_parametric_bundle.select_convs}

  fun normalize_small_products_prop ctxt proposition =
    Thm.term_of (Thm.rhs_of (Simplifier.rewrite (small_product_simpset ctxt)
      (Thm.cterm_of ctxt proposition)))

  fun normalize_small_products ctxt theorem =
    let
      val conversion = Simplifier.rewrite (small_product_simpset ctxt)
        (Thm.cterm_of ctxt (Thm.prop_of theorem))
    in Thm.equal_elim conversion theorem end

  (* Transport a checked proposition through one exact equality without
     invoking the ambient theory simpset on its certificate or bundle terms. *)
  fun rewrite_rule_sterile ctxt rules theorem =
    Simplifier.rewrite_rule (put_simpset HOL_basic_ss ctxt) rules theorem

  fun profiled_stage stage work =
    if not (Comma_Proof_Profile.enabled ()) then work ()
    else
      let
        val owner = "Frontier24 publisher"
        val started = Time.now ()
        val _ = Comma_Proof_Profile.report
          (owner ^ " stage=" ^ stage ^ "-start")
        val result = Exn.capture work ()
        val status = (case result of Exn.Res _ => "ok" | Exn.Exn _ => "failed")
        val _ = Comma_Proof_Profile.report
          (owner ^ " stage=" ^ stage ^ "-complete status=" ^ status ^
            " elapsed_ms=" ^ Comma_Proof_Profile.elapsed_ms started)
      in Exn.release result end

  fun list_all_proof ctxt label elementT predicate elements element_facts =
    let
      val values = list elementT elements
      val prop = const @{const_name list_all} boolT
        [Term.lambda (Free ("cf24_item",elementT))
          (Term.betapply (predicate,Free ("cf24_item",elementT))), values]
      val expected = HOLogic.mk_Trueprop prop
      val ss = put_simpset HOL_basic_ss ctxt
        |> Simplifier.add_simps @{thms list_all_Cons_iff list_all_Nil_iff prod.collapse}
        |> Simplifier.add_simps element_facts
      val theorem = Utils.prove_exact ctxt label expected
        (fn _ => Simplifier.asm_full_simp_tac ss 1)
    in Utils.exact_prop ctxt label expected theorem end

  fun raw_shift_requests (result: Compiler.result) =
    maps (fn (closure: Compiler.closure) =>
      map (fn (row: Compiler.closure_case) =>
        (#full_shift closure,#guard_root row,#shifted_guard_root row))
        (#cases closure)) (Compiler.closures result)

  fun shift_requests raw =
    let
      val indexed = map_index (fn (index,key) => (index,key)) raw
      val latest = fold (fn (index,key) =>
        Shift_Request_Table.update (key,index)) indexed Shift_Request_Table.empty
    in map_filter (fn (index,key) =>
      if Shift_Request_Table.lookup latest key = SOME index then SOME key else NONE)
      indexed end

  fun raw_bind_requests (result: Compiler.result) =
    maps (fn (closure: Compiler.closure) =>
      map (fn (row: Compiler.closure_case) =>
        let val (source,fallback,mapping) = #bind_key row
        in (mapping,fallback,source,#selected_root row) end)
        (#cases closure)) (Compiler.closures result)

  fun bind_requests store (result: Compiler.result) raw =
    let
      val indexed = map_index (fn (index,(mapping,fallback,source,result_root)) =>
        (index,((source,fallback,mapping),result_root))) raw
      val latest = fold (fn (index,(key,result_root)) => fn table =>
        (case Bind_Key_Table.lookup table key of
          SOME (_,prior_root) =>
            if prior_root = result_root then
              Bind_Key_Table.update (key,(index,result_root)) table
            else error "One frozen bind key has inconsistent closure result roots"
        | NONE => Bind_Key_Table.update (key,(index,result_root)) table))
        indexed Bind_Key_Table.empty
      val keys = Compiler.bind_keys result
      val _ = if length keys = length (Bind_Key_Table.dest latest) then ()
        else error "Frontier24 interned bind keys disagree with closure requests"
      val ordered = fold (fn key as (source,fallback,mapping) =>
        let
          val (index,expected_root) = (case Bind_Key_Table.lookup latest key of
            SOME value => value
          | NONE => error "Frontier24 bind-key index is missing")
          val witness = Store.bind_witness store key
          val _ = if #result witness = expected_root then ()
            else error "Frontier24 bind result disagrees with the frozen arena witness"
          val request = (mapping,fallback,source,expected_root)
        in Inttab.update (index,request) end) keys Inttab.empty
      val _ = if length keys = Inttab.size ordered then ()
        else error "Frontier24 bind request order contains duplicate keys"
    in map #2 (Inttab.dest ordered) end

  fun shift_request_term (amount,source,target) =
    pair (nat amount) (pair (nat source) (nat target))

  fun bind_request_term (mapping,fallback,source,result) =
    pair (list nat_pairT (map (fn (label,root) => pair (nat label) (nat root)) mapping))
      (pair (nat fallback) (pair (nat source) (nat result)))

  fun raw_shift_request_term bundle =
    let
      val closures = Const (@{const_name cf24_closures},
        bundleT --> list_type closureT) $ bundle
      val closure = Free ("cf24_closure",closureT)
      val row = Free ("cf24_row",closure_caseT)
      val full_shift = Const (@{const_name cf24_closure_full_shift},closureT --> natT)
        $ closure
      val row_guard = Const (@{const_name cf24_closure_case_guard_root},
        closure_caseT --> natT) $ row
      val row_shifted = Const (@{const_name cf24_closure_case_shifted_guard_root},
        closure_caseT --> natT) $ row
      val item = pair full_shift (pair row_guard row_shifted)
      val rows = Const (@{const_name cf24_closure_cases},
        closureT --> list_type closure_caseT) $ closure
      val inner = map_term closure_caseT shift_requestT (Term.lambda row item) rows
      val outer = map_term closureT (list_type shift_requestT)
        (Term.lambda closure inner) closures
    in concat_term shift_requestT outer end

  fun raw_bind_request_term bundle =
    let
      val closures = Const (@{const_name cf24_closures},
        bundleT --> list_type closureT) $ bundle
      val closure = Free ("cf24_closure",closureT)
      val row = Free ("cf24_row",closure_caseT)
      val keyT = HOLogic.mk_prodT (natT,HOLogic.mk_prodT (natT,nat_pair_listT))
      val key = Const (@{const_name cf24_closure_case_bind_key},
        closure_caseT --> keyT) $ row
      val source = Const (@{const_name fst},keyT --> natT) $ key
      val tailT = HOLogic.mk_prodT (natT,nat_pair_listT)
      val tail = Const (@{const_name snd},keyT --> tailT) $ key
      val fallback = Const (@{const_name fst},tailT --> natT) $ tail
      val mapping = Const (@{const_name snd},tailT --> nat_pair_listT) $ tail
      val selected = Const (@{const_name cf24_closure_case_selected_root},
        closure_caseT --> natT) $ row
      val item = pair mapping (pair fallback (pair source selected))
      val rows = Const (@{const_name cf24_closure_cases},
        closureT --> list_type closure_caseT) $ closure
      val inner = map_term closure_caseT bind_requestT (Term.lambda row item) rows
      val outer = map_term closureT (list_type bind_requestT)
        (Term.lambda closure inner) closures
    in concat_term bind_requestT outer end

  fun raw_list_requests ctxt label elementT predicate raw_items unique_facts
      raw_function request_function request_definition bundle =
    let
      val raw_literal = list elementT raw_items
      val all_literal = list_all_proof ctxt (label ^ " raw request fold")
        elementT predicate raw_items unique_facts
      val raw_equation = code_equation ctxt (label ^ " raw request list")
        raw_function raw_literal
      val all_raw = rewrite_rule_sterile ctxt [Thm.symmetric raw_equation] all_literal
      val expected_raw = HOLogic.mk_Trueprop
        (const @{const_name list_all} boolT [predicate,raw_function])
      val all_raw = Utils.exact_prop ctxt (label ^ " raw request fold")
        expected_raw all_raw
      val remdups_raw = Const (@{const_name remdups},
        fastype_of raw_function --> fastype_of raw_function) $ raw_function
      val raw_all_term = const @{const_name list_all} boolT [predicate,raw_function]
      val remdups_all_term = const @{const_name list_all} boolT
        [predicate,remdups_raw]
      val ss = put_simpset HOL_basic_ss ctxt
        |> Simplifier.add_simps @{thms list_all_iff set_remdups}
      val remdups_equivalence = Utils.prove_exact ctxt
        (label ^ " list_all remdups quotient")
        (HOLogic.mk_Trueprop (HOLogic.mk_eq (remdups_all_term,raw_all_term)))
        (fn context => Simplifier.asm_full_simp_tac ss 1)
      val all_remdups = @{thm iffD2} OF [remdups_equivalence,all_raw]
      val request_def = Drule.infer_instantiate ctxt
        [(("bundle",0),Thm.cterm_of ctxt bundle)] request_definition
      val expected_def = normalize_small_products_prop ctxt
        (HOLogic.mk_Trueprop (HOLogic.mk_eq (request_function,remdups_raw)))
      val request_def = normalize_small_products ctxt request_def
      val request_def = Utils.exact_prop ctxt (label ^ " request definition")
        expected_def request_def
      val request_def_meta = request_def RS @{thm eq_reflection}
      val (request_lhs,request_rhs) = HOLogic.dest_eq
        (HOLogic.dest_Trueprop (Thm.prop_of request_def))
      val _ = Utils.exact_prop ctxt (label ^ " meta request definition")
        (Logic.mk_equals (request_lhs,request_rhs)) request_def_meta
      val all_requested = rewrite_rule_sterile ctxt [Thm.symmetric request_def_meta]
        all_remdups
      val expected = HOLogic.mk_Trueprop
        (const @{const_name list_all} boolT [predicate,request_function])
    in Utils.exact_prop ctxt (label ^ " deduplicated request fold") expected all_requested end

  fun shift_predicate store =
    let
      val triple = Free ("cf24_shift_request",shift_requestT)
      val fst_nat = Const (@{const_name fst},shift_requestT --> natT)
      val snd_pair = Const (@{const_name snd},shift_requestT -->
        HOLogic.mk_prodT (natT,natT)) $ triple
      val snd_fst = Const (@{const_name fst},HOLogic.mk_prodT (natT,natT) --> natT) $ snd_pair
      val snd_snd = Const (@{const_name snd},HOLogic.mk_prodT (natT,natT) --> natT) $ snd_pair
      val pred = const @{const_name comma_crt_mdd_root_shift_certificate} boolT
        [Store.radices store,Store.table store,
         fst_nat $ triple,snd_fst,snd_snd]
    in Term.lambda triple pred end

  fun bind_predicate store =
    let
      val request = Free ("cf24_bind_request",bind_requestT)
      val fst_map = Const (@{const_name fst},bind_requestT --> nat_pair_listT) $ request
      val tail1 = Const (@{const_name snd},bind_requestT -->
        HOLogic.mk_prodT (natT,HOLogic.mk_prodT (natT,natT))) $ request
      val fallback = Const (@{const_name fst},fastype_of tail1 --> natT) $ tail1
      val tail2 = Const (@{const_name snd},fastype_of tail1 -->
        HOLogic.mk_prodT (natT,natT)) $ tail1
      val source = Const (@{const_name fst},fastype_of tail2 --> natT) $ tail2
      val result = Const (@{const_name snd},fastype_of tail2 --> natT) $ tail2
      val pred = const @{const_name comma_crt_mdd_bind_certificate} boolT
        [Store.radices store,Store.table store,fst_map,fallback,source,result]
    in Term.lambda request pred end

  fun certify_shift_requests ctxt store replay requests raw_requests bundle =
    let
      val raw_items = map shift_request_term raw_requests
      val facts = map (fn (amount,source,target) =>
        let
          val theorem = Operation.certify_shift replay amount source target
          val item = shift_request_term (amount,source,target)
          val application = Term.betapply (shift_predicate store,item)
          val actual = HOLogic.dest_Trueprop (Thm.prop_of theorem)
          val conversion = Simplifier.rewrite
            (put_simpset HOL_basic_ss ctxt
              |> Simplifier.add_simps @{thms prod.collapse})
            (Thm.cterm_of ctxt application)
          val _ = Utils.exact_prop ctxt "Frontier24 shift tuple projections"
            (Logic.mk_equals (application,actual)) conversion
          val theorem = rewrite_rule_sterile ctxt [Thm.symmetric conversion] theorem
        in Utils.exact_prop ctxt "Frontier24 shift replay"
          (HOLogic.mk_Trueprop application) theorem end) requests
      val request_function = Const (@{const_name comma_frontier24_shift_requests},
        bundleT --> list_type shift_requestT) $ bundle
      val all_requested = raw_list_requests ctxt "Frontier24 shift"
        shift_requestT (shift_predicate store) raw_items facts
        (raw_shift_request_term bundle) request_function
        @{thm comma_frontier24_shift_requests_def} bundle
      val definition = Drule.infer_instantiate ctxt
        [(("bundle",0),Thm.cterm_of ctxt bundle)]
        @{thm comma_frontier24_shifts_certified_def}
      val expected_definition = normalize_small_products_prop ctxt
        (HOLogic.mk_Trueprop (HOLogic.mk_eq
        (bundle_pred @{const_name comma_frontier24_shifts_certified} bundle,
         const @{const_name list_all} boolT
           [shift_predicate store,request_function])))
      val definition = normalize_small_products ctxt definition
      val definition = Utils.exact_prop ctxt "Frontier24 shifts definition shape"
        expected_definition definition
      val certified = @{thm iffD2} OF [definition,all_requested]
      val expected = HOLogic.mk_Trueprop
        (bundle_pred @{const_name comma_frontier24_shifts_certified} bundle)
    in Utils.exact_prop ctxt "Frontier24 shifts certified" expected certified end

  fun certify_bind_requests ctxt store replay requests raw_requests bundle =
    let
      val raw_items = map bind_request_term raw_requests
      val pred = bind_predicate store
      val facts = map (fn (mapping,fallback,source,result_root) =>
        let
          val key = (source,fallback,mapping)
          val theorem = Bind.certify_bind replay key
          val item = bind_request_term (mapping,fallback,source,result_root)
          val application = Term.betapply (pred,item)
          val actual = HOLogic.dest_Trueprop (Thm.prop_of theorem)
          val conversion = Simplifier.rewrite
            (put_simpset HOL_basic_ss ctxt
              |> Simplifier.add_simps @{thms prod.collapse})
            (Thm.cterm_of ctxt application)
          val _ = Utils.exact_prop ctxt "Frontier24 bind tuple projections"
            (Logic.mk_equals (application,actual)) conversion
          val theorem = rewrite_rule_sterile ctxt [Thm.symmetric conversion] theorem
        in Utils.exact_prop ctxt "Frontier24 bind replay"
          (HOLogic.mk_Trueprop application) theorem end)
        requests
      val request_function = Const (@{const_name comma_frontier24_bind_requests},
        bundleT --> list_type bind_requestT) $ bundle
      val all_requested = raw_list_requests ctxt "Frontier24 bind"
        bind_requestT pred raw_items facts (raw_bind_request_term bundle)
        request_function @{thm comma_frontier24_bind_requests_def} bundle
      val definition = Drule.infer_instantiate ctxt
        [(("bundle",0),Thm.cterm_of ctxt bundle)]
        @{thm comma_frontier24_binds_certified_def}
      val expected_definition = normalize_small_products_prop ctxt
        (HOLogic.mk_Trueprop (HOLogic.mk_eq
        (bundle_pred @{const_name comma_frontier24_binds_certified} bundle,
         const @{const_name list_all} boolT [pred,request_function])))
      val definition = normalize_small_products ctxt definition
      val definition = Utils.exact_prop ctxt "Frontier24 binds definition shape"
        expected_definition definition
      val certified = @{thm iffD2} OF [definition,all_requested]
      val expected = HOLogic.mk_Trueprop
        (bundle_pred @{const_name comma_frontier24_binds_certified} bundle)
    in Utils.exact_prop ctxt "Frontier24 binds certified" expected certified end

  fun guard_import ctxt store arena (entry: Compiler.guard_entry) =
    let
      val core = #core entry
      val wanted = nat (#wanted entry)
      val nodes_request = const @{const_name comma_frontier24_core_guard_nodes}
        @{typ "bool comma_crt_mdd_node list"} [core,wanted]
      val nodes_equation = code_equation ctxt "Frontier24 guard source table"
        nodes_request (#source_nodes entry)
      val root_request = const @{const_name comma_frontier24_core_guard_root} natT [core]
      val root_equation = code_equation ctxt "Frontier24 guard source root"
        root_request (nat (#source_root entry))
      val import: Import.guard_import =
        {source_nodes= #source_nodes entry,source_root= #source_root entry,
         source_seeds= #source_seeds entry,
         arena_roots= #arena_roots entry,arena_nodes= #arena_nodes entry}
      val literal_map = Import.root_map_certificate store arena import
      val theorem = rewrite_rule_sterile ctxt
        [Thm.symmetric nodes_equation,Thm.symmetric root_equation] literal_map
      val encode = Abs ("value",@{typ bool},
        Const (@{const_name If},@{typ "bool => nat => nat => nat"}) $
          Bound 0 $ nat 1 $ nat 0)
      val source_function = const @{const_name comma_frontier24_core_guard_nodes}
        @{typ "bool comma_crt_mdd_node list"} [core,wanted]
      val source_root_function = const @{const_name comma_frontier24_core_guard_root}
        natT [core]
      val relation = const @{const_name comma_crt_mdd_root_map_certificate} boolT
        [list natT (map nat (Arena.radices arena)),source_function,Store.table store,encode,
         source_root_function,nat (#root entry)]
    in Utils.exact_prop ctxt "Frontier24 canonical guard root-map certificate"
      (HOLogic.mk_Trueprop relation) theorem end

  fun certify_guard_imports ctxt store arena result bundle =
    let
      val facts = map (guard_import ctxt store arena) (Compiler.guard_entries result)
      val predicate = bundle_pred @{const_name comma_frontier24_guard_imports_exact} bundle
      val target = HOLogic.mk_Trueprop predicate
      val ss = put_simpset HOL_basic_ss ctxt
        |> Simplifier.add_simps (@{thms comma_frontier24_guard_imports_exact_def
          comma_frontier24_parametric_bundle.select_convs
          comma_frontier24_guard_entry.select_convs
          list.simps set_simps ball_simps})
        |> Simplifier.add_simps facts
      val theorem = Utils.prove_exact ctxt "Frontier24 guard root maps" target
        (fn _ => Simplifier.asm_full_simp_tac ss 1)
    in Utils.exact_prop ctxt "Frontier24 exact guard import set" target theorem end

  fun referenced_roots (result: Compiler.result) =
    let
      fun case_roots (row: Compiler.closure_case) =
        let val (source,fallback,mapping) = #bind_key row
        in [#guard_root row,#shifted_guard_root row,#action_output_root row,
          #selected_root row,source,fallback] @ map #2 mapping end
      fun closure_roots (closure: Compiler.closure) =
        [#output_root closure] @ maps case_roots (#cases closure) @
        maps the_list
          [#near_action_output_root closure]
      fun selector_roots selector = (case selector of
          Compiler.Near_Selector _ => []
        | Compiler.Entry_Selector {cases,...} => map (fn row =>
            Arena.boolean_index (Compiler.arena result) (#guard_root row)) cases)
      val guard_roots = map #root (Compiler.guard_entries result)
      val class_roots = map (Arena.action_index (Compiler.arena result))
        (Compiler.class_roots result)
      val zero_root = Arena.action_index (Compiler.arena result)
        (Arena.action_none (Compiler.arena result))
    in unique_ints (zero_root::class_roots @ guard_roots @
      maps closure_roots (Compiler.closures result) @
      maps selector_roots (Compiler.selectors result)) end

  fun output_leaf_roots (result: Compiler.result) =
    let
      fun row_roots (row: Compiler.closure_case) = [#action_output_root row]
      fun closure_roots (closure: Compiler.closure) =
        maps row_roots (#cases closure) @
        the_list (#near_action_output_root closure)
      val zero_root = Arena.action_index (Compiler.arena result)
        (Arena.action_none (Compiler.arena result))
    in unique_ints (zero_root::maps closure_roots (Compiler.closures result)) end

  (* Memoize only closed locator equations in this one proof context.
     Equal output tokens do not identify equal locator requests. *)
  fun locator_conversion_plan ctxt =
    let
      val locator = @{term comma_entry_port_refined_locator}
      val resultT = @{typ "(nat * nat * nat) option"}
      val capacity = 4096
      val equations = Unsynchronized.ref (Termtab.empty: thm Termtab.table)
      val attempts = Unsynchronized.ref 0
      val rejected = Unsynchronized.ref 0
      val probes = Unsynchronized.ref 0
      val hits = Unsynchronized.ref 0
      val misses = Unsynchronized.ref 0
      val elapsed = Unsynchronized.ref Time.zeroTime
      val argument_elapsed = Unsynchronized.ref Time.zeroTime
      val scalar = Comma_Selected_List_Conversion.make_natural_normalizer ctxt
      val result_codec = Comma_Selected_List_Alias.make_codec
        {ctxt=ctxt,validate_equation=fn request => fn theorem =>
          Utils.exact_prop ctxt "Frontier24 locator representation equation"
            (Logic.mk_equals (request,Thm.term_of (Thm.rhs_of theorem))) theorem}
      fun canonical_nat t =
        (case try HOLogic.dest_number t of
          SOME (T,n) => T=natT andalso n>=0 andalso t aconv nat n
        | NONE => false)
      fun option_value t =
        (case strip_comb t of
          (Const (name,_),[]) => name = @{const_name None}
        | (Const (name,_),[triple]) =>
            name = @{const_name Some} andalso
            (let val (a,bc) = HOLogic.dest_prod triple
                 val (b,c) = HOLogic.dest_prod bc
             in forall canonical_nat [a,b,c] end)
        | _ => false)
        handle TERM _ => false
      fun validate request theorem =
        let
          val rhs = Thm.term_of (Thm.rhs_of theorem)
          val _ = if fastype_of rhs=resultT andalso
              Term.size_of_term rhs<=128 andalso option_value rhs then () else
            error ("Locator equation did not return a bounded closed option: " ^
              Syntax.string_of_term ctxt rhs)
        in Utils.exact_prop ctxt "Frontier24 locator equation"
          (Logic.mk_equals (request,rhs)) theorem end
      val base_ctxt = put_simpset HOL_basic_ss ctxt
        |> Simplifier.add_cong @{thm conj_left_cong}
        |> Simplifier.add_cong @{thm disj_left_cong}
        |> Simplifier.add_cong @{thm bind_option_cong_code}
      val prepared = Time.now ()
      val evaluator = Code_Simp.static_conv
        {ctxt=base_ctxt,simpset=SOME (Simplifier.simpset_of base_ctxt),
         consts=Code_Thingol.read_const_exprs base_ctxt
           [@{const_name comma_entry_port_refined_locator}]} base_ctxt
      val preparation_elapsed = Time.- (Time.now (),prepared)
      fun canonical_equation ct =
        let
          val request = Thm.term_of ct
          val _ = probes := !probes+1
        in case Termtab.lookup (!equations) request of
          SOME theorem => (hits := !hits+1; validate request theorem)
        | NONE =>
            let
              val _ = misses := !misses+1
              val _ = if Comma_Proof_Profile.enabled () then Comma_Proof_Profile.report
                  ("Frontier24 locator stage=miss-start misses=" ^ Int.toString (!misses) ^
                   " hits=" ^ Int.toString (!hits) ^ " elapsed_ms=" ^
                   LargeInt.toString (Time.toMilliseconds (!elapsed)) ^
                   " argument_ms=" ^
                   LargeInt.toString (Time.toMilliseconds (!argument_elapsed)) ^
                   " request=" ^ XML.content_of
                     (YXML.parse_body (Syntax.string_of_term ctxt request))) else ()
              val started = Time.now ()
              val outcome = Exn.capture (fn request_ct =>
                let
                  val raw = evaluator request_ct
                  val normalized = Simplifier.rewrite
                    (Comma_Entry_Arithmetic.natural_context ctxt) (Thm.rhs_of raw)
                in validate request (Thm.transitive raw normalized) end) ct
              val _ = elapsed := Time.+ (!elapsed,Time.- (Time.now (),started))
              val _ = if Comma_Proof_Profile.enabled () then
                Comma_Proof_Profile.report
                  ("Frontier24 locator stage=miss-complete misses=" ^
                   Int.toString (!misses) ^ " elapsed_ms=" ^
                   Comma_Proof_Profile.elapsed_ms started) else ()
              val theorem = Exn.release outcome
              val _ = if Termtab.size (!equations)<capacity then
                  equations := Termtab.update (request,theorem) (!equations)
                else ()
            in theorem end
        end
      fun reject () = (rejected := !rejected+1; NONE)
      fun convert code_output active_ctxt ct =
        let
          val _ = attempts := !attempts+1
          val request_size = Term.size_of_term (Thm.term_of ct)
          val _ = if Comma_Proof_Profile.enabled () andalso !attempts<=4 then
              Comma_Proof_Profile.report ("Frontier24 locator stage=request nodes=" ^
                Int.toString request_size) else ()
          val _ = if !attempts mod 256=1 then Comma_Proof_Profile.report
              ("Frontier24 locator stage=probe attempts=" ^ Int.toString (!attempts) ^
               " rejected=" ^ Int.toString (!rejected) ^
               " misses=" ^ Int.toString (!misses) ^
               " hits=" ^ Int.toString (!hits) ^
               " argument_ms=" ^
               LargeInt.toString (Time.toMilliseconds (!argument_elapsed)) ^
               " conversion_ms=" ^
               LargeInt.toString (Time.toMilliseconds (!elapsed))) else ()
        in
        if request_size>512 orelse
            not (Utils.closed (Thm.term_of ct)) then reject () else
        let
          val started = Time.now ()
          val argument = #convert scalar active_ctxt
          val normalized = Conv.combination_conv
            (Conv.combination_conv (Conv.arg_conv argument) argument) argument ct
          val (_,args) = strip_comb (Thm.term_of (Thm.rhs_of normalized))
          val _ = argument_elapsed := Time.+
            (!argument_elapsed,Time.- (Time.now (),started))
        in if length args=3 andalso forall canonical_nat args then
            let
              val exact = Thm.transitive normalized
                (canonical_equation (Thm.rhs_of normalized))
              val result = if code_output then
                  #encode_equation result_codec exact
                else Thm.transitive exact
                  (Axclass.unoverload_conv ctxt (Thm.rhs_of exact))
            in SOME result end
          else reject ()
        end
        end
      val pattern = list_comb (locator,
        map (fn name => Free (name,natT)) ["locator_f","locator_d","locator_eta"])
      fun make_procedure code_output = Simplifier.make_simproc ctxt
        {name=if code_output then "frontier24_locator_code_equation"
          else "frontier24_locator_equation",kind=Simplifier.Congproc true,
         lhss=[pattern],proc=fn _ => convert code_output,identifier=[]}
      val procedure = make_procedure false
      val code_procedure = make_procedure true
      fun statistics () =
        "locator_attempts=" ^ Int.toString (!attempts) ^
        " locator_rejected=" ^ Int.toString (!rejected) ^
        " locator_probes=" ^ Int.toString (!probes) ^
        " locator_hits=" ^ Int.toString (!hits) ^
        " locator_misses=" ^ Int.toString (!misses) ^
        " locator_retained=" ^ Int.toString (Termtab.size (!equations)) ^
        " locator_preparation_ms=" ^ LargeInt.toString
          (Time.toMilliseconds preparation_elapsed) ^
        " locator_argument_ms=" ^ LargeInt.toString
          (Time.toMilliseconds (!argument_elapsed)) ^
        " locator_conversion_ms=" ^ LargeInt.toString (Time.toMilliseconds (!elapsed))
    in {procedure=procedure,code_procedure=code_procedure,statistics=statistics} end

  fun certify_selector ctxt bundle procedures =
    let
      val locator = locator_conversion_plan ctxt
      val predicate = bundle_pred @{const_name comma_frontier24_selector_rows_checked} bundle
      (* Remove unrelated bundle fields before Code_Preproc traverses the
         evaluator input.  The kernel equation retains the original contract. *)
      val definition = Drule.infer_instantiate ctxt
        [(("bundle",0),Thm.cterm_of ctxt bundle)]
        @{thm comma_frontier24_selector_rows_checked_code}
        RS @{thm eq_reflection}
      val projection = Conv.top_sweep_rewrs_conv
        (map (fn theorem => theorem RS @{thm eq_reflection})
          @{thms comma_frontier24_parametric_bundle.select_convs}) ctxt
        (Thm.rhs_of definition)
      val reduced = Thm.transitive definition projection
      val selected = Thm.term_of (Thm.rhs_of reduced)
      val outcome = Exn.capture (fn () => profiled_stage "selector_rows" (fn () =>
        code_true ctxt "Frontier24 selector rows"
          @{const_name comma_frontier24_selector_rows_checked} []
          (#code_procedure locator::procedures) selected)) ()
      val _ = Comma_Proof_Profile.report
        ("Frontier24 selector " ^ #statistics locator ())
      val theorem = @{thm iffD2} OF
        [reduced RS @{thm meta_eq_to_obj_eq},Exn.release outcome]
      val expected = HOLogic.mk_Trueprop predicate
    in Utils.exact_prop ctxt "Frontier24 checked selector table" expected theorem end

  fun selector_transport ctxt bundle selector
      (programs_plan: Selected_Table.plan) (selectors_plan: Selected_Table.plan)
      (actions_plan: Selected_Table.plan) =
    let
      val expected = HOLogic.mk_Trueprop
        (bundle_pred @{const_name comma_frontier24_selector_rows_checked} bundle)
      val selector = Utils.exact_prop ctxt "Selector transport authority" expected selector
      val raw_rule = (@{thm comma_frontier24_selector_rows_checkedD} OF [selector])
        RS @{thm eqTrueI} RS @{thm eq_reflection}
      val rule = (case #transport_equation actions_plan of
          NONE => raw_rule
        | SOME equation => rewrite_rule_sterile ctxt [equation] raw_rule)
      val pattern = #1 (Logic.dest_equals (Thm.concl_of rule))
      val pattern_ct = Thm.cterm_of ctxt pattern
      val hits = Unsynchronized.ref 0
      fun canonical_argument plan argument =
        #canonicalize (plan: Selected_Table.plan) (Thm.cterm_of ctxt argument)
      fun rewrite request =
        let
          val request_term = Thm.term_of request
          val (head,arguments) = strip_comb request_term
        in if not (Utils.closed request_term) then NONE else
          case (head,arguments) of
            (Const (name,_),[program,recipe,actions]) =>
              if name <> @{const_name comma_frontier24_selector_recipe_matches}
              then NONE else
              (case (canonical_argument programs_plan program,
                     canonical_argument selectors_plan recipe,
                     canonical_argument actions_plan actions) of
                (SOME program_eq,SOME recipe_eq,SOME actions_eq) =>
                  let
                    val canonical = fold (fn argument => fn function =>
                      Thm.combination function argument)
                      [program_eq,recipe_eq,actions_eq]
                      (Thm.reflexive (Thm.cterm_of ctxt head))
                    val equation = Thm.instantiate
                      (Thm.match (pattern_ct,Thm.rhs_of canonical)) rule
                    val index = #2 (dest_comb program)
                    val programs = const @{const_name cf24_programs}
                      (HOLogic.listT programT) [bundle]
                    val bound = HOLogic.mk_Trueprop (HOLogic.mk_binrel @{const_name less}
                      (index,const @{const_name size} natT [programs]))
                    val _ = if Thm.concl_of equation aconv
                          Logic.mk_equals (Thm.term_of (Thm.rhs_of canonical),@{term True})
                        andalso Thm.prems_of equation=[bound]
                        andalso null (Thm.hyps_of equation)
                        andalso null (Thm.tpairs_of equation) then () else
                      error "Selector transport changed its indexed bound or result"
                    val bound_ct = Thm.cterm_of ctxt bound
                    val point = Thm.implies_elim equation (Thm.assume bound_ct)
                    val exact = Thm.implies_intr bound_ct
                      (Thm.transitive canonical point)
                    val _ = if Thm.concl_of exact aconv
                        Logic.mk_equals (request_term,@{term True}) andalso
                        Thm.prems_of exact=[bound] andalso
                        null (Thm.hyps_of exact) andalso
                        null (Thm.tpairs_of exact) then () else
                      error "Selector transport changed the original request"
                    val _ = hits := !hits+1
                  in SOME exact end
              | _ => NONE)
          | _ => NONE
        end
        handle Pattern.MATCH => NONE
      val dispatch = @{term "comma_frontier24_selector_recipe_matches
        selector_program selector_recipe selector_actions"}
      val procedure = Simplifier.make_simproc ctxt
        {name="frontier24_checked_selector_transport",kind=Simplifier.Congproc true,
         lhss=[dispatch],proc=fn _ => fn _ => rewrite,identifier=[]}
    in {procedure=procedure,hits=fn () => !hits} end

  fun certify ctxt store arena operation_replay bind_replay
      (candidate: Runtime.candidate) =
    let
      val result = #result candidate
      val bundle = #bundle candidate
      val _ = Comma_Proof_Profile.report
        ("Frontier24 publisher candidate " ^ Runtime.statistics candidate)
      val root_indices = referenced_roots result
      val output_indices = output_leaf_roots result
      val bound_facts = map (Store.bound store) root_indices
      val lookup_facts = map (Store.lookup store) output_indices
      val lookup_plans =
        [Selected_Table.make ctxt bundle "programs" @{const_name cf24_programs}
          programT (length (Compiler.programs result))
          (SOME (Compiler.programs result)),
         Selected_Table.make ctxt bundle "selectors" @{const_name cf24_selectors}
          selectorT (length (Compiler.selectors result)) NONE,
         Selected_Table.make_named ctxt bundle "actions" @{const_name cf24_action_tokens}
          actionT (length (Compiler.action_tokens result))
          (#named_actions candidate) (Compiler.action_tokens result),
         Selected_Table.make ctxt bundle "closures" @{const_name cf24_closures}
          closureT (length (Compiler.closures result)) NONE]
      val lookup_procedures = maps Selected_Table.procedures lookup_plans
      val selector_outcome = Exn.capture (fn () => profiled_stage "selector" (fn () =>
        certify_selector ctxt bundle lookup_procedures)) ()
      val _ = Comma_Proof_Profile.report
        ("Frontier24 selector lookups " ^
          String.concatWith " " (map Selected_Table.statistics lookup_plans))
      val selector = Exn.release selector_outcome
      val transport = (case lookup_plans of
          [programs,selectors,actions,_] =>
            selector_transport ctxt bundle selector programs selectors actions
        | _ => error "Selector transport requires its three exact table owners")
      val structural_procedures = #procedure transport::lookup_procedures
      val structural = profiled_stage "structural" (fn () =>
        code_true ctxt "Frontier24 checked closure structure"
          @{const_name comma_frontier24_bundle_semantic_structure_checked}
          (selector::bound_facts @ lookup_facts) structural_procedures
          (bundle_pred @{const_name comma_frontier24_bundle_semantic_structure_checked} bundle))
      val _ = Comma_Proof_Profile.report
        ("Frontier24 selector_transports=" ^ Int.toString (#hits transport ()))
      val guard_imports = profiled_stage "guard_imports" (fn () =>
        certify_guard_imports ctxt store arena result bundle)
      val (shifts_requested,shifts) =
        profiled_stage "shift_requests" (fn () =>
          let
            val raw = raw_shift_requests result
            val requested = shift_requests raw
            val theorem = certify_shift_requests ctxt store operation_replay
              requested raw bundle
          in (requested,theorem) end)
      val (binds_requested,binds) =
        profiled_stage "bind_requests" (fn () =>
          let
            val raw = raw_bind_requests result
            val requested = bind_requests store result raw
            val theorem = certify_bind_requests ctxt store bind_replay
              requested raw bundle
          in (requested,theorem) end)
      val theorem = profiled_stage "final_assembly" (fn () =>
        let
          val table = Store.wellformed store
          val expected_table = HOLogic.mk_Trueprop
            (const @{const_name comma_crt_mdd_table_wellformed} boolT
              [Store.radices store,Store.table store])
          val table = Utils.exact_prop ctxt "Frontier24 frozen table" expected_table table
          val components = [table,structural,guard_imports,shifts,binds]
          val expected = HOLogic.mk_Trueprop
            (bundle_pred @{const_name comma_frontier24_bundle_semantic_certified} bundle)
          val simp = put_simpset HOL_basic_ss ctxt
            |> Simplifier.add_simps [@{thm comma_frontier24_bundle_semantic_certified_def}]
            |> Simplifier.add_simps
              @{thms comma_frontier24_parametric_bundle.select_convs}
            |> Simplifier.add_simps components
          val theorem = Utils.prove_exact ctxt "Frontier24 certified bundle" expected
            (fn _ => Simplifier.asm_full_simp_tac simp 1)
        in Utils.exact_prop ctxt "Frontier24 certified bundle" expected theorem end)
      val statistics = Store.statistics store ^ " " ^
        Operation.statistics operation_replay ^ " " ^ Bind.statistics bind_replay ^
        " guard_root_maps=" ^ Int.toString (length (Compiler.guard_entries result)) ^
        " shift_requests=" ^ Int.toString (length shifts_requested) ^
        " bind_requests=" ^ Int.toString (length binds_requested) ^
        " referenced_roots=" ^ Int.toString (length root_indices) ^
        " output_rows=" ^ Int.toString (length output_indices) ^ " " ^
        String.concatWith " " (map Selected_Table.statistics lookup_plans)
    in {theorem=theorem,statistics=statistics} end
end
