structure Comma_Semantic_Continue_Column_Proofs =
struct
  val natT = @{typ nat}
  val columnT = @{typ comma_crt_column}

  val natural_zero_name = Axclass.unoverload_const @{theory}
    (@{const_name Groups.zero_class.zero},natT)

  fun natural_value term =
    (case try HOLogic.dest_number term of
      SOME (typ,n) => if typ=natT andalso n>=0 then SOME n else NONE
    | NONE =>
        (case Term.strip_comb term of
          (Const (name,typ),[]) =>
            if name=natural_zero_name andalso typ=natT then SOME 0 else NONE
        | (Const (name,_),[previous]) =>
            if name = @{const_name Suc} then
              Option.map (fn n => n+1) (natural_value previous)
            else NONE
        | _ => NONE))

  fun core_guard_context ctxt = ctxt
    |> Simplifier.add_simps @{thms comma_core_value_guard.simps
      comma_core_value_guard_one_axis_def comma_core_value_guard_two_axes_def
      comma_core_value_guard_leaf_def comma_core_guard_clock_def
      comma_crt_period_def list.map}

  (* Keep a map's function opaque until its concrete list head is supplied.
     Normalizing the lambda first expands recursive Apply with a free digit. *)
  val map_list_argument_cong =
    @{lemma "xs = ys \<Longrightarrow> map f xs = map f ys" by (rule arg_cong)}

  val shift_column_argument_cong =
    @{lemma "xs = ys \<Longrightarrow> comma_crt_shift amount xs =
      comma_crt_shift amount ys" by (rule arg_cong)}

  val let_bound_argument_cong =
    @{lemma "x = y \<Longrightarrow> Let x f = Let y f" by (rule arg_cong)}

  (* Code preprocessing replaces HOL equality with the datatype's overloaded
     comparator.  Share reflexivity before that comparator descends into two
     identical trees.  This equation is total; it grants no column admission. *)
  fun column_reflexivity_proc ctxt =
    let
      val equation = Axclass.unoverload ctxt (mk_meta_eq
        @{lemma "HOL.equal (column::comma_crt_column) column = True"
          by (simp add: equal_eq)})
      val pattern = Thm.term_of (Thm.lhs_of equation)
      fun rewrite ct =
        (case Term.strip_comb (Thm.term_of ct) of
          (_, [left,right]) =>
            if left aconv right then SOME (Conv.rewr_conv equation ct) else NONE
        | _ => NONE)
    in
      Simplifier.make_simproc ctxt
        {name="comma_crt_column_reflexivity",kind=Simplifier.Congproc true,
         lhss=[pattern],proc=fn _ => fn _ => rewrite,identifier=[]}
    end

  fun column_clock_mod_proc ctxt =
    let
      val pattern=Thm.term_of (Thm.lhs_of (Axclass.unoverload ctxt
        (mk_meta_eq @{lemma "(n::nat) mod d = n mod d" by (rule refl)})))
      val arithmetic=Comma_Entry_Arithmetic.natural_context ctxt
        |> Simplifier.add_simps @{thms list.size length_map}
      fun rewrite ct =
        let val input=Thm.term_of ct in
          if Term.is_open input orelse not (null (Term.add_frees input []))
              orelse not (null (Term.add_vars input [])) then NONE
          else
            let
              val overloaded=Axclass.overload_conv ctxt ct
              val reduced=Simplifier.rewrite arithmetic (Thm.rhs_of overloaded)
              val result=Thm.term_of (Thm.rhs_of reduced)
            in
              case try HOLogic.dest_number result of
                SOME (typ,_) => if typ=natT then
                  SOME (Thm.transitive overloaded
                    (Thm.transitive reduced
                      (Axclass.unoverload_conv ctxt (Thm.rhs_of reduced))))
                  else NONE
              | NONE => NONE
            end
        end
    in
      Simplifier.make_simproc ctxt
        {name="comma_crt_closed_clock_mod",kind=Simplifier.Congproc true,
         lhss=[pattern],proc=fn _ => fn _ => rewrite,identifier=[]}
    end

  fun profile_stage label action =
    if not (Comma_Proof_Profile.enabled ()) then action ()
    else
      let
        val started=Time.now ()
        val result=action ()
        val elapsed=Time.toMilliseconds (Time.- (Time.now (),started))
        (* Publisher checkpoints retain aggregate progress. Per-node zero-time
           messages can themselves exhaust the guarded output allowance. *)
        val _=if elapsed<10 then () else
          Comma_Proof_Profile.report ("Continue builder stage=done label=" ^ label ^
            " elapsed_ms=" ^ LargeInt.toString elapsed)
      in result end

  fun dest_constructor label term =
    (case Term.strip_comb term of
      (Const (name,_),arguments) => (name,arguments)
    | _ => error (label ^ " is not a constructor application"))

  fun dest_nat label term =
    (case try HOLogic.dest_number term of
      SOME (typ,value) =>
        if typ=natT andalso value>=0 then value
        else error (label ^ " is not a natural numeral")
    | NONE => error (label ^ " is not a natural numeral"))

  fun dest_list label term =
    (HOLogic.dest_list term
      handle TERM _ => error (label ^ " is not a literal list"))

  fun bounded_term_size limit term =
    let
      fun visit count current =
        if count > limit then count
        else case current of
          f $ x => visit (visit (count+1) f) x
        | Abs (_,_,body) => visit (count+1) body
        | _ => count+1
    in visit 0 term <= limit end

  fun bool_result label theorem =
    let val result=Thm.term_of (Thm.rhs_of theorem) in
      if result aconv @{term True} then true
      else if result aconv @{term False} then false
      else error (label ^ " did not reduce to True or False: " ^
        (if Term.size_of_term result <= 100 then
           Syntax.string_of_term_global (Thm.theory_of_thm theorem) result
         else "residual term nodes=" ^ Int.toString (Term.size_of_term result)))
    end

  fun scalar_from_facts ctxt validate_native label term rules =
    let
      val context=Comma_Entry_Arithmetic.signed_context ctxt
        |> Simplifier.add_simps rules
      val theorem=profile_stage label
        (fn () => Simplifier.rewrite context (Thm.cterm_of ctxt term))
      val _=if Thm.term_of (Thm.lhs_of theorem) aconv term then ()
        else error (label ^ " changed its scalar input")
      val theorem=validate_native label theorem
    in (bool_result label theorem,Thm.term_of (Thm.rhs_of theorem),theorem) end

  fun checked_rhs validate_equation label term theorem =
    let
      val rhs=Thm.term_of (Thm.rhs_of theorem)
      val theorem=validate_equation label term rhs theorem
    in (rhs,theorem) end

  fun column_shape natural column =
    (case Term.strip_comb column of
      (Const (name,_),[bit]) => name = @{const_name Comma_CRT_Bool}
        andalso (bit aconv @{term True} orelse bit aconv @{term False})
    | (Const (name,_),[level,children]) =>
        name = @{const_name Comma_CRT_Node} andalso
        natural level andalso
        (case try HOLogic.dest_list children of
          SOME values => List.all (column_shape natural) values | NONE => false)
    | _ => false)

  val is_literal_column = column_shape (is_some o try HOLogic.dest_number)

  (* Certify a literal clock transport before code evaluation can expand the
     numeric clock or normalize a partially applied recursive mapper. *)
  fun column_shift_proc ctxt =
    let
      val pattern=Thm.term_of (Thm.lhs_of (mk_meta_eq
        @{lemma "comma_crt_shift amount column = comma_crt_shift amount column"
          by (rule refl)}))
      val arithmetic=Comma_Entry_Arithmetic.natural_context ctxt
        |> Simplifier.del_simps @{thms comma_crt_shift.simps}
        |> Simplifier.add_simps @{thms comma_crt_shift.simps(1)
          comma_crt_shift_node_bounded_rotation list.map list.size
          drop.simps take.simps append.simps nat.case case_nat_numeral pred_numeral_simps}
        |> Simplifier.add_simp
          @{lemma "case_nat x f 1 = f 0" by (simp add: One_nat_def)}
        |> fold Simplifier.add_cong
          [map_list_argument_cong,shift_column_argument_cong,let_bound_argument_cong]
      fun rewrite ct =
        let
          val overloaded=Axclass.overload_conv ctxt ct
          val numerals=Simplifier.rewrite
            (Comma_Entry_Arithmetic.numeral_context ctxt
              |> Simplifier.add_simps @{thms nat_of_num_numeral})
            (Thm.rhs_of overloaded)
          val prepared=Thm.transitive overloaded numerals
          val input=Thm.rhs_of prepared
        in
          case Term.strip_comb (Thm.term_of input) of
            (_, [amount,column]) =>
              if is_some (try HOLogic.dest_number amount) andalso
                  is_literal_column column then
                let
                  val proof=Simplifier.rewrite arithmetic input
                in SOME (Thm.transitive prepared
                  (Thm.transitive proof
                    (Axclass.unoverload_conv ctxt (Thm.rhs_of proof)))) end
              else NONE
          | _ => NONE
        end
    in
      Simplifier.make_simproc ctxt
        {name="comma_crt_literal_clock_transport",kind=Simplifier.Congproc true,
         lhss=[pattern],proc=fn _ => fn _ => rewrite,identifier=[]}
    end

  fun column_code_context ctxt proc =
    put_simpset HOL_basic_ss ctxt
    |> fold Simplifier.add_cong
      (@{thms conj_left_cong disj_left_cong bind_option_cong_code} @
        [map_list_argument_cong,shift_column_argument_cong,let_bound_argument_cong])
    |> Simplifier.add_proc (column_reflexivity_proc ctxt)
    |> Simplifier.add_proc (column_clock_mod_proc ctxt)
    |> Simplifier.add_proc (column_shift_proc ctxt)
    |> Simplifier.add_proc proc

  fun is_core_value_guard term =
    let
      val core_names = [@{const_name Comma_Core_1},@{const_name Comma_Core_3},
        @{const_name Comma_Core_7},@{const_name Comma_Core_11},
        @{const_name Comma_Core_13},@{const_name Comma_Core_21},
        @{const_name Comma_Core_23},@{const_name Comma_Core_27},
        @{const_name Comma_Core_29}]
      fun natural input =
        (case try HOLogic.dest_number input of
          SOME (typ,n) => typ=natT andalso n>=0 | NONE => false)
    in
      case Term.strip_comb term of
        (Const (name,_),[core,wanted]) =>
          name = @{const_name comma_core_value_guard} andalso
          (case core of Const (core_name,_) => member (op =) core_names core_name
            | _ => false) andalso natural wanted
      | _ => false
    end

  (* Only retain equations for the small CRT operations produced by the
     observer fold.  The node limit is a retention bound, not an execution or
     semantic limit; larger requests still take the ordinary conversion path. *)
  fun shallow_column_operation term =
    let
      fun natural input =
        (case try HOLogic.dest_number input of
          SOME (typ,n) => typ=natT andalso n>=0 | NONE => false)
      fun leaf input =
        if is_literal_column input orelse is_core_value_guard input then true
        else case Term.strip_comb input of
          (Const (name,_),[offset,column]) =>
            name = @{const_name comma_crt_shift} andalso natural offset andalso
              (is_literal_column column orelse is_core_value_guard column)
        | _ => false
      fun operation apply_depth input =
        if leaf input then true
        else case Term.strip_comb input of
          (Const (name,_),[operator,left,right]) =>
            name = @{const_name comma_crt_apply} andalso apply_depth < 2 andalso
            (case operator of
              Const (op_name,_) =>
                (op_name = @{const_name Comma_CRT_And} orelse
                 op_name = @{const_name Comma_CRT_Or})
            | _ => false) andalso
            operation (apply_depth+1) left andalso
            operation (apply_depth+1) right
        | (Const (name,_),[column]) =>
            name = @{const_name comma_crt_negate} andalso
              (is_literal_column column orelse
               (case Term.strip_comb column of
                 (Const (shift_name,_),[offset,child]) =>
                   shift_name = @{const_name comma_crt_shift} andalso
                   natural offset andalso
                   (is_literal_column child orelse is_core_value_guard child)
               | _ => false))
        | _ => false
    in
      fastype_of term = columnT andalso bounded_term_size 4096 term andalso
        not (is_literal_column term) andalso operation 0 term
    end

  fun dead_false_guarded_or_tail term =
    let
      fun shifted_guard input =
        (case Term.strip_comb input of
          (Const (name,_),[offset,_]) =>
            name = @{const_name comma_crt_shift} andalso
            (case try HOLogic.dest_number offset of
              SOME (typ,n) => typ=natT andalso n>=0 | NONE => false)
        | _ => false)
      val false_column = @{term "Comma_CRT_Bool False"}
    in
      if not (shallow_column_operation term) then NONE
      else
        (case Term.strip_comb term of
          (Const (outer,_),[operator,left,tail]) =>
            if outer = @{const_name comma_crt_apply} andalso
                operator aconv @{term Comma_CRT_Or} andalso
                is_literal_column tail then
              (case Term.strip_comb left of
                (Const (inner,_),[inner_operator,guard,right]) =>
                  if inner = @{const_name comma_crt_apply} andalso
                      inner_operator aconv @{term Comma_CRT_And} andalso
                      shifted_guard guard andalso right aconv false_column
                  then SOME tail else NONE
              | _ => NONE)
            else NONE
        | _ => NONE)
    end

  fun shallow_column_guard_leaves term =
    if not (shallow_column_operation term) then []
    else
      let
        fun add_unique candidate found =
          if exists (fn previous => previous aconv candidate) found then found
          else found @ [candidate]
        fun visit current found =
          if is_literal_column current then found
          else if is_core_value_guard current then
            if current aconv term then found else add_unique current found
          else
            (case Term.strip_comb current of
              (Const (name,_),[_,child]) =>
                  if name = @{const_name comma_crt_shift} then
                    if is_core_value_guard child then
                      if current aconv term then visit child found
                      else add_unique current found
                    else found
                  else found
            | (Const (name,_),[_,left,right]) =>
                  if name = @{const_name comma_crt_apply} then
                    visit right (visit left found) else found
            | (Const (name,_),[child]) =>
                  if name = @{const_name comma_crt_negate} then
                    visit child found else found
            | _ => found)
        val leaves=visit term []
      in leaves end

  fun require_literal_column label column =
    if is_literal_column column then ()
      else error (label ^ " retains unevaluated column operations: " ^
        commas (sort_distinct fast_string_ord (Term.add_const_names column [])))

  fun application_admitted ctxt validate_native operator_contract observer_admitted
      operator observer program =
    let
      val lhs=operator $ observer $ program $ HOLogic.mk_number natT 0
      val proposition = @{term comma_crt_admitted} $
        HOLogic.mk_number natT 0 $ lhs
      val admitted_rule= @{thm comma_continue_operator_contract_admitted} OF
        [operator_contract,observer_admitted]
      val theorem=Goal.prove ctxt [] [] (HOLogic.mk_Trueprop proposition)
        (fn {context,...} => resolve_tac context [admitted_rule] 1)
    in validate_native "Continue output admission" theorem end

  fun checked_proposition validate_native label expected theorem =
    if Thm.prop_of theorem aconv expected then validate_native label theorem
    else error (label ^ " proves a different proposition")

  fun admitted_proposition column =
    HOLogic.mk_Trueprop (@{term comma_crt_admitted} $
      HOLogic.mk_number natT 0 $ column)

  fun transport_admission ctxt validate_native label conversion input output admitted =
    let
      val _=checked_proposition validate_native (label ^ " equation")
        (Logic.mk_equals (input,output)) conversion
      val _=checked_proposition validate_native (label ^ " input admission")
        (admitted_proposition input) admitted
      val predicate= @{term comma_crt_admitted} $ HOLogic.mk_number natT 0
      val relation=Thm.combination
        (Thm.reflexive (Thm.cterm_of ctxt predicate)) conversion
      val proposition=Thm.combination
        (Thm.reflexive (Thm.cterm_of ctxt
          (Const (@{const_name Trueprop},HOLogic.boolT --> propT)))) relation
      val theorem=Thm.equal_elim proposition admitted
    in checked_proposition validate_native label
      (admitted_proposition output) theorem end

  (* Transport the exact root equation through the relation constructor. This
     neither traverses a child proof nor searches for equality of column sets. *)
  fun transport_equivalence ctxt validate_native label conversion actual middle
      canonical congruence =
    let
      val _=checked_proposition validate_native (label ^ " root equation")
        (Logic.mk_equals (actual,middle)) conversion
      val _=checked_proposition validate_native (label ^ " child equivalence")
        (HOLogic.mk_Trueprop
          (@{term comma_crt_equiv_check} $ middle $ canonical)) congruence
      val head=Thm.combination
        (Thm.reflexive (Thm.cterm_of ctxt @{term comma_crt_equiv_check})) conversion
      val relation=Thm.combination head
        (Thm.reflexive (Thm.cterm_of ctxt canonical))
      val proposition=Thm.combination
        (Thm.reflexive (Thm.cterm_of ctxt
          (Const (@{const_name Trueprop},HOLogic.boolT --> propT)))) relation
      val theorem=Thm.equal_elim (Thm.symmetric proposition) congruence
    in checked_proposition validate_native label
      (HOLogic.mk_Trueprop
        (@{term comma_crt_equiv_check} $ actual $ canonical)) theorem end

  fun equation_to_equiv ctxt validate_native label equation left right
      left_admitted right_admitted =
    let
      val _=checked_proposition validate_native (label ^ " left admission")
        (admitted_proposition left) left_admitted
      val _=checked_proposition validate_native (label ^ " right admission")
        (admitted_proposition right) right_admitted
      val reflexive= @{thm comma_crt_equiv_check_refl} OF [right_admitted]
    in transport_equivalence ctxt validate_native label equation left right right
      reflexive end

  fun canonicalize_column ctxt validate_native scalar label raw raw_admitted =
    let
      val conversion=scalar label raw
      val canonical=Thm.term_of (Thm.rhs_of conversion)
      val _=require_literal_column label canonical
      val canonical_admitted=transport_admission ctxt validate_native
        (label ^ " admission") conversion raw canonical raw_admitted
      val equivalent=equation_to_equiv ctxt validate_native
        (label ^ " canonicalization") conversion raw canonical
        raw_admitted canonical_admitted
    in (canonical,canonical_admitted,equivalent,conversion) end

  fun trans_equiv ctxt validate_native label left middle right first second =
    let
      val first_expected=HOLogic.mk_Trueprop
        (@{term comma_crt_equiv_check} $ left $ middle)
      val second_expected=HOLogic.mk_Trueprop
        (@{term comma_crt_equiv_check} $ middle $ right)
      val _=if Thm.prop_of first aconv first_expected andalso
          Thm.prop_of second aconv second_expected then ()
        else error (label ^ " has mismatched child equivalence authority")
      val theorem=Goal.prove ctxt [] []
        (HOLogic.mk_Trueprop (@{term comma_crt_equiv_check} $ left $ right))
        (fn {context,...} =>
          resolve_tac context [@{thm comma_crt_equiv_check_trans}] 1
          THEN resolve_tac context [first] 1
          THEN resolve_tac context [second] 1)
    in validate_native label theorem end

  fun apply_equiv ctxt validate_native label operation left right left' right'
      left_equiv right_equiv =
    let
      val theorem=Goal.prove ctxt [] []
        (HOLogic.mk_Trueprop
          (@{term comma_crt_equiv_check} $
            (@{term comma_crt_apply} $ operation $ left $ right) $
            (@{term comma_crt_apply} $ operation $ left' $ right')))
        (fn {context,...} =>
          resolve_tac context [@{thm comma_crt_equiv_check_apply}] 1
          THEN resolve_tac context [left_equiv] 1
          THEN resolve_tac context [right_equiv] 1)
    in validate_native label theorem end

  fun make_equivalent ctxt validate_native label actual canonical conversion
      actual_admitted canonical_admitted congruence =
    let
      val middle=Thm.term_of (Thm.rhs_of conversion)
      val _=checked_proposition validate_native (label ^ " input admission")
        (admitted_proposition actual) actual_admitted
      val _=checked_proposition validate_native (label ^ " result admission")
        (admitted_proposition canonical) canonical_admitted
    in transport_equivalence ctxt validate_native label conversion actual middle
      canonical congruence end

  fun make_support_fact validate_native evaluate validate_equation supported_check
      actual node observer program column equivalent =
    let
      val canonical_support = @{term comma_crt_supported} $ column
      val support_thm=evaluate "Canonical Continue column support" canonical_support
      val support_rhs=Thm.term_of (Thm.rhs_of support_thm)
      val supported=bool_result "Canonical Continue column support" support_thm
      val support_thm=validate_equation "Canonical Continue support value"
        canonical_support support_rhs support_thm
      val actual_support = @{term comma_crt_supported} $ (actual node observer program)
      val expected=HOLogic.mk_eq (actual_support,
        if supported then @{term True} else @{term False})
      val support_equivalence=supported_check OF [equivalent]
      val transferred=Thm.transitive (mk_meta_eq support_equivalence) support_thm
      val theorem=transferred RS @{thm meta_eq_to_obj_eq}
      val expected_prop=HOLogic.mk_Trueprop expected
      val _=if Thm.prop_of theorem aconv expected_prop then ()
        else error "Continue image support transfer has a different proposition"
      val theorem=validate_native "Continue image support transfer" theorem
    in (supported,theorem) end

  (* Memoize closed, literal-producing applications of the shifted CRT fold.
     The cache and active set are owned by one evaluator request.  In
     particular, the key is the exact application term (including its full
     shift); no phase, source occurrence, or cross-request identifier is
     introduced here. *)
  fun apply_memo_proc ctxt facts validate_equation hits misses : Simplifier.simproc =
    let
      val active = Unsynchronized.ref (Termtab.empty: unit Termtab.table)
      val reported = Unsynchronized.ref false
      val apply_name = @{const_name comma_crt_apply_shifted_from}
      val apply_type = Sign.the_const_type (Proof_Context.theory_of ctxt) apply_name
      val opT = @{typ comma_crt_boolean_operation}
      val operation_names = [@{const_name Comma_CRT_And}, @{const_name Comma_CRT_Or}]
      val nat_value = natural_value

      val internal_column = column_shape (is_some o nat_value)

      fun closed term = not (Term.is_open term) andalso
        null (Term.add_frees term []) andalso null (Term.add_vars term [])

      fun forbidden_source_constant term =
        let
          val forbidden =
            [@{const_name comma_phase_continue_compile_job},
             @{const_name comma_continue_job_observe},
             @{const_name comma_semantic_phase_continue_columns},
             @{const_name comma_semantic_phase_program_for_class},
             @{const_name comma_semantic_port_program_of_source},
             @{const_name comma_phase_program_operator_nf},
             @{const_name comma_phase_program_entry_core_value_action}]
        in Term.exists_subterm
          (fn Const (name,_) => member (op =) forbidden name | _ => false) term end

      fun supported_application term =
        bounded_term_size 4096 term andalso closed term andalso
        not (forbidden_source_constant term) andalso
        (case Term.strip_comb term of
          (Const (name,_),[depth,shift,operation,left,right]) =>
            name = apply_name andalso
            (case (nat_value depth, nat_value shift, operation) of
              (SOME d,SOME _,Const (op_name,_)) => d <= 4 andalso
                member (op =) operation_names op_name andalso
                internal_column left andalso internal_column right
            | _ => false) andalso
            fastype_of term = columnT
        | _ => false)

      fun closed_equation theorem =
        Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem) andalso
        null (Thm.tpairs_of theorem) andalso closed (Thm.prop_of theorem)

      fun checked_cache label key =
        (case Termtab.lookup (!facts) key of
          NONE => NONE
        | SOME theorem =>
            let
              val rhs = Thm.term_of (Thm.rhs_of theorem)
              val _ = if bounded_term_size 4096 rhs andalso
                  internal_column rhs andalso supported_application key
                then () else error (label ^ " is not a bounded literal CRT equation")
              val theorem = validate_equation label key rhs theorem
            in SOME theorem end)

      fun normalize_argument simpset term =
        if closed term andalso bounded_term_size 4096 term
        then Simplifier.rewrite simpset (Thm.cterm_of simpset term)
        else Thm.reflexive (Thm.cterm_of simpset term)

      fun remove_active keys =
        active := fold Termtab.delete_safe keys (!active)

      fun with_active keys action =
        let
          val _ = active := fold (fn key => Termtab.update (key,())) keys (!active)
          val result = Exn.capture (fn () => action ()) ()
          val _ = remove_active keys
        in Exn.release result end

      fun proc _ simpset ct =
        let
          val input = Thm.term_of ct
          val trace = Comma_Proof_Profile.enabled () andalso not (!reported)
            andalso not (bounded_term_size 200 input)
          val started = Time.now ()
          val _ = if trace then
              (reported := true;
               Comma_Proof_Profile.report "Continue Apply memo first callback")
            else ()
          fun attempt () =
            (case Term.strip_comb input of
              (head as Const (name,_),[depth,shift,operation,left,right]) =>
                if name <> apply_name orelse
                    not (fastype_of input = columnT andalso
                      bounded_term_size 4096 input andalso closed input) orelse
                    forbidden_source_constant input
                then NONE
                else
                  let
                    val argument_equations =
                      map (normalize_argument simpset)
                        [depth,shift,operation,left,right]
                    val arguments_equation = List.foldl
                      (fn (argument_equation,equation) =>
                        Thm.combination equation argument_equation)
                      (Thm.reflexive (Thm.cterm_of simpset head)) argument_equations
                    val _ = if Thm.term_of (Thm.lhs_of arguments_equation) aconv input
                      then () else error "Continue Apply argument conversion changed its input"
                    val canonical = Thm.term_of (Thm.rhs_of arguments_equation)
                    val _ = if trace then
                        Comma_Proof_Profile.report
                          ("Continue Apply memo first normalized closed=" ^
                            Bool.toString (closed_equation arguments_equation) ^
                            " supported=" ^ Bool.toString (supported_application canonical) ^
                            " argument_ms=" ^ Comma_Proof_Profile.elapsed_ms started)
                      else ()
                  in
                    if not (closed_equation arguments_equation) orelse
                        not (supported_application canonical) then NONE
                    else
                      let
                        val same_key = canonical aconv input
                        val external_active = Termtab.defined (!active) canonical
                          andalso not same_key
                      in
                        (case checked_cache "Continue Apply cached equation" canonical of
                            SOME cached =>
                              let
                                val equation=Thm.transitive arguments_equation cached
                                val rhs=Thm.term_of (Thm.rhs_of equation)
                                val equation=validate_equation
                                  "Continue Apply cached result" input rhs equation
                                val _=hits := !hits + 1
                              in SOME equation end
                          | NONE =>
                              if external_active then NONE
                              else let
                                val _=misses := !misses + 1
                                val active_keys=if same_key then [] else [canonical]
                                val computed=with_active active_keys (fn () =>
                                  let
                                    val theorem=if trace then
                                        profile_stage "Continue internal Apply rewrite"
                                          (fn () => Simplifier.rewrite simpset
                                            (Thm.cterm_of simpset canonical))
                                      else Simplifier.rewrite simpset
                                        (Thm.cterm_of simpset canonical)
                                    val rhs=Thm.term_of (Thm.rhs_of theorem)
                                    val lhs=Thm.term_of (Thm.lhs_of theorem)
                                  in
                                    if not (lhs aconv canonical) then
                                      error "Continue Apply conversion changed its canonical input"
                                    else if not (bounded_term_size 4096 rhs andalso
                                        internal_column rhs) then NONE
                                    else if not (closed_equation theorem) then NONE
                                    else
                                      let
                                        val theorem=validate_equation
                                          "Continue Apply computed equation"
                                          canonical rhs theorem
                                      in SOME theorem end
                                  end)
                              in
                                (case computed of
                                  NONE => NONE
                                | SOME canonical_equation =>
                                    let
                                      val equation=Thm.transitive
                                        arguments_equation canonical_equation
                                      val rhs=Thm.term_of (Thm.rhs_of equation)
                                      val equation=validate_equation
                                        "Continue Apply computed result" input rhs equation
                                      val _=case Termtab.lookup (!facts) canonical of
                                        NONE => facts := Termtab.update
                                          (canonical,canonical_equation) (!facts)
                                      | SOME previous =>
                                          let
                                            val previous_rhs = Thm.term_of
                                              (Thm.rhs_of previous)
                                            val _=validate_equation
                                              "Continue Apply existing equation"
                                              canonical previous_rhs previous
                                          in if previous_rhs aconv
                                              Thm.term_of (Thm.rhs_of canonical_equation)
                                            then () else error
                                              "Continue Apply equation cache collision"
                                          end
                                    in SOME equation end)
                              end)
                      end
                  end
            | _ => NONE)
        in
          if not (bounded_term_size 4096 input) then NONE
          else if Termtab.defined (!active) input then NONE
          else with_active [input] attempt
        end

      val depth_var = Var (("depth",0),natT)
      val shift_var = Var (("shift",0),natT)
      val operation_var = Var (("operation",0),opT)
      val left_var = Var (("left",0),columnT)
      val right_var = Var (("right",0),columnT)
      val lhs = list_comb (Const (apply_name,apply_type),
        [depth_var,shift_var,operation_var,left_var,right_var])
    in
      Simplifier.make_simproc ctxt
        {name="comma_crt_apply_request_memo",kind=Simplifier.Congproc true,
         lhss=[lhs],proc=fn _ => fn simpset => fn ct => proc () simpset ct,
         identifier=[]}
    end
end
