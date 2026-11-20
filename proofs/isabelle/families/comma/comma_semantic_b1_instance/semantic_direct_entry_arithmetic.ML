(* Shared checked Entry arithmetic conversion owners. *)
structure Comma_Direct_Entry_Arithmetic =
struct
  structure Utils = Comma_CRT_MDD_Proof_Utils
  val natT = @{typ nat}
  fun near_operator_plan ctxt =
    let
      val evaluator = Code_Simp.static_conv {ctxt=ctxt,simpset=NONE,
        consts=Code_Thingol.read_const_exprs ctxt
          [@{const_name comma_phase_program_operator_nf}]} ctxt
      val codec = Comma_Selected_List_Alias.make_codec
        {ctxt=ctxt,validate_equation=Comma_Selected_List_Conversion.validate_equation}
      val facts = Unsynchronized.ref (Termtab.empty: thm Termtab.table)
      fun equation program =
        let
          val request = @{term comma_phase_program_operator_nf} $ program $
            HOLogic.mk_number natT 0
        in case Termtab.lookup (!facts) request of
          SOME theorem => Utils.exact_prop ctxt "Cached Near operator equation"
            (Logic.mk_equals (request,Thm.term_of (Thm.rhs_of theorem))) theorem
        | NONE =>
            let
              val evaluated = evaluator (Thm.cterm_of ctxt request)
              val decoded = #decode codec (Thm.rhs_of evaluated)
              val normalized = Simplifier.rewrite
                (Comma_Entry_Arithmetic.natural_context ctxt) (Thm.rhs_of decoded)
              val theorem = Thm.transitive evaluated (Thm.transitive decoded normalized)
              val theorem = Utils.exact_prop ctxt "Near operator equation"
                (Logic.mk_equals (request,Thm.term_of (Thm.rhs_of theorem))) theorem
              val _ = facts := Termtab.update (request,theorem) (!facts)
            in theorem end
        end
    in {equation=equation} end
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
      val seed_name = @{const_name comma_core_seed}
      val hits = Unsynchronized.ref 0
      val seed_hits = Unsynchronized.ref 0
      fun is_parameter name term =
        (case strip_comb term of
          (Const (actual, _), [_]) => actual = name
        | _ => false)
      fun parameter_facts name theorems =
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
            end) theorems Termtab.empty
      val primary_facts = parameter_facts primary_name @{thms comma_core_lift_parameters}
      val modulus_facts = parameter_facts modulus_name @{thms comma_core_lift_parameters}
      val seed_facts = parameter_facts seed_name @{thms comma_core_seed_parameters}
      val _ = if not (Termtab.is_empty primary_facts) andalso
          not (Termtab.is_empty modulus_facts) andalso
          not (Termtab.is_empty seed_facts) then ()
        else error "Core parameter theorem collection is empty"
      fun canonical_nat term =
        (case try HOLogic.dest_number term of
          SOME (typ, value) => typ = natT andalso value >= 0
        | NONE => false)
      fun convert code_output active_ctxt cterm =
        let
          val request = Thm.term_of cterm
          val (head, args) = strip_comb request
          val table = (case head of
              Const (name, _) =>
                if name = primary_name then SOME primary_facts
                else if name = modulus_name then SOME modulus_facts
                else if name = seed_name then SOME seed_facts
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
                          val _ = if is_parameter seed_name request
                            then seed_hits := !seed_hits + 1 else ()
                        in SOME (if code_output then #encode_equation codec result
                          else result) end)
                  end
              end
          | _ => NONE
        end
      val pattern_primary = Comma_Selected_List_Conversion.schematize
        @{term "comma_core_primary (p::nat)"}
      val pattern_modulus = Comma_Selected_List_Conversion.schematize
        @{term "comma_core_modulus (p::nat)"}
      val pattern_seed = Comma_Selected_List_Conversion.schematize
        @{term "comma_core_seed (p::nat)"}
      fun make_procedure code_output = Simplifier.make_simproc ctxt
        {name=if code_output then "frontier24_exact_core_parameter_facts"
          else "frontier24_exact_core_parameter_plain",kind=Simplifier.Congproc true,
         lhss=[pattern_primary,pattern_modulus,pattern_seed],
         proc=fn _ => convert code_output,identifier=[]}
      val procedure = make_procedure true
      val plain_procedure = make_procedure false
    in {procedure=procedure,plain_procedure=plain_procedure,hits=fn () => !hits,
      seed_hits=fn () => !seed_hits} end

  (* Fixed Entry arithmetic belongs to the shared Entry_Port owner.  One
     context-local bundle per admitted sector/digit supplies exact equations
     for seed, potential, period and tree; eta never enters this cache. *)
  fun fixed_entry_port_conversion_plan ctxt =
    let
      val facts = Unsynchronized.ref (Termtab.empty: (thm * thm) Termtab.table)
      val ports = Unsynchronized.ref (Symtab.empty: unit Symtab.table)
      val hits = Unsynchronized.ref 0
      val misses = Unsynchronized.ref 0
      val scalar = Comma_Selected_List_Conversion.make_natural_normalizer ctxt
      val validate = Comma_Selected_List_Conversion.validate_equation
      val codec = Comma_Selected_List_Alias.make_codec
        {ctxt=ctxt,validate_equation=validate}
      val base = Comma_Entry_Arithmetic.natural_context ctxt
      val evaluator = Code_Simp.static_conv
        {ctxt=base,simpset=NONE,consts=
          [@{const_name comma_entry_port_seed},
           @{const_name comma_entry_port_potential},
           @{const_name comma_finite_period},
           @{const_name comma_entry_port_search_tree}]} base
      fun evaluate input =
        let
          val raw = evaluator (Thm.cterm_of base input)
          val decoded = #decode codec (Thm.rhs_of raw)
          val exact = Thm.transitive raw decoded
          val normalized = Simplifier.rewrite base (Thm.rhs_of exact)
        in Thm.transitive exact normalized end
      fun check label expected theorem = Utils.exact_prop ctxt label expected theorem
      fun literal_number T nonnegative term =
        (case try HOLogic.dest_number term of
          SOME (actual,n) => actual = T andalso (not nonnegative orelse n>=0)
            andalso term aconv HOLogic.mk_number T n
        | NONE => false)
      val literal_nat = literal_number natT true
      fun literal_tree term =
        (case strip_comb term of
          (Const (name,_),[first,second,third,fourth]) =>
            if name = @{const_name Comma_Prefix_Leaf} then
              forall literal_nat [first,second,third,fourth]
            else name = @{const_name Comma_Prefix_Split} andalso
              forall literal_nat [first,second] andalso
              literal_tree third andalso literal_tree fourth
        | _ => false)
      fun admit f d =
        let val key = Int.toString f ^ ":" ^ Int.toString d in
          if Symtab.defined (!ports) key then ()
          else
            let
              val _ = misses := !misses + 1
              val _ = if !misses mod 8 = 1 then Comma_Proof_Profile.report
                  ("Frontier24 fixed Entry port proof start count=" ^
                    Int.toString (!misses) ^ " sector=" ^ Int.toString f ^
                    " digit=" ^ Int.toString d) else ()
              val raw_rules = Comma_Entry_Port_Fixed_Facts.build ctxt evaluate check f d
              val _ = (case raw_rules of
                  [seed,potential,period,seed_period,tree] =>
                    let
                      fun require name predicate theorem =
                        let
                          val decoded = #decode codec (Thm.rhs_of theorem)
                          val normalized = Simplifier.rewrite base (Thm.rhs_of decoded)
                          val rhs = Thm.term_of (Thm.rhs_of normalized)
                        in
                          if predicate rhs then ()
                          else error ("Fixed Entry port " ^ name ^
                            " is not literal for sector=" ^ Int.toString f ^
                            " digit=" ^ Int.toString d ^ ": " ^
                            (if Term.size_of_term rhs <= 256 then
                               Syntax.string_of_term ctxt rhs
                             else "head=" ^ Syntax.string_of_term ctxt (Term.head_of rhs) ^
                               " nodes=" ^ Int.toString (Term.size_of_term rhs)))
                        end
                    in
                      require "seed" literal_nat seed;
                      require "potential" (literal_number @{typ int} false) potential;
                      require "period" literal_nat period;
                      require "seed period" literal_nat seed_period;
                      require "tree" literal_tree tree
                    end
                | _ => error "Fixed Entry port has an unexpected fact count")
              fun plain_rule theorem =
                let
                  val decoded = #decode codec (Thm.rhs_of theorem)
                  val normalized = Simplifier.rewrite base (Thm.rhs_of decoded)
                in Thm.transitive theorem (Thm.transitive decoded normalized) end
              val plain_rules = map plain_rule raw_rules
              val rules = map (#encode_equation codec) plain_rules
              fun insert (plain,theorem) table =
                let val lhs = Thm.term_of (Thm.lhs_of theorem)
                in case Termtab.lookup table lhs of
                  NONE => Termtab.update (lhs,(plain,theorem)) table
                | SOME (prior_plain,prior) =>
                    if Thm.prop_of prior aconv Thm.prop_of theorem andalso
                        Thm.prop_of prior_plain aconv Thm.prop_of plain then table
                    else error "Fixed Entry port equations disagree"
                end
              val _ = facts := fold insert (plain_rules ~~ rules) (!facts)
              val _ = ports := Symtab.update (key,()) (!ports)
              val _ = if !misses mod 8 = 1 then Comma_Proof_Profile.report
                  ("Frontier24 fixed Entry port proof complete count=" ^
                    Int.toString (!misses) ^ " rewrites=" ^
                    Int.toString (!hits)) else ()
            in () end
        end
      fun small_nat term =
        (case try HOLogic.dest_number term of
          SOME (T,n) => if T=natT andalso 0<=n andalso n<=9
            then SOME (IntInf.toInt n) else NONE
        | NONE => NONE)
      fun convert code_output active_ctxt ct =
        let
          val original = Thm.term_of ct
          val valid_context = Context.subthy
            (Proof_Context.theory_of ctxt,Proof_Context.theory_of active_ctxt)
          val heads = [@{const_name comma_entry_port_seed},
            @{const_name comma_entry_port_potential},
            @{const_name comma_finite_period},
            @{const_name comma_entry_port_search_tree}]
          val expected_shape = (case strip_comb original of
              (Const (name,_),[_,_]) => member (op =) heads name
            | _ => false)
        in if not valid_context orelse not expected_shape orelse
            not (Utils.closed original) orelse Term.size_of_term original>512
          then NONE else
        let
          val argument = #convert scalar active_ctxt
          val normalized = Conv.combination_conv
            (Conv.arg_conv argument) argument ct
          val request = Thm.term_of (Thm.rhs_of normalized)
        in case strip_comb request of
          (_, [first,second]) =>
            (case (small_nat first,small_nat second) of
              (SOME f,SOME d) =>
                if f<1 then NONE else
                let
                  val _ = admit f d
                in case Termtab.lookup (!facts) request of
                  NONE => NONE
                | SOME (plain,encoded) =>
                    let
                      val fact = if code_output then encoded else plain
                      val exact = Thm.transitive normalized fact
                      val _ = Utils.exact_prop ctxt "Fixed Entry port conversion"
                        (Logic.mk_equals (original,Thm.term_of (Thm.rhs_of exact))) exact
                      val _ = hits := !hits + 1
                    in SOME exact end
                end
            | _ => NONE)
        | _ => NONE end
        end
      val patterns = map Comma_Selected_List_Conversion.schematize
        [@{term "comma_entry_port_seed (f::nat) (d::nat)"},
         @{term "comma_entry_port_potential (f::nat) (d::nat)"},
         @{term "comma_finite_period (f::nat) (d::nat)"},
         @{term "comma_entry_port_search_tree (f::nat) (d::nat)"}]
      fun make_procedure code_output = Simplifier.make_simproc ctxt
        {name=if code_output then "frontier24_fixed_entry_port"
          else "frontier24_fixed_entry_port_plain",kind=Simplifier.Congproc true,
         lhss=patterns,proc=fn _ => convert code_output,identifier=[]}
      val procedure = make_procedure true
      val plain_procedure = make_procedure false
      fun statistics () = "fixed_entry_port_rewrites=" ^ Int.toString (!hits) ^
        " fixed_entry_port_proofs=" ^ Int.toString (!misses)
    in {procedure=procedure,plain_procedure=plain_procedure,statistics=statistics} end

end
