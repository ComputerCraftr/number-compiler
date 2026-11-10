(* Exact request-local bridges for natural numerals in Code_Simp's code form.
   Root aliases and selected results are checked against their HOL endpoint. *)
structure Comma_Selected_List_Alias =
struct
  fun make_codec {ctxt, validate_equation} =
    let
      val natT = @{typ nat}
      val numT = @{typ num}
      val integerT = @{typ Code_Numeral.integer}
      fun num_literal value =
        let
          fun build 1 = Const (@{const_name Num.One}, numT)
            | build number =
                let
                  val constructor = if number mod 2 = 0
                    then @{const_name Num.Bit0} else @{const_name Num.Bit1}
                in Const (constructor, numT --> numT) $ build (number div 2) end
        in if value > 0 then build value
          else error "Selected-list code numeral must be positive" end
      fun code_natural value =
        Const (@{const_name Code_Numeral.nat_of_integer}, integerT --> natT) $
          (Const (@{const_name Code_Numeral.Pos}, numT --> integerT) $
            num_literal value)
      fun map_term rewrite term =
        (case rewrite term of
          SOME replacement => replacement
        | NONE =>
            (case term of
              Abs (name, typ, body) => Abs (name, typ, map_term rewrite body)
            | function $ argument =>
                map_term rewrite function $ map_term rewrite argument
            | _ => term))
      val thy = Proof_Context.theory_of ctxt
      fun unoverload_term term = Term.map_aterms (fn Const (name, typ) =>
        Const (Axclass.unoverload_const thy (name, typ), typ) | atom => atom) term
      fun explicit_alias term =
        let
          fun replace_natural candidate =
            (case try HOLogic.dest_number candidate of
              SOME (typ, value) =>
                if typ = natT andalso value >= 2 then SOME (code_natural value)
                else NONE
            | NONE => NONE)
        in unoverload_term (map_term replace_natural term) end
      val plain_alias = unoverload_term
      val inverse_ss = put_simpset HOL_basic_ss ctxt
        |> Simplifier.add_simps
          [@{thm Code_Numeral.Pos_def},
           @{thm Code_Numeral.nat_of_integer_numeral},
           @{thm Int.Pos_def}, @{thm Int.Neg_def}, @{thm numeral_One}]
      fun decode cterm =
        let
          val overloaded = Axclass.overload_conv ctxt cterm
          val inverse = Simplifier.rewrite inverse_ss (Thm.rhs_of overloaded)
        in validate_equation (Thm.term_of cterm)
          (Thm.transitive overloaded inverse) end
      fun prove_alias alias target =
        let
          val theorem = decode (Thm.cterm_of ctxt alias)
          val _ = if Thm.term_of (Thm.rhs_of theorem) aconv target then ()
            else error "Selected-list alias did not restore its exact endpoint"
        in theorem end
      fun encode_equation theorem =
        let
          val request = Thm.term_of (Thm.lhs_of theorem)
          val value = Thm.term_of (Thm.rhs_of theorem)
          val encoded = explicit_alias value
        in
          if encoded aconv value then validate_equation request theorem
          else
            let
              val inverse = prove_alias encoded value
              val result = Thm.transitive theorem (Thm.symmetric inverse)
            in validate_equation request result end
        end
    in {explicit_alias=explicit_alias, plain_alias=plain_alias,
        prove_alias=prove_alias, decode=decode,
        encode_equation=encode_equation} end

  fun make {ctxt, root_definition, validate_equation} =
    let
      val root = (if can Logic.dest_equals (Thm.prop_of root_definition)
        then root_definition else root_definition RS @{thm eq_reflection})
      val root_term = Thm.term_of (Thm.lhs_of root)
      val _ = validate_equation root_term root
      val root_body = Thm.term_of (Thm.rhs_of root)
      val codec = make_codec {ctxt=ctxt, validate_equation=validate_equation}
      val explicit_alias = #explicit_alias codec
      val plain_alias = #plain_alias codec
      val prove_root_alias = #prove_alias codec
      fun add_alias alias target aliases =
        if alias aconv root_term orelse alias aconv root_body then aliases
        else
          (case Termtab.lookup aliases alias of
            NONE => Termtab.update (alias, target) aliases
          | SOME prior => if prior aconv target then aliases
              else error "Selected-list root alias targets disagree")
      val root_aliases = Termtab.empty
        |> add_alias (explicit_alias root_term) root_term
        |> add_alias (plain_alias root_term) root_term
        |> add_alias (explicit_alias root_body) root_body
        |> add_alias (plain_alias root_body) root_body
      val _ = if Termtab.size root_aliases <= 4 then ()
        else error "Selected-list root alias set exceeded its fixed extent"
      val root_alias_proofs = Unsynchronized.ref (Termtab.empty: thm Termtab.table)
      val root_body_refl = Thm.reflexive (Thm.cterm_of ctxt root_body)
      fun root_equation term =
        if term aconv root_term then SOME root
        else if term aconv root_body then SOME root_body_refl
        else
          (case Termtab.lookup root_aliases term of
            NONE => NONE
          | SOME target =>
              SOME (case Termtab.lookup (!root_alias_proofs) term of
                SOME theorem => theorem
              | NONE =>
                  let
                    val endpoint = prove_root_alias term target
                    val theorem = if target aconv root_term
                      then Thm.transitive endpoint root else endpoint
                    val _ = validate_equation term theorem
                    val _ = if Thm.term_of (Thm.rhs_of theorem) aconv root_body then ()
                      else error "Selected-list alias did not reach the literal root body"
                    val _ = root_alias_proofs :=
                      Termtab.update (term, theorem) (!root_alias_proofs)
                  in theorem end))
      fun named_equation term =
        if term aconv root_term then SOME (Thm.reflexive (Thm.lhs_of root))
        else if term aconv root_body then SOME (Thm.symmetric root)
        else Option.map (fn equation =>
          Thm.transitive equation (Thm.symmetric root)) (root_equation term)
      fun canonicalize_spine select_root cterm =
        let val term = Thm.term_of cterm in
          case select_root term of
            SOME equation => equation
          | NONE =>
            (case strip_comb term of
              (Const (constant, _), [_, _]) =>
                if constant = @{const_name nth} then
                  Conv.fun_conv (Conv.arg_conv
                    (canonicalize_spine select_root)) cterm
                else Thm.reflexive cterm
            | (Const (constant, typ), [_]) =>
                if constant = @{const_name size} orelse
                    constant = Axclass.unoverload_const (Proof_Context.theory_of ctxt)
                      (@{const_name size},typ) then
                  let
                    val headed = Conv.fun_conv (Axclass.overload_conv ctxt) cterm
                    val rooted = Conv.arg_conv
                      (canonicalize_spine select_root) (Thm.rhs_of headed)
                  in Thm.transitive headed rooted end
                else Thm.reflexive cterm
            | _ => Thm.reflexive cterm)
        end
      val canonical_root = canonicalize_spine named_equation
      val canonical_value = canonicalize_spine root_equation
      (* A named table is already a compact authenticated owner.  A bundle
         projection carries unrelated fields and instead uses its exact value. *)
      val canonical_lookup =
        (case root_term of Const _ => canonical_root | _ => canonical_value)
      val encode_result = #encode_equation codec
    in {root_aliases=root_aliases, root_equation=root_equation,
        canonical_root=canonical_root, canonical_value=canonical_value,
        canonical_lookup=canonical_lookup,
        encode_result=encode_result,
        code_pattern=plain_alias} end
end
