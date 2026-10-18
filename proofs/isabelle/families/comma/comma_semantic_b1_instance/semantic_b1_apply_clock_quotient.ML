(* Compose the generic suffix quotient with a right-column-supported quotient. *)
structure Comma_Semantic_B1_Apply_Clock_Quotient =
struct
  type owner =
   {rewrite: int -> int -> cterm -> int * thm,
    stats: unit -> string}

  type suffix_rewrite = int -> int -> cterm -> int * thm
  type right_support = term -> (int * thm) option

  fun make (suffix_rewrite: suffix_rewrite)
      (right_owner: Comma_Semantic_B1_Right_Shift_Quotient.owner)
      (right_support: right_support) : owner =
    let
      val apply_name = @{const_name comma_crt_apply_shifted_from}
      val natT = HOLogic.natT
      fun numeral value = HOLogic.mk_number natT value

      fun right_operand request =
        (case Term.strip_comb request of
          (Const (name, _), [_, _, _, _, right]) =>
            if name = apply_name then right
            else error "B1 clock quotient received a non-Apply request"
        | _ => error "B1 clock quotient requires a saturated Apply request")

      fun validate original representative theorem =
        let
          val expected =
            (case Term.strip_comb original of
              (Const (name, T), [depth, _, operation, left, right]) =>
                if name = apply_name then
                  list_comb (Const (name, T),
                    [depth, numeral representative, operation, left, right])
                else error "B1 clock quotient changed its Apply head"
            | _ => error "B1 clock quotient changed its Apply shape")
        in
          if Thm.term_of (Thm.lhs_of theorem) aconv original andalso
              Thm.term_of (Thm.rhs_of theorem) aconv expected andalso
              Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem) andalso
              null (Thm.tpairs_of theorem)
          then () else error "B1 composed clock quotient changed its exact request"
        end

      fun rewrite depth shift request_ct =
        let
          val original = Thm.term_of request_ct
          val (suffix_shift, suffix_equation) =
            suffix_rewrite depth shift request_ct
          val _ = validate original suffix_shift suffix_equation
          val support = right_support (right_operand original)
        in
          (case support of
            NONE => (suffix_shift, suffix_equation)
          | SOME (lower, admission) =>
              let
                val current_ct = Thm.rhs_of suffix_equation
                val (representative, right_equation) =
                  #rewrite right_owner lower depth suffix_shift admission current_ct
                val theorem = Thm.transitive suffix_equation right_equation
                val _ = validate original representative theorem
              in (representative, theorem) end)
        end

      fun stats () =
        "apply_dag_right_shift_rules=" ^
          Int.toString (#retained_rules right_owner ()) ^
        " apply_dag_right_shift_rule_hits=" ^
          Int.toString (#rule_hits right_owner ()) ^
        " apply_dag_right_shift_rule_builds=" ^
          Int.toString (#rule_builds right_owner ())
    in {rewrite = rewrite, stats = stats} end
end
