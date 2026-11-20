(* Shared, theorem-producing fixed Entry-port specialization. *)
structure Comma_Entry_Port_Fixed_Facts =
struct
  fun checked_tuple_projections ctxt check label bundle tuple paths =
    let
      val _ = if List.all (List.all (fn 0 => true | 1 => true | _ => false)) paths
        then () else error "Tuple projection path contains an unsupported selector"
      fun project [] value = value
        | project (0::rest) value = project rest (HOLogic.mk_fst value)
        | project (_::rest) value = project rest (HOLogic.mk_snd value)
      fun component [] value = value
        | component (0::rest) value = component rest (#1 (HOLogic.dest_prod value))
        | component (_::rest) value = component rest (#2 (HOLogic.dest_prod value))
      val context = put_simpset HOL_basic_ss ctxt
        |> Simplifier.add_simps @{thms fst_conv snd_conv}
      fun projection path =
        let
          val left = component path tuple
          val tuple_rhs = Thm.term_of (Thm.rhs_of bundle)
          val right = component path tuple_rhs
          val free = Free ("checked_tuple",fastype_of tuple)
          val selector = Term.lambda free (project path free)
          val applied = Thm.combination
            (Thm.reflexive (Thm.cterm_of ctxt selector)) bundle
          val left_conversion = Simplifier.rewrite context
            (Thm.cterm_of ctxt (selector $ tuple))
          val right_conversion = Simplifier.rewrite context
            (Thm.cterm_of ctxt (selector $ tuple_rhs))
          val _ = if Thm.term_of (Thm.rhs_of left_conversion) aconv left andalso
              Thm.term_of (Thm.rhs_of right_conversion) aconv right then ()
            else error (label ^ " did not reduce to the selected tuple components")
          val theorem = Thm.transitive (Thm.symmetric left_conversion)
            (Thm.transitive applied right_conversion)
        in check label (Logic.mk_equals (left,right)) theorem end
    in map projection paths end

  fun build ctxt evaluate check f d =
    let
      val natT = @{typ nat}
      fun nat n = HOLogic.mk_number natT n
      val _ = if 1 <= f andalso f <= 9 andalso 0 <= d andalso d < 10 then ()
        else error "Entry port specialization is outside the admitted domain"
      val (f_term,d_term) = (nat f,nat d)
      val seed = @{term comma_entry_port_seed} $ f_term $ d_term
      val potential = @{term comma_entry_port_potential} $ f_term $ d_term
      val period = @{term comma_finite_period} $ f_term $ d_term
      val tree = @{term comma_entry_port_search_tree} $ f_term $ d_term
      val seed_period = @{term comma_finite_period} $ f_term $ seed
      val input = HOLogic.mk_prod (seed, HOLogic.mk_prod (potential,
        HOLogic.mk_prod (period, HOLogic.mk_prod (seed_period,tree))))
      val raw = evaluate input
      val bundle = check "Fixed Entry port tuple" (Logic.mk_equals
        (input,Thm.term_of (Thm.rhs_of raw))) raw
      val paths = [[0],[1,0],[1,1,0],[1,1,1,0],[1,1,1,1]]
      val projections = checked_tuple_projections ctxt check
        "Fixed Entry port projection" bundle input paths
    in (case projections of
        [seed_eq,potential_eq,period_eq,seed_period_eq,tree_eq] =>
          let
            val period_of = @{term comma_finite_period} $ f_term
            val congruence = Thm.combination
              (Thm.reflexive (Thm.cterm_of ctxt period_of)) seed_eq
            val normalized = Thm.transitive (Thm.symmetric congruence) seed_period_eq
            val checked = check "Fixed Entry seed-period projection"
              (Thm.prop_of normalized) normalized
          in [seed_eq,potential_eq,period_eq,checked,tree_eq] end
      | _ => error "Fixed Entry port tuple projection count changed")
    end
end
