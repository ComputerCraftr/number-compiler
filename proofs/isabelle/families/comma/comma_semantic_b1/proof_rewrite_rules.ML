(* Native theorem filtering shared by symbolic and weighted proof consumers. *)
structure Comma_Proof_Rewrite_Rules =
struct
  (* A literal named-node fixture may use t == t as its checked definition.
     Such a theorem is valid evidence but must never enter a simplifier: it
     rewrites its own left side forever.  Keep this filter at the shared
     proof-transport boundary so every consumer has the same behavior. *)
  fun reflexive_object_conclusion proposition =
    (case proposition of
      Const (name,_) $ Abs (_,_,body) =>
        if name = @{const_name All} then
          reflexive_object_conclusion body
        else false
    | _ =>
        (case try HOLogic.dest_imp proposition of
          SOME (_,conclusion) => reflexive_object_conclusion conclusion
        | NONE =>
            (case try HOLogic.dest_eq proposition of
              SOME (left,right) => left aconv right
            | NONE => false)))

  fun reflexive_equation theorem =
    let val conclusion = Logic.strip_assums_concl (Thm.prop_of theorem)
    in
      (case try Logic.dest_equals conclusion of
        SOME (left,right) => left aconv right
      | NONE =>
          (case try HOLogic.dest_Trueprop conclusion of
            SOME proposition => reflexive_object_conclusion proposition
          | NONE => false))
    end

  fun nonreflexive_rules rules = filter (not o reflexive_equation) rules

  val _ =
    let
      val meta_refl = Thm.reflexive
        (Thm.cterm_of @{context} @{term "0::nat"})
      val variable = Free ("filter_phase",@{typ nat})
      val guarded_refl_prop = HOLogic.mk_Trueprop
        (HOLogic.mk_all ("filter_phase",@{typ nat},
          HOLogic.mk_imp
            (HOLogic.mk_binrel @{const_name less}
              (variable,@{term "924::nat"}),
             HOLogic.mk_eq (variable,variable))))
      val guarded_refl = Goal.prove @{context} [] [] guarded_refl_prop
        (fn {context,...} =>
          resolve_tac context [@{thm allI}] 1 THEN
          resolve_tac context [@{thm impI}] 1 THEN
          resolve_tac context [@{thm refl}] 1)
      val informative_prop = HOLogic.mk_Trueprop
        (HOLogic.mk_all ("filter_phase",@{typ nat},
          HOLogic.mk_imp
            (HOLogic.mk_binrel @{const_name less}
              (variable,@{term "5::nat"}),
             HOLogic.mk_eq
               (@{term "(+)::nat \<Rightarrow> nat \<Rightarrow> nat"} $ variable $
                  @{term "0::nat"},variable))))
      val informative = Goal.prove @{context} [] [] informative_prop
        (fn {context,...} =>
          resolve_tac context [@{thm allI}] 1 THEN
          resolve_tac context [@{thm impI}] 1 THEN
          simp_tac context 1)
      val _ = if null (nonreflexive_rules
          [meta_refl,@{thm refl},guarded_refl]) andalso
          length (nonreflexive_rules [@{thm add_0_right}])=1 andalso
          length (nonreflexive_rules [informative])=1 then ()
        else error "CRT proof transport kept a reflexive simplifier rule"
    in () end

end
