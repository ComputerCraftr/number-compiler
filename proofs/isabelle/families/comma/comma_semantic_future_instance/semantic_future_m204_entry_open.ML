(* The decimal-root gate demands only 91 fixed-phase observations.  Each
   observation follows an authenticated MDD path; no graph power is rebuilt. *)
structure Comma_Future_M204_Entry_Open =
struct
  structure Store = Comma_CRT_MDD_Certificate_Store
  val natT = @{typ nat}
  fun literal term =
    let val (typ,value) = HOLogic.dest_number term
    in if typ = natT then value else raise TERM ("Expected natural numeral",[term]) end
  fun define name rhs lthy =
    let
      val ((value,(_,equation)),lthy') = Local_Theory.define
        ((Binding.name name,NoSyn),((Binding.name (name ^ "_def"),[]),rhs)) lthy
      val morphism = Local_Theory.target_morphism lthy'
    in ((Morphism.term morphism value,Morphism.thm morphism equation),lthy') end

  fun publish (weight:Comma_Frontier_M204_Weight_Owner.publication)
      work_store class_roots class_definition rows_selector rows_count
      rank rank_definition lthy =
    let
      val predicate = @{term "\<lambda>rank::comma_boundary_state \<Rightarrow> nat option.
        \<lambda>x::nat. case comma_semantic_decade_summary (Comma_Decade 5 x) of
          Some (h,Comma_Terminal_Fork a) \<Rightarrow>
            comma_boundary_valid (Comma_N,a,(5+h) mod 924) \<and>
            comma_boundary_valid (Comma_Z,a,(5+h) mod 924) \<and>
            (rank (Comma_N,a,(5+h) mod 924)=None \<or>
             rank (Comma_Z,a,(5+h) mod 924)=None)
        | _ \<Rightarrow> False"} $ rank |> Envir.beta_norm
      val ((open_term,open_definition),lthy') =
        define "comma_semantic_p5_entry_future_open" predicate lthy
      val ctxt = Local_Theory.target_of lthy'
      val _ = if Store.radices work_store aconv @{term "[3,4,7,11::nat]"} then ()
        else error "Entry class decoder has incompatible clock axes"
      val scalar = Comma_Entry_Arithmetic.natural_context ctxt
      val ids = map (Store.action_index work_store) class_roots
      val class_map = Thm.term_of (Thm.lhs_of class_definition)
      fun exact_value lhs rhs theorem =
        Comma_CRT_MDD_Proof_Utils.exact_prop ctxt "Entry MDD point projection"
          (Logic.mk_equals (lhs,rhs)) theorem
      fun prove_value lhs facts rules =
        Simplifier.rewrite (scalar |> Simplifier.add_simps (facts @ rules))
          (Thm.cterm_of ctxt lhs)
      fun weight_conversion ct =
        (case strip_comb (Thm.term_of ct) of
          (head,[phase,cid]) => if head aconv #weight weight then
            let
              val p = literal phase
              val c = literal cid
              val _ = if p<924 andalso c<46 then () else error "Entry weight outside checked domain"
              val root = Store.action_index (#store weight) (List.nth (#roots weight,c))
              val point = Comma_CRT_MDD_Point_Eval.prove (#store weight) p root
              val theorem = prove_value (Thm.term_of ct)
                [#definition weight,#theorem point]
                @{thms comma_frontier_m204_mdd_value_def nth_Cons_0 nth_Cons_Suc nth_Cons_numeral nth_Cons' option.sel}
            in SOME (exact_value (Thm.term_of ct)
              (HOLogic.mk_number natT (#payload point)) theorem) end
            else NONE
        | _ => NONE)
        handle TERM _ => NONE
      fun rank_conversion ct =
        (case strip_comb (Thm.term_of ct) of
          (head,[q]) => if head aconv rank then
            let
              val (kind,tail) = HOLogic.dest_prod q
              val (digit,phase) = HOLogic.dest_prod tail
              val a = literal digit
              val p = literal phase
              val offset = if kind aconv @{term Comma_N} then 0
                else if kind aconv @{term Comma_Z} then 8
                else raise TERM ("Unknown boundary kind",[kind])
              val _ = if 2<=a andalso a<=9 andalso p<924 then ()
                else error "Entry child outside checked boundary domain"
              val point = Comma_CRT_MDD_Point_Eval.prove work_store p (List.nth (ids,offset+a-2))
              val decoded = prove_value (class_map $ q) [class_definition,#theorem point]
                @{thms comma_future_m204_mdd_class_def comma_future_m204_family_slot_def
                  prod.case comma_boundary_kind.case fst_conv snd_conv
                  nth_Cons_0 nth_Cons_Suc nth_Cons_numeral nth_Cons' option.sel}
                |> exact_value (class_map $ q) (HOLogic.mk_number natT (#payload point))
              val context = scalar |> Simplifier.add_proc rows_selector
                |> Simplifier.add_simps [rank_definition,decoded,rows_count,
                    @{thm comp_apply},@{thm comma_future_m204_rank_def}]
              val result = Simplifier.rewrite context ct
              val rhs = Thm.term_of (Thm.rhs_of result)
              val _ = if rhs aconv @{term "None::nat option"} then ()
                else (case strip_comb rhs of
                  (Const (name,_),[n]) =>
                    if name = @{const_name Some} andalso literal n >= 0 then ()
                    else error "Entry rank did not normalize to an option numeral"
                | _ => error "Entry rank did not normalize to an option numeral")
            in SOME (exact_value (Thm.term_of ct) rhs result) end
            else NONE
        | _ => NONE)
        handle TERM _ => NONE
      fun procedure name pattern conversion = Simplifier.make_simproc ctxt
        {name=name,kind=Simplifier.Simproc,
         lhss=[Comma_Selected_List_Conversion.schematize pattern],
         proc=fn _ => fn _ => conversion,identifier=[]}
      val weight_proc = procedure "entry_m204_weight_point"
        (#weight weight $ Free ("phase",natT) $ Free ("cid",natT)) weight_conversion
      val rank_proc = procedure "entry_m204_rank_point"
        (rank $ Free ("q",@{typ comma_boundary_state})) rank_conversion
      val context = scalar |> Simplifier.add_proc weight_proc |> Simplifier.add_proc rank_proc
        |> Simplifier.add_simps (open_definition :: @{thms comma_semantic_decade_summary_code
          comma_decade_admitted.simps comma_terminal_weight_decode_def
          comma_terminal_weight_terminal_def comma_offset_orbit_def comma_digit_orbit_sum_def
          comma_boundary_valid_def filter.simps upt_rec})
      val target = HOLogic.mk_Trueprop (HOLogic.mk_eq
        (@{term "filter :: (nat => bool) => nat list => nat list"} $ open_term $
          @{term "[0..<91::nat]"},@{term "[3,34,75::nat]"}))
      val checked = Goal.prove ctxt [] [] target (fn _ => simp_tac context 1)
      val _ = Comma_Proof_Dependency_Audit.require_native_clean ctxt
        "M204 fixed-phase decimal-root gate" [checked]
      val (_,lthy'') = Local_Theory.note
        ((Binding.name "comma_semantic_p5_entry_future_open_checked",[]),[checked]) lthy'
    in lthy'' end
end
