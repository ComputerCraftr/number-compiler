(* Adversarial checks for authenticated, context-owned Apply shortcuts. *)
structure Comma_Semantic_B1_CRT_Apply_Shortcut_Fixture =
struct
  type owner =
   {convert: cterm -> thm option,
    recursive_certifications: unit -> int,
    fallbacks: unit -> int,
    derive_rejections: unit -> int,
    shortcut_applications: unit -> int,
    cache_hits: unit -> int,
    retained_keys: unit -> int}
  type comparison = {convert: cterm -> thm option}

  fun check ctxt (owner: owner) (comparison: comparison) =
    let
      val natT = @{typ nat}
      val columnT = @{typ comma_crt_column}
      val applyT = @{typ
        "nat => nat => comma_crt_boolean_operation => comma_crt_column => comma_crt_column => comma_crt_column"}
      val and_op = Const (@{const_name Comma_CRT_And},
        @{typ comma_crt_boolean_operation})
      val or_op = Const (@{const_name Comma_CRT_Or},
        @{typ comma_crt_boolean_operation})
      val false_column = Const (@{const_name Comma_CRT_Bool}, @{typ bool} --> columnT) $
        @{term False}
      val true_column = Const (@{const_name Comma_CRT_Bool}, @{typ bool} --> columnT) $
        @{term True}
      fun apply depth shift operation left right =
        list_comb (Const (@{const_name comma_crt_apply_shifted_from}, applyT),
          [HOLogic.mk_number natT depth, HOLogic.mk_number natT shift,
           operation, left, right])
      fun run request = #convert owner (Thm.cterm_of ctxt request)
      fun result_is request expected theorem =
        (case theorem of
          SOME checked => Thm.term_of (Thm.lhs_of checked) aconv request andalso
            Thm.term_of (Thm.rhs_of checked) aconv expected andalso
            null (Thm.prems_of checked) andalso null (Thm.hyps_of checked) andalso
            null (Thm.tpairs_of checked) andalso null (Thm_Deps.all_oracles [checked])
        | NONE => false)
      fun compare_result theorem expected =
        (case theorem of
          SOME checked =>
            let
              val proposition = HOLogic.mk_eq (Thm.term_of (Thm.rhs_of checked), expected)
            in
              (case #convert comparison (Thm.cterm_of ctxt proposition) of
                SOME equation =>
                  if Thm.term_of (Thm.lhs_of equation) aconv proposition andalso
                      null (Thm.prems_of equation) andalso null (Thm.hyps_of equation) andalso
                      null (Thm.tpairs_of equation) andalso
                      null (Thm_Deps.all_oracles [equation])
                  then SOME equation else NONE
              | NONE => NONE)
            end
        | NONE => NONE)
      fun equality_is expected base right theorem =
        (case theorem of
          SOME checked =>
            (case base of
              SOME checked_base =>
                let val proposition = HOLogic.mk_eq
                  (Thm.term_of (Thm.rhs_of checked_base), right)
                in Thm.term_of (Thm.lhs_of checked) aconv proposition andalso
                  Thm.term_of (Thm.rhs_of checked) aconv expected andalso
                  null (Thm.prems_of checked) andalso null (Thm.hyps_of checked) andalso
                  null (Thm.tpairs_of checked) andalso
                  null (Thm_Deps.all_oracles [checked])
                end
            | NONE => false)
        | NONE => false)

      val values = map (fn value =>
        Const (@{const_name Comma_CRT_Bool}, @{typ bool} --> columnT) $ value)
        [@{term False}, @{term True}, @{term False}, @{term True}, @{term True},
         @{term False}, @{term True}, @{term False}, @{term False}, @{term True},
         @{term False}]
      fun node children = Const (@{const_name Comma_CRT_Node},
          natT --> HOLogic.listT columnT --> columnT) $
        HOLogic.mk_number natT 3 $ HOLogic.mk_list columnT children
      val x = node values
      val shifted_x = node (tl values @ [hd values])

      val reflexive_request = apply 0 0 and_op x x
      val reflexive_before = #shortcut_applications owner ()
      val reflexive_recursive = #recursive_certifications owner ()
      val reflexive_fallbacks = #fallbacks owner ()
      val reflexive_result = run reflexive_request
      val reflexive_ok = result_is reflexive_request x reflexive_result andalso
        #shortcut_applications owner () = reflexive_before + 1 andalso
        #recursive_certifications owner () = reflexive_recursive andalso
        #fallbacks owner () = reflexive_fallbacks

      val canonical_request = apply 0 2 and_op false_column true_column
      val shift_alias = apply 0 13 and_op false_column true_column
      val memo_keys_before = #retained_keys owner ()
      val memo_hits_before = #cache_hits owner ()
      val memo_shortcuts_before = #shortcut_applications owner ()
      val memo_recursive_before = #recursive_certifications owner ()
      val canonical_result = run canonical_request
      val memo_keys_after = #retained_keys owner ()
      val memo_hits_after = #cache_hits owner ()
      val memo_shortcuts_after = #shortcut_applications owner ()
      val memo_recursive_after = #recursive_certifications owner ()
      val exact_warm_result = run canonical_request
      val exact_warm_hits = #cache_hits owner ()
      val exact_warm_shortcuts = #shortcut_applications owner ()
      val exact_warm_recursive = #recursive_certifications owner ()
      val alias_result = run shift_alias
      val alias_hits = #cache_hits owner ()
      val alias_recursive = #recursive_certifications owner ()
      val memo_shift_alias_ok = result_is canonical_request false_column canonical_result andalso
        result_is canonical_request false_column exact_warm_result andalso
        result_is shift_alias false_column alias_result andalso
        (* The preceding owner fixture already admitted shift 1.  At depth 0,
           shifts 2 and 13 both normalize to that existing nonzero key. *)
        memo_keys_after = memo_keys_before andalso
        #retained_keys owner () = memo_keys_after andalso
        memo_hits_after > memo_hits_before andalso
        exact_warm_hits > memo_hits_after andalso
        alias_hits > exact_warm_hits andalso
        memo_shortcuts_after = memo_shortcuts_before andalso
        exact_warm_shortcuts = memo_shortcuts_after andalso
        #shortcut_applications owner () = exact_warm_shortcuts andalso
        memo_recursive_after = memo_recursive_before andalso
        exact_warm_recursive = memo_recursive_after andalso
        alias_recursive = exact_warm_recursive

      (* A valid, declared but foreign DAG must be rejected before the False
         absorber is considered. This exercises the closed authority boundary. *)
      val dag = @{term Comma_B1_CRT_Column_DAG_Empty}
      val dagT = fastype_of dag
      val column_at = Const (@{const_name comma_semantic_b1_crt_column_at},
        dagT --> natT --> columnT)
      val foreign = column_at $ dag $ HOLogic.mk_number natT 2
      val foreign_request = apply 0 0 and_op false_column foreign
      val foreign_shortcuts = #shortcut_applications owner ()
      val foreign_fallbacks = #fallbacks owner ()
      val foreign_rejections = #derive_rejections owner ()
      val foreign_result = run foreign_request
      val foreign_rejected = is_none foreign_result andalso
        #shortcut_applications owner () = foreign_shortcuts andalso
        #fallbacks owner () > foreign_fallbacks andalso
        #derive_rejections owner () = foreign_rejections

      (* Left-neutral operations at a nonzero shift must preserve the shifted
         right operand. The zero-shift-only shortcut must not erase that clock. *)
      val and_true_request = apply 1 1 and_op true_column x
      val or_false_request = apply 1 1 or_op false_column x
      val neutral_recursive = #recursive_certifications owner ()
      val neutral_fallbacks = #fallbacks owner ()
      val and_true_result = run and_true_request
      val after_and_recursive = #recursive_certifications owner ()
      val after_and_fallbacks = #fallbacks owner ()
      val or_false_result = run or_false_request
      val after_or_recursive = #recursive_certifications owner ()
      val after_or_fallbacks = #fallbacks owner ()
      val and_true_expected = compare_result and_true_result shifted_x
      val and_true_unshifted = compare_result and_true_result x
      val or_false_expected = compare_result or_false_result shifted_x
      val or_false_unshifted = compare_result or_false_result x
      val neutral_clock_ok = equality_is @{term True} and_true_result shifted_x
            and_true_expected andalso
        equality_is @{term False} and_true_result x and_true_unshifted andalso
        equality_is @{term True} or_false_result shifted_x or_false_expected andalso
        equality_is @{term False} or_false_result x or_false_unshifted andalso
        after_and_recursive > neutral_recursive andalso
        after_or_recursive > after_and_recursive andalso
        after_and_fallbacks = neutral_fallbacks andalso
        after_or_fallbacks = after_and_fallbacks

      (* The first parse cannot use the shortcut because If is not itself an
         admitted column. After closed-guard normalization it must use exactly
         one shortcut, with no recursive certification. *)
      val closed_if = Const (@{const_name If},
        @{typ bool} --> columnT --> columnT --> columnT) $
        @{term True} $ false_column $ true_column
      val normalized_request = apply 0 0 and_op closed_if true_column
      val normalized_shortcuts = #shortcut_applications owner ()
      val normalized_recursive = #recursive_certifications owner ()
      val normalized_hits = #cache_hits owner ()
      val normalized_result = run normalized_request
      val normalized_hits_after = #cache_hits owner ()
      val normalized_ok = result_is normalized_request false_column normalized_result andalso
        #shortcut_applications owner () = normalized_shortcuts andalso
        #recursive_certifications owner () = normalized_recursive andalso
        normalized_hits_after > normalized_hits andalso
        #fallbacks owner () = after_or_fallbacks
    in
      if reflexive_ok andalso memo_shift_alias_ok andalso foreign_rejected andalso
          neutral_clock_ok andalso normalized_ok
      then Comma_Proof_Profile.report
        "B1 apply shortcuts canonical-memo=true zero-equality=true foreign-absorber-refused=true nonzero-left-neutral-clock=true normalized-if=true"
      else
        let
          fun show value = if value then "true" else "false"
        in
          error ("B1 authenticated Apply shortcut fixture failed: " ^
            "reflexive=" ^ show reflexive_ok ^
            " canonical_shift_alias=" ^ show memo_shift_alias_ok ^
            " foreign_rejected=" ^ show foreign_rejected ^
            " neutral_clock=" ^ show neutral_clock_ok ^
            " normalized_if=" ^ show normalized_ok ^
            " keys=" ^ Int.toString memo_keys_before ^ "->" ^
              Int.toString memo_keys_after ^
            " hits=" ^ Int.toString memo_hits_before ^ "->" ^
              Int.toString memo_hits_after ^ "->" ^
              Int.toString exact_warm_hits ^ "->" ^ Int.toString alias_hits ^
            " shortcuts=" ^ Int.toString memo_shortcuts_before ^ "->" ^
              Int.toString memo_shortcuts_after ^
            " recursive=" ^ Int.toString memo_recursive_before ^ "->" ^
              Int.toString memo_recursive_after ^ "->" ^
              Int.toString exact_warm_recursive ^ "->" ^ Int.toString alias_recursive ^
            " normalized_hits=" ^ Int.toString normalized_hits ^ "->" ^
              Int.toString normalized_hits_after)
        end
    end
end
