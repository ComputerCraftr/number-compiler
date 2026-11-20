(* End-to-end native smoke for proposal construction and checked zip replay. *)
structure Comma_Semantic_Future_Zip_Producer_Fixture =
struct
  structure Arena = Comma_CRT_MDD_Arena
  structure Store = Comma_CRT_MDD_Certificate_Store
  structure Producer = Comma_Semantic_Future_Zip_Producer
  structure Certificate = Comma_Semantic_Future_Zip_Certificates
  val natT = @{typ nat}
  fun nat n = HOLogic.mk_number natT n

  fun equation ctxt combine a b c =
    let
      val proposition = HOLogic.mk_Trueprop
        (HOLogic.mk_eq (combine $ nat a $ nat b,nat c))
    in Goal.prove ctxt [] [] proposition
      (fn {context,...} => simp_tac context 1) end

  fun run initial_lthy =
    let
      val left = Arena.create [3,4,7,11]
      val right = Arena.create [3,4,7,11]
      fun leaf arena n =
        if n=0 then Arena.action_none arena else Arena.action_some arena (n-1)
      val left_root = Arena.action_branch left 0 (map (leaf left) [0,1,2])
      val right_root = Arena.action_branch right 1 (map (leaf right) [0,1,2,3])
      val left_wide = Arena.action_branch left 2 (map (leaf left) [0,1,2,3,4,5,6])
      val right_wide = Arena.action_branch right 3 (map (leaf right) [0,1,2,3,4,5,6,7,8,9,10])
      val wide = Producer.zip_roots (Arena.create [3,4,7,11])
        left [left_wide] right [right_wide] (fn x => fn y => 2*x+y)
      val asymmetric = Producer.zip_roots (Arena.create [3,4,7,11])
        left [left_root,left_root] right [right_root,right_root]
        (fn x => fn y => 2*x+y)
      val reduced = Producer.zip_roots (Arena.create [3,4,7,11])
        left [left_root,left_root] right [right_root,right_root] (fn _ => fn _ => 0)
      val _ = if #pair_states asymmetric > 1 andalso
          Arena.node_count (#arena reduced) = 1 andalso
          Arena.action_index (#arena asymmetric) (hd (#roots asymmetric)) =
            Arena.action_index (#arena asymmetric) (List.nth (#roots asymmetric,1)) then ()
        else error "Future zip proposal lost its unequal-axis or reduced result"
      val binary_left = Arena.create [2]
      val binary_right = Arena.create [2]
      val binary_l = Arena.action_branch binary_left 0 (map (leaf binary_left) [0,1])
      val binary_r = Arena.action_branch binary_right 0 (map (leaf binary_right) [1,0])
      val binary = Producer.zip_roots (Arena.create [2]) binary_left [binary_l]
        binary_right [binary_r] (fn x => fn y => 2*x+y)
      val (left_store,lthy1) = Store.make "zip_fixture_left" left initial_lthy
      val (right_store,lthy2) = Store.make "zip_fixture_right" right lthy1
      val (out_store,lthy3) = Store.make "zip_fixture_out" (#arena asymmetric) lthy2
      val (reduced_store,lthy4) = Store.make "zip_fixture_reduced" (#arena reduced) lthy3
      val (wide_store,lthy_wide) = Store.make "zip_fixture_wide" (#arena wide) lthy4
      val (binary_left_store,lthy_binary1) = Store.make "zip_binary_left" binary_left lthy_wide
      val (binary_right_store,lthy_binary2) = Store.make "zip_binary_right" binary_right lthy_binary1
      val (binary_store,lthy_binary3) = Store.make "zip_binary_out" (#arena binary) lthy_binary2
      val foreign_arena = Arena.create [4,3,7,11]
      val foreign_root = Arena.action_none foreign_arena
      val (foreign_store,lthy5) = Store.make "zip_fixture_foreign" foreign_arena lthy_binary3
      val ctxt = Local_Theory.target_of lthy5
      val combine = @{term "\<lambda>x::nat. \<lambda>y::nat. 2*x+y"}
      val zero = @{term "\<lambda>x::nat. \<lambda>y::nat. (0::nat)"}
      val l = Store.action_index left_store left_root
      val r = Store.action_index right_store right_root
      val out = Store.action_index out_store (hd (#roots asymmetric))
      val reduced_root = Store.action_index reduced_store (hd (#roots reduced))
      val leaf_calls = Unsynchronized.ref 0
      val poison_after_success = Unsynchronized.ref false
      fun flaky a b c =
        if !poison_after_success then error "Warm Zip replay evaluated a leaf"
        else (leaf_calls := !leaf_calls+1;
          if !leaf_calls=2 then error "Injected Zip leaf failure"
          else equation ctxt combine a b c)
      val retry_replay = Certificate.make ctxt left_store right_store out_store combine flaky
      val _ = (case Exn.capture (fn () => Certificate.certify retry_replay l r out) () of
          Exn.Exn (ERROR _) => ()
        | Exn.Exn exn => Exn.reraise exn
        | Exn.Res _ => error "Zip fixture did not inject its leaf failure")
      val _ = if Certificate.proof_count retry_replay>0 then ()
        else error "Zip failure did not follow a completed child proof"
      val retry_theorem = Certificate.certify retry_replay l r out
      val retry_count = Certificate.proof_count retry_replay
      val _ = poison_after_success := true
      val warm = Certificate.certify retry_replay l r out
      val _ = if Certificate.proof_count retry_replay=retry_count andalso
          Thm.eq_thm (retry_theorem,warm) then ()
        else error "Zip retry or warm-parent reuse lost its checked theorem"
      val replay = Certificate.make ctxt left_store right_store out_store combine
        (equation ctxt combine)
      val theorem = Certificate.certify replay l r out
      val proof_count = Certificate.proof_count replay
      val repeated = Certificate.certify replay l r out
      val _ = if Certificate.proof_count replay=proof_count andalso
          Thm.eq_thm (theorem,repeated) then ()
        else error "Future zip repeated root rebuilt checked pair states"
      val reduced_replay = Certificate.make ctxt left_store right_store reduced_store zero
        (equation ctxt zero)
      val reduced_theorem = Certificate.certify reduced_replay l r reduced_root
      val wide_replay = Certificate.make ctxt left_store right_store wide_store combine
        (equation ctxt combine)
      val wide_theorem = Certificate.certify wide_replay
        (Store.action_index left_store left_wide) (Store.action_index right_store right_wide)
        (Store.action_index wide_store (hd (#roots wide)))
      val binary_replay = Certificate.make ctxt binary_left_store binary_right_store binary_store combine
        (equation ctxt combine)
      val binary_theorem = Certificate.certify binary_replay
        (Store.action_index binary_left_store binary_l) (Store.action_index binary_right_store binary_r)
        (Store.action_index binary_store (hd (#roots binary)))
      val _ = Comma_Proof_Dependency_Audit.require_native_clean ctxt
        "Future zip replay fixture" [theorem,reduced_theorem,wide_theorem,binary_theorem,retry_theorem,warm]
      fun rejects label attempt =
        (case Exn.capture attempt () of Exn.Exn _ => ()
        | Exn.Res _ => error ("Future zip replay accepted " ^ label))
      val _ = rejects "a foreign arena root" (fn () =>
        Store.action_index left_store foreign_root)
      val _ = rejects "a different radix vector" (fn () =>
        Certificate.make ctxt left_store right_store foreign_store combine
          (equation ctxt combine))
      fun assumed_equation a b c =
        Thm.assume (Thm.cterm_of ctxt (HOLogic.mk_Trueprop
          (HOLogic.mk_eq (combine $ nat a $ nat b,nat c))))
      val _ = rejects "a leaf equality with an open hypothesis" (fn () =>
        Certificate.certify
          (Certificate.make ctxt left_store right_store out_store combine assumed_equation)
          l r out)
      val wrong = Exn.capture (fn () => Certificate.certify
        (Certificate.make ctxt left_store right_store out_store zero (equation ctxt zero))
        l r out) ()
      val _ = (case wrong of Exn.Exn _ => ()
        | Exn.Res _ => error "Future zip replay accepted swapped leaf outputs")
    in lthy5 end
end
