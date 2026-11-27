(* Request-local structural Bellman terminal projection.  Every returned root
   is untrusted until the receiving Store replays mapped-shift certificates. *)
structure Comma_Direct_Bellman_Terminal_Proposal =
struct
  structure Arena = Comma_CRT_MDD_Arena
  structure Utils = Comma_CRT_MDD_Proof_Utils
  val natT = @{typ nat}
  type continued = {target:int,source:Arena.action_root,output:Arena.action_root}
  fun make arena roots =
    let
      val _ = if Arena.radices arena = [3,4,7,11] andalso length roots=46 then ()
        else error "Bellman terminal projection needs 46 CRT roots"
      val _ = List.app (fn root => ignore (Arena.action_index arena root)) roots
      val invalid = Arena.action_some arena 242
      val mapped_shift = Arena.make_action_shift_map arena (Arena.Shift_Add 9)
      val continuations = Unsynchronized.ref (Inttab.empty: continued Inttab.table)
      val requests = Unsynchronized.ref 0
      val hits = Unsynchronized.ref 0
      fun constant n = if n=0 then Arena.action_none arena else Arena.action_some arena (n-1)
      fun continue target =
        (case Inttab.lookup (!continuations) target of
          SOME item => (hits := !hits + 1; #output item)
        | NONE =>
            let
              val source = List.nth (roots,target)
              val output = Arena.shift_map_action mapped_shift source 1
              val item = {target=target,source=source,output=output}
              val _ = continuations := Inttab.update (target,item) (!continuations)
            in output end)
      fun terminal requested_arena expression shift =
        let
          val _ = ignore (Arena.action_index requested_arena invalid)
          val _ = if shift >= 0 then () else error "Negative Bellman application shift"
          val _ = requests := !requests + 1
          val (head,args) = strip_comb expression
          val name = (case head of Const (n,_) => n | _ => error "Malformed direct terminal")
          fun num label term = Utils.dest_nat label natT term
        in
          if name = @{const_name Comma_Direct_Invalid} andalso null args then SOME invalid
          else if name = @{const_name Comma_Direct_Continue} then
            (case args of [t,d] =>
              let val target = num "Continue target" t and delta = num "Continue delta" d
              in SOME (if target<46 andalso (delta+shift) mod 924 = 1
                then continue target else invalid) end
            | _ => error "Malformed Bellman Continue")
          else if name = @{const_name Comma_Direct_Fork} then
            (case args of [d,k] =>
              let val digit = num "Fork digit" d and delta = num "Fork delta" k
              in SOME (if 2<=digit andalso digit<=9 andalso shift+delta=0
                then constant (digit-2) else invalid) end
            | _ => error "Malformed Bellman Fork")
          else if name = @{const_name Comma_Direct_Landmine} then
            (case args of [k] => SOME (if shift + num "Landmine delta" k = 0
              then constant 8 else invalid)
            | _ => error "Malformed Bellman Landmine")
          else NONE
        end
      fun snapshot () = map #2 (Inttab.dest (!continuations))
      fun statistics () = "bellman_terminal_requests=" ^ Int.toString (!requests) ^
        " bellman_continue_actions=" ^ Int.toString (Inttab.size (!continuations)) ^
        " bellman_continue_hits=" ^ Int.toString (!hits)
    in {terminal=terminal,fallback=invalid,continuations=snapshot,statistics=statistics} end
end
