(* Untrusted constructor checks; semantic authority comes from kernel replay. *)
structure Comma_CRT_MDD_Priority_Fixture =
struct
  structure Arena = Comma_CRT_MDD_Arena

  fun run () =
    let
      val arena = Arena.create [3,4,7,11]
      val no = Arena.boolean_false arena
      val yes = Arena.boolean_true arena
      val guard = Arena.boolean_branch arena 0 [no,yes,no]
      val first = Arena.action_some arena 2
      val second = Arena.action_some arena 5
      val fallback = Arena.action_none arena
      val (root,key) = Arena.priority_select arena [(guard,first),(yes,second)] fallback
      val _ = (case Arena.priority_witness arena key of
          {step=Arena.Priority_Branch (0,children),...} =>
            if length children=3 then () else error "Priority fixture has wrong branch arity"
        | _ => error "Priority fixture did not publish the expected branch")
      val _ = (case Arena.action_view arena root of Arena.Branch_At (0,children) =>
          if length children=3 andalso List.nth (children,0)=List.nth (children,2) andalso
              List.nth (children,0)<>List.nth (children,1) then ()
          else error "Priority fixture selected incorrect children"
        | _ => error "Priority fixture result is not the expected branch")
      val (first_root,first_key) = Arena.priority_select arena [(yes,first),(yes,second)] fallback
      val _ = if Arena.action_index arena first_root = Arena.action_index arena first
        then () else error "Priority fixture did not choose the first true guard"
      val _ = (case #step (Arena.priority_witness arena first_key) of
          Arena.Priority_Fallback => () | _ => error "Priority fixture did not normalize true guard")
      val (default_root,default_key) = Arena.priority_select arena [(no,first)] fallback
      val _ = (case #step (Arena.priority_witness arena default_key) of
          Arena.Priority_Fallback => () | _ => error "Priority fixture did not remove false guard")
      val _ = if Arena.action_index arena default_root = Arena.action_index arena fallback
        then () else error "Priority fixture did not retain fallback"
      val _ = (case Exn.capture (fn () => Arena.action_as_boolean arena first) () of
          Exn.Exn exn => if String.isSubstring "non-Boolean" (Runtime.exn_message exn)
            then () else Exn.reraise exn
        | Exn.Res _ => error "Priority fixture accepted a non-Boolean guard")
      val foreign = Arena.create [3,4,7,11]
      val _ = (case Exn.capture (fn () => Arena.priority_select arena
            [(Arena.boolean_true foreign,first)] fallback) () of
          Exn.Exn exn => if String.isSubstring "another arena" (Runtime.exn_message exn)
            then () else Exn.reraise exn
        | Exn.Res _ => error "Priority fixture accepted a foreign guard")
    in () end

end
