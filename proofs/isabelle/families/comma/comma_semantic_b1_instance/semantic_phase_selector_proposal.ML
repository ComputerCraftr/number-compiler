(* Untrusted, arena-local construction of reusable CRT phase selectors.
   The caller must certify the result before consuming the action. *)
structure Comma_Semantic_Phase_Selector =
struct
  structure Arena = Comma_CRT_MDD_Arena
  val radices = [3,4,7,11]
  val coefficients = [616,693,792,672]
  val periods = [1,2,3,6,22,28]

  type template =
    {period:int, offset:int, base:Arena.action_root, shifted:Arena.action_root,
     root:Arena.action_root, fallback:Arena.action_root,
     rows:(int * Arena.action_root) list}
  type owner =
    {arena:Arena.arena, bases:Arena.action_root Inttab.table Unsynchronized.ref,
     charts:template Termtab.table Unsynchronized.ref,
     base_builds:int Unsynchronized.ref, chart_builds:int Unsynchronized.ref,
     chart_hits:int Unsynchronized.ref, unsupported:int Unsynchronized.ref}
  type proposal = {shift:int, template:template}

  fun make arena : owner =
    if Arena.radices arena = radices then
      {arena=arena, bases=Unsynchronized.ref Inttab.empty,
       charts=Unsynchronized.ref Termtab.empty,
       base_builds=Unsynchronized.ref 0, chart_builds=Unsynchronized.ref 0,
       chart_hits=Unsynchronized.ref 0, unsupported=Unsynchronized.ref 0}
    else error "Phase selector requires CRT axes [3,4,7,11]"

  fun core_spec (Const (name,_)) =
        if name = @{const_name Comma_Core_1} then SOME (1,1)
        else if name = @{const_name Comma_Core_3} then SOME (3,1)
        else if name = @{const_name Comma_Core_7} then SOME (7,6)
        else if name = @{const_name Comma_Core_11} then SOME (11,2)
        else if name = @{const_name Comma_Core_13} then SOME (13,6)
        else if name = @{const_name Comma_Core_21} then SOME (21,6)
        else if name = @{const_name Comma_Core_23} then SOME (23,22)
        else if name = @{const_name Comma_Core_27} then SOME (27,3)
        else if name = @{const_name Comma_Core_29} then SOME (29,28)
        else NONE
    | core_spec _ = NONE

  fun power_mod modulus exponent =
    let
      fun loop 0 value = value
        | loop n value = loop (n-1) ((10*value) mod modulus)
    in if modulus = 1 then 0 else loop exponent 1 end

  (* Each coefficient is the CRT basis element for its axis.  A zero
     coefficient modulo the requested period makes that axis irrelevant. *)
  fun build_base arena period =
    let
      fun visit axis residue =
        if axis = length radices then Arena.action_some arena residue
        else
          let val radix = List.nth (radices,axis)
              val coefficient = List.nth (coefficients,axis) mod period
          in if coefficient = 0 then visit (axis+1) residue
             else Arena.action_branch arena axis
               (map (fn digit =>
                 visit (axis+1) ((residue + digit*coefficient) mod period))
                 (0 upto (radix-1)))
          end
    in visit 0 0 end

  fun base ({arena,bases,base_builds,...}:owner) period =
    (case Inttab.lookup (!bases) period of
      SOME root => root
    | NONE =>
        let
          val _ = if member (op =) periods period then ()
            else error "Unsupported phase selector period"
          val root = build_base arena period
          val reachable_period =
            (case period of 1 => 1 | 2 => 4 | 3 => 3 | 6 => 12
              | 22 => 44 | 28 => 28 | _ => error "Unsupported CRT phase period")
          val repeated = Arena.shift_action arena root reachable_period
          val _ = if Arena.action_index arena repeated = Arena.action_index arena root
            then () else error "Phase chart did not close at its reachable-axis period"
          val _ = bases := Inttab.update (period,root) (!bases)
          val _ = base_builds := !base_builds+1
        in root end)

  fun propose (owner as {arena,charts,chart_builds,chart_hits,unsupported,...}:owner)
      core shift wanted =
    let
      val _ = if shift >= 0 andalso List.all (fn value => value >= 0) wanted then ()
        else error "Phase selector requires nonnegative shift and labels"
      val _ = if length (distinct (op =) wanted) = length wanted then ()
        else error "Phase selector has duplicate wanted labels"
    in case core_spec core of
      NONE => (unsupported := !unsupported+1; NONE)
    | SOME (modulus,period) =>
        let
          val offset = ((shift mod period) + (919 mod period)) mod period
          val nat = HOLogic.mk_number @{typ nat}
          val key = HOLogic.mk_prod (core, HOLogic.mk_prod
            (nat offset, HOLogic.mk_list @{typ nat} (map nat wanted)))
          val template = (case Termtab.lookup (!charts) key of
            SOME cached =>
              let
                val _ = if #period cached=period andalso #offset cached=offset then ()
                  else error "Cached phase selector has different period or offset"
                val _ = ignore (Arena.action_index arena (#root cached))
                val _ = chart_hits := !chart_hits+1
              in cached end
          | NONE =>
              let
                val phase_root = base owner period
                val shifted = Arena.shift_action arena phase_root offset
                val fallback = Arena.action_none arena
                fun row slot =
                  let val value = power_mod modulus slot
                  in if member (op =) wanted value
                     then SOME (slot+1,Arena.action_some arena value)
                     else NONE end
                val rows = map_filter row (0 upto (period-1))
                val root = Arena.bind_action_to_action arena shifted fallback rows
                val built:template =
                  {period=period,offset=offset,base=phase_root,shifted=shifted,
                   root=root,fallback=fallback,rows=rows}
                val _ = charts := Termtab.update (key,built) (!charts)
                val _ = chart_builds := !chart_builds+1
              in built end)
        in SOME {shift=shift,template=template}:proposal option end
    end

  fun statistics ({base_builds,chart_builds,chart_hits,unsupported,...}:owner) =
    "phase_bases=" ^ Int.toString (!base_builds) ^
    " phase_charts=" ^ Int.toString (!chart_builds) ^
    " phase_chart_hits=" ^ Int.toString (!chart_hits) ^
    " phase_unclassified=" ^ Int.toString (!unsupported)
end
