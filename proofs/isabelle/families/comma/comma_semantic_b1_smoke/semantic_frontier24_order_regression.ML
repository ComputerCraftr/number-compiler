(* Differential proposal regression; theorem authority remains with the
   universally quantified core_guard_phase_eval theorem. *)
structure Comma_Frontier24_Order_Regression =
struct
  structure Data = Comma_Frontier24_Data
  fun n i = Data.nat_of_integer (IntInf.fromInt i)
  fun int value = IntInf.toInt (Data.integer_of_nat value)
  val cores = [Data.Comma_Core_1, Data.Comma_Core_3, Data.Comma_Core_7,
    Data.Comma_Core_11, Data.Comma_Core_13, Data.Comma_Core_21,
    Data.Comma_Core_23, Data.Comma_Core_27, Data.Comma_Core_29]
  val radices = Vector.fromList [3,4,7,11]
  fun check core wanted =
    let
      val nodes = Vector.fromList (Data.comma_frontier24_core_guard_nodes core (n wanted))
      val root = int (Data.comma_frontier24_core_guard_root core)
      val modulus = Data.comma_phase_core_modulus core
      fun eval phase remaining index =
        if remaining = 0 orelse index < 0 orelse index >= Vector.length nodes
        then error "Frontier24 guard regression: malformed graph"
        else case Vector.sub (nodes,index) of
          Data.Comma_CRT_MDD_Leaf value => value
        | Data.Comma_CRT_MDD_Branch (axis,children) =>
            let
              val a = int axis
              val _ = if a >= 0 andalso a < Vector.length radices then ()
                else error "Frontier24 guard regression: invalid axis"
              val radix = Vector.sub (radices,a)
              val _ = if length children = radix then ()
                else error "Frontier24 guard regression: invalid branch width"
            in eval phase (remaining-1) (int (List.nth (children,phase mod radix))) end
      fun phase p =
        if eval p (Vector.length nodes) root =
          (* The clock guard is the recursive core action at the shifted
             exponent p+919, not the unshifted occurrence coordinate. *)
          (int (Data.comma_recursive_core_residue modulus (n (p+919))) = wanted)
        then () else error "Frontier24 guard regression: phase mismatch"
    in List.app phase (0 upto 923) end
  val _ = List.app (fn core =>
    List.app (check core o int) (Data.comma_core_supported_values core)) cores
end
