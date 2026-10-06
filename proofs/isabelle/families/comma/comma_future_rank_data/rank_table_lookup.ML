(* Future-rank callers use the shared proof-producing selected-list owner. *)
structure Comma_Future_Rank_Lookup =
struct
  fun selected_table_with_extents ctxt name codes_def table_pattern extents =
    let
      val {procedure, stats} = Comma_Selected_List_Conversion.make
        {ctxt = ctxt, name = "future_" ^ name,
         root_definition = codes_def, table_pattern = table_pattern,
         extents = extents}
    in (procedure, stats) end

  fun selected_table ctxt name codes_def =
    let
      val pattern =
        (case name of
          "N" => @{term "comma_rank_codes_N ! i"}
        | "Z" => @{term "comma_rank_codes_Z ! i"}
        | _ => error "Unknown future rank table")
    in selected_table_with_extents ctxt name codes_def pattern [2,16,16,16] end
end
