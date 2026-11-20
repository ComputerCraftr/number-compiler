(* Exercise interval joins with a source-independent finite graph. *)
structure Comma_Future_M204_Class_Rank_Fixture =
struct
  fun run lthy =
    let
      val terminal = (~1, [], SOME 0)
      val rows = replicate 17 terminal @ [(2, [0,1], SOME 1)]
      val (published,lthy') = Comma_Future_M204_Class_Rank.publish_rows
        "m204_interval_fixture" rows lthy
      val ctxt = Local_Theory.target_of lthy'
      val _ = Comma_Proof_Dependency_Audit.require_native_clean ctxt
        "M204 interval fixture" [#rows_checked published,#rank published]
      fun reject name bad =
        (case Exn.capture (fn () =>
            Comma_Future_M204_Class_Rank.publish_rows name bad lthy') () of
          Exn.Exn (ERROR _) => ()
        | Exn.Exn (THM _) => ()
        | Exn.Exn exn => Exn.reraise exn
        | Exn.Res _ => error "Invalid M204 fixture graph was accepted")
      val _ = reject "m204_interval_bad_rank"
        (replicate 17 terminal @ [(2,[0,1],SOME 0)])
      val _ = reject "m204_interval_bad_child"
        (replicate 17 terminal @ [(2,[0,18],SOME 1)])
    in lthy' end
end
