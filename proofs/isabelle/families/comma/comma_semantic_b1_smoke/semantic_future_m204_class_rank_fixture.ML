(* Exercise interval joins with a source-independent finite graph. *)
structure Comma_Future_M204_Class_Rank_Fixture =
struct
  fun run lthy =
    let
      val terminal = (~1, [], SOME 0)
      val graph = replicate 17 (~1, []) @ [(2, [0,1]), (2, [17,18])]
      val rows = Comma_Future_M204_Graph_Reachability.derive graph
      val expected = replicate 17 terminal @ [(2, [0,1], SOME 1), (2, [17,18], NONE)]
      val _ = if rows = expected then () else error "Future reachability changed ordered ranks"
      val full_graph = map (fn (control,children,_) => (control,children))
        Comma_Future_M204_Graph_Data.rows
      val _ = if Comma_Future_M204_Graph_Reachability.derive full_graph =
          Comma_Future_M204_Graph_Data.rows then ()
        else error "Derived Future reachability differs from bounded regression data"
      fun reject_graph graph =
        (case Exn.capture Comma_Future_M204_Graph_Reachability.derive graph of
           Exn.Exn (ERROR _) => ()
         | Exn.Exn exn => Exn.reraise exn
         | Exn.Res _ => error "Invalid Future reachability graph was accepted")
      val _ = reject_graph [(2,[1,0])]
      val _ = reject_graph [(2,[0,0])]
      val _ = reject_graph [(~1,[0])]
      val (published,lthy') = Comma_Future_M204_Class_Rank.publish_rows
        "m204_interval_fixture" rows lthy
      val (swapped,lthy'') = Comma_Future_M204_Class_Rank.publish_rows
        "m204_interval_swapped_fixture"
        (Comma_Future_M204_Graph_Reachability.derive
          (replicate 17 (~1, []) @ [(2,[1,0]),(2,[18,17])])) lthy'
      val ctxt = Local_Theory.target_of lthy''
      val selected = #lookup (#selector published) 17
      val selected_swapped = #lookup (#selector swapped) 17
      val _ = if Thm.term_of (Thm.rhs_of selected) aconv Thm.term_of (Thm.rhs_of selected_swapped)
        then error "Ordered Future child swaps shared the same row" else ()
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
      val _ = reject "m204_interval_multiple_unranked_children"
        (replicate 17 terminal @ [(2,[17,17],NONE)])
      val _ = reject "m204_interval_no_unranked_child"
        (replicate 17 terminal @ [(2,[0,1],NONE)])
    in lthy'' end
end
