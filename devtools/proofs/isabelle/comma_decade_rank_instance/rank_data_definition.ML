structure Comma_Decade_Rank_Data =
struct
  fun define lthy =
    let
      val started = Time.now ()
      val numerals = Vector.tabulate (27, fn n =>
        (HOLogic.mk_number @{typ nat} n, n))
      val nodes = Unsynchronized.ref (Symtab.empty: (term * int) Symtab.table)
      val next = Unsynchronized.ref 27
      val hits = Unsynchronized.ref 0
      fun node level children =
        let val key = Int.toString level ^ ":" ^
          space_implode "," (map (Int.toString o #2) children)
        in case Symtab.lookup (!nodes) key of
          SOME result => (hits := !hits + 1; result)
        | NONE =>
            let
              val terms = map #1 children
              val element_type = fastype_of (hd terms)
              val result = (HOLogic.mk_list element_type terms, !next)
              val _ = next := !next + 1
              val _ = nodes := Symtab.update (key, result) (!nodes)
            in result end
        end
      fun split 0 xs acc = (rev acc, xs)
        | split _ [] acc = (rev acc, [])
        | split n (x :: xs) acc = split (n - 1) xs (x :: acc)
      fun chunks _ [] = []
        | chunks size xs =
            let val (front, rest) = split size xs []
            in front :: chunks size rest end
      fun parse row =
        let
          val ranks = map (fn c => Char.ord c - Char.ord #"A") (String.explode row)
          val _ = if length ranks = 91 andalso forall (fn n => 0 <= n andalso n < 27) ranks
            then () else error "Malformed untrusted decade rank row"
        in ranks @ replicate 5 0 end
      val _ = if length comma_decade_candidate_rows = 924 then ()
        else error "Incomplete untrusted decade rank candidates"
      val ranks = map parse comma_decade_candidate_rows @ replicate 100 (replicate 96 0)
      val rows = map (fn row => node 2
        (map (node 1 o map (fn n => Vector.sub (numerals, n))) (chunks 16 row))) ranks
      val groups = map (node 3) (chunks 16 rows)
      val quarters = map (node 4) (chunks 16 groups)
      val (body, _) = node 5 quarters
      val result = Local_Theory.define
        ((Binding.name "comma_decade_rank_codes", NoSyn),
          ((Binding.name "comma_decade_rank_codes_def", []), body)) lthy
      val _ = warning ("Typed rank data: nodes=" ^ Int.toString (!next - 27) ^
        " shared=" ^ Int.toString (!hits) ^ " milliseconds=" ^
        LargeInt.toString (Time.toMilliseconds (Time.- (Time.now (), started))))
    in #2 result end
end
