(* Bounded exact-term storage for completed results and partial markers. *)
structure Comma_Semantic_B1_Term_LRU =
struct
  datatype 'a publication = Added | Existing | Refused

  type 'a state =
   {values: 'a Termtab.table,
    partials: unit Termtab.table,
    stamps: int Termtab.table,
    order: term Inttab.table,
    clock: int,
    oldest: int,
    hits: int,
    misses: int,
    evictions: int,
    refusals: int}

  type 'a cache = {capacity: int, state: 'a state Synchronized.var}

  fun state values partials stamps order clock oldest hits misses evictions refusals =
    {values = values, partials = partials, stamps = stamps, order = order,
     clock = clock, oldest = oldest, hits = hits, misses = misses,
     evictions = evictions, refusals = refusals}

  fun make name capacity : 'a cache =
    if capacity <= 0 then error "B1 exact-term LRU capacity must be positive"
    else {capacity = capacity,
      state = Synchronized.var ("semantic_b1_term_lru_" ^ name)
        (state Termtab.empty Termtab.empty Termtab.empty Inttab.empty 0 0 0 0 0 0)}

  fun advance_oldest clock order start =
    let
      fun seek age =
        if age >= clock then age
        else
          (case Inttab.lookup order age of
            SOME _ => age
          | NONE => seek (age + 1))
    in seek start end

  fun touch_state (key: term) (old: 'a state) =
    (case Termtab.lookup (#stamps old) key of
      NONE => error "B1 exact-term LRU lost a retained key stamp"
    | SOME previous =>
        let
          val age = #clock old
          val order1 = Inttab.update (age, key)
            (Inttab.delete previous (#order old))
          val stamps1 = Termtab.update (key, age)
            (Termtab.delete key (#stamps old))
          val clock1 = age + 1
          val oldest1 = if previous = #oldest old
            then advance_oldest clock1 order1 (previous + 1)
            else #oldest old
        in state (#values old) (#partials old) stamps1 order1 clock1 oldest1
          (#hits old + 1) (#misses old) (#evictions old) (#refusals old) end)

  fun evict_state (old: 'a state) =
    let
      val oldest = advance_oldest (#clock old) (#order old) (#oldest old)
    in
      (case Inttab.lookup (#order old) oldest of
        NONE => NONE
      | SOME key =>
          (case Termtab.lookup (#stamps old) key of
            NONE => error "B1 exact-term LRU order index has no key stamp"
          | SOME age =>
              if age <> oldest then
                error "B1 exact-term LRU order index disagrees with key stamp"
              else
                let
                  val order1 = Inttab.delete oldest (#order old)
                  val stamps1 = Termtab.delete key (#stamps old)
                  val values1 = Termtab.delete key (#values old)
                  val oldest1 = advance_oldest (#clock old) order1 (oldest + 1)
                in SOME (state values1 (#partials old) stamps1 order1
                  (#clock old) oldest1 (#hits old) (#misses old)
                  (#evictions old + 1) (#refusals old)) end))
    end

  fun lookup ({state = cache, ...}: 'a cache) key =
    Synchronized.change_result cache (fn old =>
      (case Termtab.lookup (#values old) key of
        NONE => (NONE, state (#values old) (#partials old) (#stamps old)
          (#order old) (#clock old) (#oldest old) (#hits old) (#misses old + 1)
          (#evictions old) (#refusals old))
      | SOME value => (SOME value, touch_state key old)))

  fun insert_completed ({capacity, state = cache}: 'a cache) key value =
    Synchronized.change_result cache (fn old =>
      let
        val partials1 = Termtab.delete_safe key (#partials old)
        val old1 = state (#values old) partials1 (#stamps old) (#order old)
          (#clock old) (#oldest old) (#hits old) (#misses old)
          (#evictions old) (#refusals old)
      in
        if Termtab.defined (#values old1) key then
          let
            val touched = touch_state key old1
            val values1 = Termtab.update (key, value) (#values touched)
          in (Existing, state values1 (#partials touched) (#stamps touched)
            (#order touched) (#clock touched) (#oldest touched)
            (#hits touched) (#misses touched) (#evictions touched)
            (#refusals touched)) end
        else
          let
            val occupied = Termtab.size (#values old1) + Termtab.size partials1
            val slot = if occupied < capacity then SOME old1 else evict_state old1
          in
            (case slot of
              NONE => (Refused, state (#values old1) partials1 (#stamps old1)
                (#order old1) (#clock old1) (#oldest old1) (#hits old1)
                (#misses old1) (#evictions old1) (#refusals old1 + 1))
            | SOME room =>
                let
                  val age = #clock room
                  val values1 = Termtab.update (key, value) (#values room)
                  val stamps1 = Termtab.update (key, age) (#stamps room)
                  val order1 = Inttab.update (age, key) (#order room)
                in (Added, state values1 (#partials room) stamps1 order1
                  (age + 1) (#oldest room) (#hits room) (#misses room)
                  (#evictions room) (#refusals room)) end)
          end
      end)

  fun remember_partial ({capacity, state = cache}: 'a cache) key =
    Synchronized.change_result cache (fn old =>
      if Termtab.defined (#values old) key then (false, old)
      else if Termtab.defined (#partials old) key then (true, old)
      else if Termtab.size (#values old) + Termtab.size (#partials old) < capacity
      then (true, state (#values old) (Termtab.update (key, ()) (#partials old))
        (#stamps old) (#order old) (#clock old) (#oldest old)
        (#hits old) (#misses old) (#evictions old) (#refusals old))
      else (false, state (#values old) (#partials old) (#stamps old) (#order old)
        (#clock old) (#oldest old) (#hits old) (#misses old) (#evictions old)
        (#refusals old + 1)))

  fun contains_completed ({state = cache, ...}: 'a cache) key =
    Termtab.defined (#values (Synchronized.value cache)) key

  fun contains_partial ({state = cache, ...}: 'a cache) key =
    Termtab.defined (#partials (Synchronized.value cache)) key

  fun clear_partial ({state = cache, ...}: 'a cache) key =
    Synchronized.change cache (fn old => state (#values old)
      (Termtab.delete_safe key (#partials old)) (#stamps old) (#order old)
      (#clock old) (#oldest old) (#hits old) (#misses old)
      (#evictions old) (#refusals old))

  fun completed_size ({state = cache, ...}: 'a cache) =
    Termtab.size (#values (Synchronized.value cache))
  fun partial_size ({state = cache, ...}: 'a cache) =
    Termtab.size (#partials (Synchronized.value cache))
  fun hits ({state = cache, ...}: 'a cache) = #hits (Synchronized.value cache)
  fun misses ({state = cache, ...}: 'a cache) = #misses (Synchronized.value cache)
  fun evictions ({state = cache, ...}: 'a cache) = #evictions (Synchronized.value cache)
  fun refusals ({state = cache, ...}: 'a cache) = #refusals (Synchronized.value cache)

  fun clear ({state = cache, ...}: 'a cache) = Synchronized.change cache (fn _ =>
    state Termtab.empty Termtab.empty Termtab.empty Inttab.empty 0 0 0 0 0 0)

  fun check_fixture () =
    let
      val cache = make "fixture" 2
      val a = Free ("lru_a", HOLogic.boolT)
      val b = Free ("lru_b", HOLogic.boolT)
      val c = Free ("lru_c", HOLogic.boolT)
      val d = Free ("lru_d", HOLogic.boolT)
      val _ = if insert_completed cache a 1 = Added andalso
          insert_completed cache b 2 = Added andalso lookup cache a = SOME 1 andalso
          insert_completed cache c 3 = Added andalso lookup cache b = NONE andalso
          lookup cache a = SOME 1 andalso lookup cache c = SOME 3 andalso
          insert_completed cache d 4 = Added andalso lookup cache a = NONE andalso
          lookup cache c = SOME 3 andalso lookup cache d = SOME 4 andalso
          completed_size cache = 2 andalso evictions cache = 2
        then () else error "B1 bounded exact-term LRU refresh/eviction fixture failed"
      val partial_only = make "partial-fixture" 2
      val _ = if remember_partial partial_only a andalso
          remember_partial partial_only b andalso
          not (remember_partial partial_only c) andalso
          lookup partial_only a = NONE andalso insert_completed partial_only a 1 = Added andalso
          not (contains_partial partial_only a) andalso
          contains_completed partial_only a andalso partial_size partial_only = 1 andalso
          refusals partial_only = 1
        then () else error "B1 partial-marker/capacity LRU fixture failed"
    in () end
end

val _ = Comma_Semantic_B1_Term_LRU.check_fixture ()
