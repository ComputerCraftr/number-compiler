theory Comma_Fast_Kernel_Smoke
  imports Comma_Fast_Kernel
begin

text \<open>Receiving occurrences keep exact theorem statements. Complete local
jumps share short phases; decade results retain their receiving phase/source.
The reference unfolds the previous sector semantics without the jump cache.\<close>

local_setup \<open>fn lthy =>
  let
    val forbid_children = Unsynchronized.ref false
    val engine = Comma_Fast_Kernel.make_with_transport
      (fn name => fn _ =>
        if name="sector_target" then error "Entry jump reopened the sector wrapper"
        else if !forbid_children andalso name<>"decade" then
          error "Warm parent reopened a child proof owner"
        else NONE) lthy
    val reference = Comma_Fast_Kernel.context lthy
      delsimps @{thms comma_fast_entry_round_jump}
    fun nat n = HOLogic.mk_number @{typ nat} n
    fun request fuel phase offset = @{term comma_fast_round_aux} $ nat fuel $ nat phase $
      (@{term Comma_Entry} $ nat 1 $ nat 0 $ nat offset)
    fun evaluate term = Simplifier.rewrite (#context engine) (Thm.cterm_of lthy term)
    fun headroom residue delta = @{term comma_finite_headroom_fast} $
      nat 1 $ nat residue $ nat delta $ nat 17
    fun check term =
      let
        val actual = evaluate term
        val expected = Simplifier.rewrite reference (Thm.cterm_of lthy term)
        val _ = if Thm.term_of (Thm.lhs_of actual) aconv term andalso
          Thm.term_of (Thm.rhs_of actual) aconv Thm.term_of (Thm.rhs_of expected)
          then () else error "Jump cache disagrees with the independent sector evaluator"
      in actual end
    fun counter name = the (AList.lookup (op =) (#measurements engine ()) name)
    val headroom0 = evaluate (headroom 0 17)
    val headroom_before = counter "headroom"
    val headroom_affine = evaluate (headroom 1 16)
    val headroom_periodic = evaluate (headroom 924 17)
    val headroom_after = counter "headroom"
    val headroom_rhs = Thm.term_of (Thm.rhs_of headroom0)
    val _ = if #misses headroom_after = #misses headroom_before andalso
      #hits headroom_after >= #hits headroom_before + 2 andalso
      Thm.term_of (Thm.rhs_of headroom_affine) aconv headroom_rhs andalso
      Thm.term_of (Thm.rhs_of headroom_periodic) aconv headroom_rhs andalso
      null (Thm_Deps.all_oracles [headroom0,headroom_affine,headroom_periodic])
      then () else error "Affine headroom quotient lost its endpoint or cache reuse"
    fun decade phase = @{term comma_fast_decade_control} $
      (@{term Comma_Decade} $ nat phase $ nat 0)
    val first = check (decade 0)
    val prior = #measurements engine ()
    val _ = forbid_children := true
    val repeated = evaluate (decade 0)
    val _ = forbid_children := false
    val after = #measurements engine ()
    val _ = if map (fn (name,work) => (name,#misses work)) prior =
        map (fn (name,work) => (name,#misses work)) after andalso
        #hits (counter "decade") > 0 andalso
        Thm.prop_of first aconv Thm.prop_of repeated then ()
      else error "Warm parent repeated child construction or changed its source"
    val jump_before = #misses (counter "entry_jump")
    val shifted = check (decade 924)
    val _ = if #misses (counter "entry_jump") = jump_before andalso
      not (Thm.term_of (Thm.lhs_of first) aconv Thm.term_of (Thm.lhs_of shifted))
      then () else error "Absolute phase leaked into local jump identity"
    val examples = map (fn (fuel,phase,offset) => check (request fuel phase offset))
      [(0,0,0),(1,0,0),(9,1,0),(9,22,1),(9,923,98)]
    val _ = if null (Thm_Deps.all_oracles (first::shifted::examples)) then ()
      else error "Jump cache smoke depends on an oracle"
    val _ = Comma_Fast_Kernel.report ("jump_cache_smoke " ^ #stats engine ())
  in #2 (Local_Theory.note
    ((Binding.name "comma_jump_cache_checked", []), first::shifted::examples) lthy) end\<close>

ML \<open>
  val _ = if null (Thm_Deps.all_oracles @{thms comma_jump_cache_checked}) then ()
    else error "Published jump cache checks depend on an oracle";
\<close>

end
