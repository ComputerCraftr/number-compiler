theory Reverse_Native_Slab_Clock_Guard
  imports Reverse_Native_Slab_1011
begin

text \<open>The clock is selected by the exact valid source, not supplied as
an independent width word.  The two accepted orders each have three births.\<close>

theorem slab_outer_eighteen_physical_clock_admitted:
  assumes valid: "valid_pair (18 # c # rest)"
  shows "slab_core_clock_admitted
    [carry_out False (18 # c # rest),
     carry_out False (step (18 # c # rest)),
     carry_out False (step (step (18 # c # rest))),
     carry_out False (step (step (step (18 # c # rest))))]"
proof (cases "carry_out False (step (18 # c # rest))")
  case True
  have bits: "carry_out False (18 # c # rest)"
    "carry_out False (step (step (18 # c # rest)))"
    "\<not> carry_out False (step (step (step (18 # c # rest))))"
    using slab_outer_eighteen_second_birth_clock[OF valid _ True] by simp_all
  show ?thesis using bits True by (simp add: slab_core_clock_admitted_def)
next
  case False
  have bits: "carry_out False (18 # c # rest)"
    "carry_out False (step (step (18 # c # rest)))"
    using slab_outer_eighteen_second_quiet_prefix[OF valid _ False] by simp_all
  have fourth: "carry_out False (step (step (step (18 # c # rest))))"
    by (rule slab_outer_eighteen_second_quiet_clock[OF valid False])
  show ?thesis using bits False fourth by (simp add: slab_core_clock_admitted_def)
qed

ML \<open>
  val checked = @{thms slab_outer_eighteen_physical_clock_admitted};
  val _ = if null (Thm_Deps.all_oracles checked) then () else error "Native slab clock oracle";
  val _ = if Thm_Deps.has_skip_proof checked then error "Skipped native slab clock proof" else ();
\<close>

end
