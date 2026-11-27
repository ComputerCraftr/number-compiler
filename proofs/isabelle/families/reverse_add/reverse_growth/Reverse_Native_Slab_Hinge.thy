theory Reverse_Native_Slab_Hinge
  imports Reverse_Native_Slab_Growth_Clock
begin

text \<open>The first selected interior cell retains its exact physical
backward inlet.  This is the source-facing entry to the born-quiet hinge;
it does not yet establish the complete four-tick hinge.\<close>

theorem slab_outer_eighteen_first_interior:
  assumes valid: "valid_pair (18 # c # rest)"
  shows "step (18 # c # rest) ! 1 =
    reverse_native_slab_birth 18 c True
      (carry_apply (domain c) (carry_out False (rev rest)))"
proof -
  let ?source = "18 # c # rest"
  have outer: "hd ?source = 18" by simp
  have first: "carry_out False ?source"
    using slab_core_outer_forces_birth[OF valid] by simp
  have cbound: "c \<le> 18" and rbound: "\<forall>x\<in>set rest. x \<le> 18"
    using valid by (auto simp: valid_pair_def)
  have cell: "c < 19" using cbound by arith
  have suffix: "\<forall>x\<in>set rest. x < 19"
  proof
    fix x assume "x \<in> set rest"
    then have "x \<le> 18" using rbound by blast
    then show "x < 19" by arith
  qed
  have branch: "carry_out (carry_apply (domain c) (carry_out False [18])) rest"
    using first by (simp add: carry_out_def)
  have emit: "reverse_emit (reverse_left_fold [18]) c (reverse_right_fold rest) =
    growth_pair_step c (last [18]) (carry_bit (carry_out False [18]))
      (carry_bit (carry_apply (domain c) (carry_out False (rev rest))))"
    by (rule reverse_emit_growth_interior[OF _ suffix cell _ branch]) simp_all
  have scan: "reverse_emit (reverse_left_fold (take 1 ?source)) (?source ! 1)
      (reverse_right_fold (drop 2 ?source)) = step ?source ! 1"
    using slab_core_physical_scan[OF valid, of 1] by simp
  show ?thesis using emit scan
    by (simp add: reverse_native_slab_birth_def reverse_native_slab_digit_def
        growth_pair_step_def carry_out_def domain_def carry_bit_def)
qed

lemma slab_outer_nine_quiet_interior:
  assumes valid: "valid_pair (9 # u # tail)"
      and quiet: "\<not> carry_out False (9 # u # tail)"
  shows "\<not> carry_apply (domain u) (carry_out False (rev tail))"
    and "step (9 # u # tail) ! 1 =
      reverse_native_slab_quiet u False (carry_out False (rev tail))"
proof -
  let ?source = "9 # u # tail"
  let ?inlet = "carry_out False (rev tail)"
  have ubound: "u \<le> 18" and tbound: "\<forall>x\<in>set tail. x \<le> 18"
    using valid by (auto simp: valid_pair_def)
  have cell: "u < 19" using ubound by arith
  have suffix: "\<forall>x\<in>set tail. x < 19"
  proof
    fix x assume "x \<in> set tail"
    then have "x \<le> 18" using tbound by blast
    then show "x < 19" by arith
  qed
  have symmetric: "rev ?source = ?source" using valid by (simp add: valid_pair_def)
  have reverse_quiet: "\<not> carry_out False (rev ?source)"
    using quiet symmetric by simp
  have no_through: "\<not> carry_apply (domain u) ?inlet"
    using reverse_quiet by (simp add: carry_out_append carry_out_def domain_def)
  have branch: "\<not> carry_out (carry_apply (domain u) (carry_out False [9])) tail"
    using quiet by (simp add: carry_out_def)
  have emit: "reverse_emit (reverse_left_fold [9]) u (reverse_right_fold tail) =
    mirror_pair_step u (carry_bit (carry_out False [9])) (carry_bit ?inlet)"
    by (rule reverse_emit_no_growth_cell[OF _ suffix cell branch]) simp
  have scan: "reverse_emit (reverse_left_fold (take 1 ?source)) (?source ! 1)
      (reverse_right_fold (drop 2 ?source)) = step ?source ! 1"
    using slab_core_physical_scan[OF valid, of 1] by simp
  show "\<not> carry_apply (domain u) ?inlet" by (rule no_through)
  show "step ?source ! 1 = reverse_native_slab_quiet u False ?inlet"
    using emit scan by (simp add: reverse_native_slab_quiet_def
      reverse_native_slab_digit_def mirror_pair_step_def carry_out_def domain_def carry_bit_def)
qed

ML \<open>
  val checked = @{thms slab_outer_eighteen_first_interior slab_outer_nine_quiet_interior};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Reverse native slab hinge depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked
    then error "Skipped reverse native slab hinge proof" else ();
\<close>

end
