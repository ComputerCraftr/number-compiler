theory Reverse_Native_Slab_Source_Transport
  imports Reverse_Native_Slab_Clock_Guard
begin

text \<open>The first core birth is selected from the same physical source,
with the exact global carry and both reset coefficients.  The remaining
collar induction must apply this boundary to an entire interior interval.\<close>

theorem slab_core_physical_first_birth_cell:
  assumes valid: "valid_pair (before @ [left, s] @ after)"
      and source: "reverse_native_slab_source_symbol left"
        "reverse_native_slab_source_symbol s"
      and growth: "carry_out False (before @ [left, s] @ after)"
  shows "step (before @ [left, s] @ after) ! (length before + 1) =
    slab_core_initial (left \<noteq> 18) (s \<noteq> 18)"
proof -
  let ?source = "before @ [left, s] @ after"
  let ?i = "length before + 1"
  have positive: "0 < ?i" by simp
  have index: "?i < length ?source" by simp
  have admitted: "\<forall>x\<in>set ?source. x < 19"
  proof
    fix x assume "x \<in> set ?source"
    then have "x \<le> 18" using valid by (auto simp: valid_pair_def)
    then show "x < 19" by arith
  qed
  have prefix: "\<forall>x\<in>set (before @ [left]). x < 19" using admitted by auto
  have suffix: "\<forall>x\<in>set after. x < 19" using admitted by auto
  have branch: "carry_out
    (carry_apply (domain s) (carry_out False (before @ [left]))) after"
    using growth by (simp add: carry_out_append carry_out_def)
  have selected: "reverse_emit (reverse_left_fold (before @ [left])) s
      (reverse_right_fold after) = slab_core_initial (left \<noteq> 18) (s \<noteq> 18)"
    by (rule slab_core_first_selected_birth[OF prefix suffix source branch])
  show ?thesis using slab_core_physical_scan[OF valid positive index] selected
    by (simp add: nth_append take_append drop_append)
qed

lemma slab_core_first_birth_source_negative:
  "\<not> reverse_native_slab_source_symbol 9"
  "reverse_native_slab_birth 8 17 False True = 16"
  "reverse_native_slab_birth 8 17 False False \<noteq> 16"
  "reverse_native_slab_birth 8 17 True False = 16"
  by (simp_all add: reverse_native_slab_source_symbol_def
      reverse_native_slab_birth_def reverse_native_slab_digit_def carry_bit_def)

ML \<open>
  val checked = @{thms slab_core_physical_first_birth_cell slab_core_first_birth_source_negative};
  val _ = if null (Thm_Deps.all_oracles checked) then () else error "Native slab source transport oracle";
  val _ = if Thm_Deps.has_skip_proof checked then error "Skipped native slab source transport proof" else ();
\<close>

end
