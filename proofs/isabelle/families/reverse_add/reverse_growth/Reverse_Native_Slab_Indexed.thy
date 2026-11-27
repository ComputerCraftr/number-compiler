theory Reverse_Native_Slab_Indexed
  imports Reverse_Native_Slab_Source_Transport
begin

theorem slab_core_physical_first_birth_at:
  assumes valid: "valid_pair source" and positive: "0 < i" and bound: "i < length source"
      and symbols: "reverse_native_slab_source_symbol (source ! (i - 1))"
        "reverse_native_slab_source_symbol (source ! i)"
      and growth: "carry_out False source"
  shows "step source ! i = slab_core_initial (source ! (i - 1) \<noteq> 18) (source ! i \<noteq> 18)"
proof -
  let ?before = "take (i - 1) source"
  let ?after = "drop (Suc i) source"
  have prior: "i - 1 < length source" using positive bound by arith
  have take: "take i source = ?before @ [source ! (i - 1)]"
    using take_Suc_conv_app_nth[OF prior] positive by simp
  have split: "source = ?before @ [source ! (i - 1), source ! i] @ ?after"
    using id_take_nth_drop[OF bound] take by simp
  have len: "length ?before + 1 = i" using positive bound by simp
  have valid': "valid_pair (?before @ [source ! (i - 1), source ! i] @ ?after)"
    using valid split by simp
  have growth': "carry_out False (?before @ [source ! (i - 1), source ! i] @ ?after)"
    using growth split by simp
  show ?thesis using slab_core_physical_first_birth_cell[OF valid' symbols growth'] split len by simp
qed

theorem slab_core_physical_step_at:
  assumes valid: "valid_pair source" and positive: "0 < i"
      and bound: "Suc i < length source"
      and core: "10 \<le> source ! (i - 1)" "10 \<le> source ! i" "10 \<le> source ! Suc i"
  shows "step source ! i = (if carry_out False source
    then slab_core_birth (source ! (i - 1)) (source ! i)
    else slab_core_quiet (source ! i))"
proof -
  let ?before = "take (i - 1) source"
  let ?after = "drop (Suc (Suc i)) source"
  have ibound: "i < length source" using bound by arith
  have prior: "i - 1 < length source" using positive ibound by arith
  have take1: "take i source = ?before @ [source ! (i - 1)]"
    using take_Suc_conv_app_nth[OF prior] positive by simp
  have take2: "take (Suc i) source = ?before @ [source ! (i - 1), source ! i]"
    using take_Suc_conv_app_nth[OF ibound] take1 by simp
  have split: "source = ?before @ [source ! (i - 1), source ! i, source ! Suc i] @ ?after"
    using id_take_nth_drop[OF bound] take2 by simp
  have len: "length ?before + 1 = i" using positive ibound by simp
  have valid': "valid_pair (?before @ [source ! (i - 1), source ! i, source ! Suc i] @ ?after)"
    using valid split by simp
  have cell_le: "source ! i \<le> 18" using valid ibound by (auto simp: valid_pair_def)
  have cell: "source ! i < 19" using cell_le by arith
  show ?thesis using slab_core_physical_step_cell[OF valid' core(1,2) cell core(3)] split len by simp
qed

ML \<open>
  val checked = @{thms slab_core_physical_first_birth_at slab_core_physical_step_at};
  val _ = if null (Thm_Deps.all_oracles checked) then () else error "Native slab index oracle";
  val _ = if Thm_Deps.has_skip_proof checked then error "Skipped native slab index proof" else ();
\<close>

end
