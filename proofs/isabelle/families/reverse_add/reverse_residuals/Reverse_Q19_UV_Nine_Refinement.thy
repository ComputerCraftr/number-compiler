theory Reverse_Q19_UV_Nine_Refinement
  imports Reverse_Q19_UV_Contraction Reverse_Q19_UV_Six_Phase Reverse_Ordered_Carry_Gram
begin

text \<open>The source guard authenticates ordered tiles, both inlet ports and
the three physical entry steps.  The protected tail then composes six
physical actions from separately checked fringe and core receipts.\<close>

lemma uv_stage3_has_protected_form:
  "uv_stage3 xs @ [10] =
    uv_protected_half (34 * length xs + 16) uv_protected_head3 2 uv_protected_tail3"
proof -
  have head: "uv_protected_head3 = [8,7,11] @ replicate 9 2"
    by (simp add: uv_protected_head3_def eval_nat_numeral)
  have tail: "uv_protected_tail3 = replicate 7 2 @ [3,10]"
    by (simp add: uv_protected_tail3_def eval_nat_numeral)
  have middle: "replicate 9 (2::nat) @ replicate (34 * length xs + 16) 2 @ replicate 7 2 =
      replicate (34 * length xs + 32) 2"
    by (simp only: replicate_add[symmetric]) (simp add: algebra_simps)
  have protected:
    "uv_protected_half (34 * length xs + 16) uv_protected_head3 2 uv_protected_tail3 =
      [8,7,11] @ (replicate 9 2 @ replicate (34 * length xs + 16) 2 @ replicate 7 2) @ [3,10]"
    by (simp only: uv_protected_half_def head tail append_assoc)
  show ?thesis by (simp only: uv_stage3_explicit protected middle)
qed

theorem uv_source_nine_physical_steps:
  "run step 9 (uv_stage0 xs b @ rev (uv_stage0 xs b)) =
    uv_protected_field
      (uv_protected_half (34 * length xs + 16) uv_protected_head9 2 uv_protected_tail9)
      [12]"
proof -
  have nine: "(9::nat) = Suc (Suc (Suc 6))" by simp
  have entry: "(uv_stage3 xs @ [10]) @ rev (uv_stage3 xs @ [10]) =
    uv_protected_field
      (uv_protected_half (34 * length xs + 16) uv_protected_head3 2 uv_protected_tail3) []"
    by (simp add: uv_stage3_has_protected_form uv_protected_field_def)
  show ?thesis
    by (simp only: nine run.simps uv_actual_three_steps entry uv_protected_six_physical_ticks)
qed

theorem uv_guard_nine_ordered_gram:
  fixes z :: "'a::comm_ring_1"
  assumes accepted: "fold (uv_next uv_source_u uv_source_v) encoded ScanStart = ScanAccept"
  shows "\<exists>xs b. encoded = [19] @ uv_stage0 xs b @ [21] \<and>
    (let original = uv_stage0 xs b @ rev (uv_stage0 xs b);
         field = uv_protected_field
           (uv_protected_half (34 * length xs + 16) uv_protected_head9 2 uv_protected_tail9)
           [12]
     in run step 9 original = field \<and>
        carry_out a (map gram_domain_representative (run step 9 original)) = carry_out a field \<and>
        carry_out b' (rev (map gram_domain_representative (run step 9 original))) =
          carry_out b' (rev field) \<and>
        gram_sum z (length field)
          (\<lambda>i. f (gram_ports a b' (map gram_domain_representative (run step 9 original)) i)) =
          gram_sum z (length field) (\<lambda>i. f (gram_ports a b' field i)) \<and>
        gram_sum z (length field - 1)
          (\<lambda>i. h (gram_ports a b' (map gram_domain_representative (run step 9 original)) i)
            (gram_ports a b' (map gram_domain_representative (run step 9 original)) (Suc i))) =
          gram_sum z (length field - 1)
            (\<lambda>i. h (gram_ports a b' field i) (gram_ports a b' field (Suc i))) \<and>
        gram_sum z (length field - 1)
          (\<lambda>i. h (gram_ports a b' (map gram_domain_representative (run step 9 original)) (Suc i))
            (gram_ports a b' (map gram_domain_representative (run step 9 original)) i)) =
          gram_sum z (length field - 1)
            (\<lambda>i. h (gram_ports a b' field (Suc i)) (gram_ports a b' field i)))"
proof -
  obtain xs b where source: "encoded = [19] @ uv_stage0 xs b @ [21]"
    using uv_guard_source_half[OF accepted] by blast
  show ?thesis
    by (intro exI[of _ xs] exI[of _ b])
      (simp add: source uv_source_nine_physical_steps Let_def rev_map)
qed

ML \<open>
  val checked = @{thms uv_source_nine_physical_steps uv_guard_nine_ordered_gram};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "U/V nine-tick Gram refinement depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked then
    error "U/V nine-tick Gram refinement has skipped proofs" else ();
\<close>

end
