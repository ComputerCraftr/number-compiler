theory Reverse_Native_Slab_1011
  imports Reverse_Native_Slab_Hinge
begin

lemma slab_list_two_decompose:
  assumes "2 \<le> length xs"
  shows "xs = hd xs # xs ! 1 # drop 2 xs"
proof (cases xs)
  case Nil
  then show ?thesis using assms by simp
next
  case (Cons x tail)
  then show ?thesis using assms by (cases tail) simp_all
qed

theorem slab_outer_eighteen_second_quiet_clock:
  assumes valid: "valid_pair (18 # c # rest)"
      and quiet: "\<not> carry_out False (step (18 # c # rest))"
  shows "carry_out False (step (step (step (18 # c # rest))))"
proof -
  let ?s0 = "18 # c # rest"
  let ?s1 = "step ?s0"
  let ?s2 = "step ?s1"
  let ?s3 = "step ?s2"
  let ?i0 = "carry_out False (rev rest)"
  have outer0: "hd ?s0 = 18" by simp
  have first: "carry_out False ?s0"
    using slab_outer_eighteen_second_quiet_prefix(1)[OF valid outer0 quiet] .
  have third: "carry_out False ?s2"
    using slab_outer_eighteen_second_quiet_prefix(4)[OF valid outer0 quiet] .
  have outer1: "hd ?s1 = 9"
    using source_growth_edge_successor[of ?s0] first by simp
  have outer2: "hd ?s2 = 18"
    by (rule slab_outer_eighteen_second_quiet_prefix(3)[OF valid outer0 quiet])
  have valid1: "valid_pair ?s1" by (rule valid_pair_successor[OF valid])
  have valid2: "valid_pair ?s2" by (rule valid_pair_successor[OF valid1])
  have valid3: "valid_pair ?s3" by (rule valid_pair_successor[OF valid2])
  have nonempty2: "?s2 \<noteq> []" using valid2 by (simp add: valid_pair_def)
  have outer3: "hd ?s3 = 9"
    using source_growth_edge_successor[OF nonempty2 third] outer2 by simp
  have len1: "2 \<le> length ?s1" using first by (simp add: length_digits_exact)
  have len2: "2 \<le> length ?s2" using len1 by (simp add: length_digits_exact; arith)
  have len3: "2 \<le> length ?s3" using len2 by (simp add: length_digits_exact; arith)
  have split1: "?s1 = 9 # (?s1 ! 1) # drop 2 ?s1"
    using slab_list_two_decompose[OF len1] outer1 by simp
  have split2: "?s2 = 18 # (?s2 ! 1) # drop 2 ?s2"
    using slab_list_two_decompose[OF len2] outer2 by simp
  have split3: "?s3 = 9 # (?s3 ! 1) # drop 2 ?s3"
    using slab_list_two_decompose[OF len3] outer3 by simp
  let ?i1 = "carry_out False (rev (drop 2 ?s1))"
  let ?i2 = "carry_out False (rev (drop 2 ?s2))"
  have first_cell: "?s1 ! 1 = reverse_native_slab_birth 18 c True
      (carry_apply (domain c) ?i0)"
    by (rule slab_outer_eighteen_first_interior[OF valid])
  have valid1': "valid_pair (9 # (?s1 ! 1) # drop 2 ?s1)" using valid1 split1 by simp
  have quiet1': "\<not> carry_out False (9 # (?s1 ! 1) # drop 2 ?s1)" using quiet split1 by simp
  have stopped: "\<not> carry_apply (domain (?s1 ! 1)) ?i1"
    by (rule slab_outer_nine_quiet_interior(1)[OF valid1' quiet1'])
  have second_cell: "?s2 ! 1 = reverse_native_slab_quiet (?s1 ! 1) False ?i1"
    using slab_outer_nine_quiet_interior(2)[OF valid1' quiet1'] split1 by simp
  have cle: "c \<le> 18" using valid by (auto simp: valid_pair_def)
  have cbound: "c < 19" using cle by arith
  have quiet_birth: "\<not> carry_apply (domain (reverse_native_slab_birth 18 c True
      (carry_apply (domain c) ?i0))) ?i1"
    using stopped first_cell by simp
  have force: "9 < reverse_native_slab_birth 18 (?s2 ! 1) True
      (carry_apply (domain (?s2 ! 1)) ?i2)"
    using reverse_native_slab_born_quiet_forces_next_birth[OF cbound quiet_birth, of ?i2]
      first_cell second_cell by simp
  have valid2': "valid_pair (18 # (?s2 ! 1) # drop 2 ?s2)" using valid2 split2 by simp
  have third_cell: "?s3 ! 1 = reverse_native_slab_birth 18 (?s2 ! 1) True
      (carry_apply (domain (?s2 ! 1)) ?i2)"
    using slab_outer_eighteen_first_interior[OF valid2'] split2 by simp
  have gt: "9 < ?s3 ! 1" using force third_cell by simp
  show ?thesis by (rule slab_outer_nine_next_reset_forces_birth[OF valid3 split3 gt])
qed

ML \<open>
  val checked = @{thms slab_list_two_decompose slab_outer_eighteen_second_quiet_clock};
  val _ = if null (Thm_Deps.all_oracles checked) then () else error "Native slab 1011 oracle";
  val _ = if Thm_Deps.has_skip_proof checked then error "Skipped native slab 1011 proof" else ();
\<close>

end
