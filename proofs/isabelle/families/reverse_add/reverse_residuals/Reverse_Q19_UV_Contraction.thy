theory Reverse_Q19_UV_Contraction
  imports Reverse_Q19_UV_Piece Reverse_Q19_UV_Admission
begin

text \<open>The source half has a fixed head, a word of rotated U/V pieces,
and a fixed tail.  Each piece transports both actual inlets and the
birth-alignment digit through each physical pass.\<close>

definition uv_common :: "nat list" where
  "uv_common = [1,9,5,9,1,3,7,3]"

definition uv_other :: "nat list" where
  "uv_other = [1,9,5,9,5,9,1,3,7,3]"

definition uv_source_u :: "nat list" where
  "uv_source_u = uv_common @ uv_common @ uv_other @ uv_common"

definition uv_source_v :: "nat list" where
  "uv_source_v = uv_common @ uv_other @ uv_common @ uv_common"

definition uv_head0 :: "nat list" where
  "uv_head0 = [17] @ uv_common"

definition uv_u0 :: "nat list" where
  "uv_u0 = drop 8 uv_source_u @ uv_common"

definition uv_tail_u0 :: "nat list" where
  "uv_tail_u0 = drop 8 uv_source_u @ [11]"

definition uv_v0 :: "nat list" where
  "uv_v0 = drop 8 uv_source_v @ uv_common"

definition uv_tail_v0 :: "nat list" where
  "uv_tail_v0 = drop 8 uv_source_v @ [11]"

definition uv_head1 :: "nat list" where
  "uv_head1 = [8,9,10,14,14,10,4,10,10]"

definition uv_u1 :: "nat list" where
  "uv_u1 = [4,10,14,14,10,4,10,10,4,10,14,14,14,14,10,4,10,10,4,10,14,14,10,4,10,10,4,10,14,14,10,4,10,10]"

definition uv_tail_u1 :: "nat list" where
  "uv_tail_u1 = [4,10,14,14,10,4,10,10,4,10,14,14,14,14,10,4,10,10,4,10,14,14,10,4,10,10,5]"

definition uv_v1 :: "nat list" where
  "uv_v1 = [4,10,14,14,14,14,10,4,10,10,4,10,14,14,10,4,10,10,4,10,14,14,10,4,10,10,4,10,14,14,10,4,10,10]"

definition uv_tail_v1 :: "nat list" where
  "uv_tail_v1 = [4,10,14,14,14,14,10,4,10,10,4,10,14,14,10,4,10,10,4,10,14,14,10,4,10,10,5]"

definition uv_head2 :: "nat list" where
  "uv_head2 = [17,9,1,10,10,1,10,1,1]"

definition uv_u2 :: "nat list" where
  "uv_u2 = [10,1,10,10,1,10,1,1,10,1,10,10,10,10,1,10,1,1,10,1,10,10,1,10,1,1,10,1,10,10,1,10,1,1]"

definition uv_tail_u2 :: "nat list" where
  "uv_tail_u2 = [10,1,10,10,1,10,1,1,10,1,10,10,10,10,1,10,1,1,10,1,10,10,1,10,1,1,11]"

definition uv_v2 :: "nat list" where
  "uv_v2 = [10,1,10,10,10,10,1,10,1,1,10,1,10,10,1,10,1,1,10,1,10,10,1,10,1,1,10,1,10,10,1,10,1,1]"

definition uv_tail_v2 :: "nat list" where
  "uv_tail_v2 = [10,1,10,10,10,10,1,10,1,1,10,1,10,10,1,10,1,1,10,1,10,10,1,10,1,1,11]"

definition uv_pick :: "nat list \<Rightarrow> nat list \<Rightarrow> bool \<Rightarrow> nat list" where
  "uv_pick u v b = (if b then v else u)"

definition uv_head3 :: "nat list" where
  "uv_head3 = [8,7,11] @ map (\<lambda>_. 2) (take 6 uv_u0)"

definition uv_tail3 :: "nat list" where
  "uv_tail3 = map (\<lambda>_. 2) (take 26 uv_u0) @ [3]"

definition uv_twos :: "bool \<Rightarrow> nat list" where
  "uv_twos b = map (\<lambda>_. 2) (uv_pick uv_u2 uv_v2 b)"

lemma uv_head_length [simp]:
  "length uv_head0 = 9" "length uv_head1 = 9" "length uv_head2 = 9"
  by (simp_all add: uv_head0_def uv_head1_def uv_head2_def uv_common_def)

lemma uv_middle_lengths [simp]:
  "length (uv_pick uv_u0 uv_v0 b) = 34"
  "length (uv_pick uv_u1 uv_v1 b) = 34"
  "length (uv_pick uv_u2 uv_v2 b) = 34"
  "length (uv_twos b) = 34"
  by (cases b; simp_all add: uv_pick_def uv_twos_def uv_u0_def uv_v0_def
      uv_u1_def uv_v1_def uv_u2_def uv_v2_def uv_source_u_def uv_source_v_def
      uv_common_def uv_other_def)+

lemma uv_head_receipts:
  "uv_piece True (False,True,1) uv_head0 (False,False,3) uv_head1"
  "uv_piece False (False,False,0) uv_head1 (True,False,0) uv_head2"
  "uv_piece True (False,True,1) uv_head2 (False,True,2) uv_head3"
  by (simp_all add: uv_piece_def uv_head0_def uv_head1_def uv_head2_def
      uv_head3_def uv_u0_def uv_source_u_def uv_common_def uv_other_def uv_after_def carry_out_def domain_def Let_def)

lemma uv_middle_receipts:
  "uv_piece True (False,False,3) (uv_pick uv_u0 uv_v0 b)
     (False,False,3) (uv_pick uv_u1 uv_v1 b)"
  "uv_piece False (True,False,0) (uv_pick uv_u1 uv_v1 b)
     (True,False,0) (uv_pick uv_u2 uv_v2 b)"
  "uv_piece True (False,True,2) (uv_pick uv_u2 uv_v2 b)
     (False,True,2) (uv_twos b)"
  by (cases b; simp_all add: uv_piece_def uv_pick_def uv_twos_def
      uv_u0_def uv_v0_def uv_u1_def uv_v1_def uv_u2_def uv_v2_def
      uv_source_u_def uv_source_v_def uv_common_def uv_other_def
      uv_after_def carry_out_def domain_def Let_def)+

lemma uv_tail_receipts:
  "uv_piece True (False,False,3) (uv_pick uv_tail_u0 uv_tail_v0 b)
     (True,True,2) (uv_pick uv_tail_u1 uv_tail_v1 b)"
  "uv_piece False (True,False,0) (uv_pick uv_tail_u1 uv_tail_v1 b)
     (False,False,0) (uv_pick uv_tail_u2 uv_tail_v2 b)"
  "uv_piece True (False,True,2) (uv_pick uv_tail_u2 uv_tail_v2 b)
     (True,False,1) uv_tail3"
  by (cases b; simp_all add: uv_piece_def uv_pick_def uv_tail3_def
      uv_tail_u0_def uv_tail_v0_def uv_tail_u1_def uv_tail_v1_def
      uv_tail_u2_def uv_tail_v2_def uv_u0_def uv_source_u_def uv_source_v_def
      uv_common_def uv_other_def uv_after_def carry_out_def domain_def Let_def)+

lemma uv_piece_list:
  assumes action: "\<And>x. uv_piece grow p (f x) p (g x)"
  shows "uv_piece grow p (concat (map f xs)) p (concat (map g xs))"
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  show ?case using uv_piece_join[OF action[of a] Cons.IH] by simp
qed

definition uv_stage0 :: "bool list \<Rightarrow> bool \<Rightarrow> nat list" where
  "uv_stage0 xs b = uv_head0 @ concat (map (uv_pick uv_u0 uv_v0) xs) @ uv_pick uv_tail_u0 uv_tail_v0 b"

definition uv_stage1 :: "bool list \<Rightarrow> bool \<Rightarrow> nat list" where
  "uv_stage1 xs b = uv_head1 @ concat (map (uv_pick uv_u1 uv_v1) xs) @ uv_pick uv_tail_u1 uv_tail_v1 b"

definition uv_stage2 :: "bool list \<Rightarrow> bool \<Rightarrow> nat list" where
  "uv_stage2 xs b = uv_head2 @ concat (map (uv_pick uv_u2 uv_v2) xs) @ uv_pick uv_tail_u2 uv_tail_v2 b"

definition uv_stage3 :: "bool list \<Rightarrow> nat list" where
  "uv_stage3 xs = uv_head3 @ concat (map uv_twos xs) @ uv_tail3"

theorem uv_stages_receipts:
  "uv_piece True (False,True,1) (uv_stage0 xs b)
     (True,True,2) (uv_stage1 xs b)"
  "uv_piece False (False,False,0) (uv_stage1 xs b)
     (False,False,0) (uv_stage2 xs b)"
  "uv_piece True (False,True,1) (uv_stage2 xs b)
     (True,False,1) (uv_stage3 xs)"
proof -
  have mid0: "uv_piece True (False,False,3)
      (concat (map (uv_pick uv_u0 uv_v0) xs)) (False,False,3)
      (concat (map (uv_pick uv_u1 uv_v1) xs))"
    by (rule uv_piece_list) (rule uv_middle_receipts(1))
  have head0: "uv_piece True (False,True,1)
      (uv_head0 @ concat (map (uv_pick uv_u0 uv_v0) xs)) (False,False,3)
      (uv_head1 @ concat (map (uv_pick uv_u1 uv_v1) xs))"
    by (rule uv_piece_join[OF uv_head_receipts(1) mid0])
  show "uv_piece True (False,True,1) (uv_stage0 xs b)
      (True,True,2) (uv_stage1 xs b)"
    using uv_piece_join[OF head0 uv_tail_receipts(1)[of b]]
    by (simp add: uv_stage0_def uv_stage1_def append_assoc)
  have mid1: "uv_piece False (True,False,0)
      (concat (map (uv_pick uv_u1 uv_v1) xs)) (True,False,0)
      (concat (map (uv_pick uv_u2 uv_v2) xs))"
    by (rule uv_piece_list) (rule uv_middle_receipts(2))
  have head1: "uv_piece False (False,False,0)
      (uv_head1 @ concat (map (uv_pick uv_u1 uv_v1) xs)) (True,False,0)
      (uv_head2 @ concat (map (uv_pick uv_u2 uv_v2) xs))"
    by (rule uv_piece_join[OF uv_head_receipts(2) mid1])
  show "uv_piece False (False,False,0) (uv_stage1 xs b)
      (False,False,0) (uv_stage2 xs b)"
    using uv_piece_join[OF head1 uv_tail_receipts(2)[of b]]
    by (simp add: uv_stage1_def uv_stage2_def append_assoc)
  have mid2: "uv_piece True (False,True,2)
      (concat (map (uv_pick uv_u2 uv_v2) xs)) (False,True,2)
      (concat (map uv_twos xs))"
    by (rule uv_piece_list) (rule uv_middle_receipts(3))
  have head2: "uv_piece True (False,True,1)
      (uv_head2 @ concat (map (uv_pick uv_u2 uv_v2) xs)) (False,True,2)
      (uv_head3 @ concat (map uv_twos xs))"
    by (rule uv_piece_join[OF uv_head_receipts(3) mid2])
  show "uv_piece True (False,True,1) (uv_stage2 xs b)
      (True,False,1) (uv_stage3 xs)"
    using uv_piece_join[OF head2 uv_tail_receipts(3)[of b]]
    by (simp add: uv_stage2_def uv_stage3_def append_assoc)
qed

theorem uv_actual_three_steps:
  "step (uv_stage0 xs b @ rev (uv_stage0 xs b)) =
       uv_stage1 xs b @ [4] @ rev (uv_stage1 xs b)"
  "step (uv_stage1 xs b @ [4] @ rev (uv_stage1 xs b)) =
       uv_stage2 xs b @ [8] @ rev (uv_stage2 xs b)"
  "step (uv_stage2 xs b @ [8] @ rev (uv_stage2 xs b)) =
       (uv_stage3 xs @ [10]) @ rev (uv_stage3 xs @ [10])"
proof -
  have n0: "uv_stage0 xs b \<noteq> []"
    by (simp add: uv_stage0_def uv_head0_def)
  have n2: "uv_stage2 xs b \<noteq> []"
    by (simp add: uv_stage2_def uv_head2_def)
  show "step (uv_stage0 xs b @ rev (uv_stage0 xs b)) =
       uv_stage1 xs b @ [4] @ rev (uv_stage1 xs b)"
    by (rule uv_piece_birth_even[OF uv_stages_receipts(1) n0])
  show "step (uv_stage1 xs b @ [4] @ rev (uv_stage1 xs b)) =
       uv_stage2 xs b @ [8] @ rev (uv_stage2 xs b)"
    by (rule uv_piece_quiet_odd[OF uv_stages_receipts(2)])
  show "step (uv_stage2 xs b @ [8] @ rev (uv_stage2 xs b)) =
       (uv_stage3 xs @ [10]) @ rev (uv_stage3 xs @ [10])"
    by (rule uv_piece_birth_odd[OF uv_stages_receipts(3) n2])
qed

definition uv_source_tile :: "bool \<Rightarrow> nat list" where
  "uv_source_tile b = uv_pick uv_source_u uv_source_v b"

definition uv_suffix :: "bool \<Rightarrow> nat list" where
  "uv_suffix b = take 26 (uv_pick uv_u0 uv_v0 b)"

lemma uv_source_layout:
  "uv_head0 = [17] @ uv_common"
  "uv_source_tile b = uv_common @ uv_suffix b"
  "uv_pick uv_u0 uv_v0 b = uv_suffix b @ uv_common"
  "uv_pick uv_tail_u0 uv_tail_v0 b = uv_suffix b @ [11]"
  by (cases b; simp_all add: uv_head0_def uv_common_def uv_source_tile_def
      uv_source_u_def uv_source_v_def uv_suffix_def uv_pick_def uv_u0_def uv_v0_def
      uv_tail_u0_def uv_tail_v0_def uv_common_def uv_other_def)+

lemma uv_rotated_word:
  "uv_common @ concat (map (\<lambda>x. uv_suffix x @ uv_common) xs) @ uv_suffix b =
   concat (map (\<lambda>x. uv_common @ uv_suffix x) (xs@[b]))"
  by (induction xs) (simp_all add: append_assoc)

lemma uv_stage0_source:
  "uv_stage0 xs b = [17] @ concat (map uv_source_tile (xs@[b])) @ [11]"
proof -
  have mid: "uv_pick uv_u0 uv_v0 = (\<lambda>x. uv_suffix x @ uv_common)"
    by (rule ext) (rule uv_source_layout(3))
  have source: "uv_source_tile = (\<lambda>x. uv_common @ uv_suffix x)"
    by (rule ext) (rule uv_source_layout(2))
  show ?thesis
    unfolding uv_stage0_def uv_source_layout(1,4) mid source
    using uv_rotated_word[of xs b] by (metis append_assoc)
qed

lemma uv_source_tile_lengths [simp]:
  "length uv_source_u = 34" "length uv_source_v = 34"
  by (simp_all add: uv_source_u_def uv_source_v_def uv_common_def uv_other_def)

lemma uv_source_tile_distinct [simp]:
  "uv_source_u \<noteq> uv_source_v"
  by (simp add: uv_source_u_def uv_source_v_def uv_common_def uv_other_def)

lemma uv_flags_from_tiles:
  assumes "set ts \<subseteq> {uv_source_u, uv_source_v}"
  shows "map uv_source_tile (map (\<lambda>t. t=uv_source_v) ts) = ts"
  using assms
  by (induction ts) (auto simp: uv_source_tile_def uv_pick_def)

theorem uv_guard_source_half:
  assumes accepted: "fold (uv_next uv_source_u uv_source_v) encoded ScanStart = ScanAccept"
  shows "\<exists>xs b. encoded = [19] @ uv_stage0 xs b @ [21]"
proof -
  obtain ts where tiles: "ts \<noteq> []" "set ts \<subseteq> {uv_source_u, uv_source_v}"
    "encoded = [19,17] @ concat ts @ [11,21]"
    using uv_guard_accepts_only_ordered_tiles[OF uv_source_tile_lengths accepted] by blast
  let ?bs = "map (\<lambda>t. t=uv_source_v) ts"
  have bs_nonempty: "?bs \<noteq> []" using tiles(1) by simp
  obtain xs b where bs: "?bs = xs @ [b]"
    using bs_nonempty by (cases ?bs rule: rev_exhaust) auto
  have decoded: "map uv_source_tile (xs@[b]) = ts"
    using uv_flags_from_tiles[OF tiles(2)] bs by simp
  show ?thesis
    using tiles(3) decoded uv_stage0_source[of xs b]
    by (intro exI[of _ xs] exI[of _ b]) (simp add: append_assoc)
qed

lemma uv_map_constant:
  "map (\<lambda>_. c) xs = replicate (length xs) c"
  by (induction xs) simp_all

lemma uv_twos_replicate [simp]:
  "uv_twos b = replicate 34 2"
  using uv_middle_lengths(3)[of b]
  by (simp add: uv_twos_def uv_map_constant)

lemma uv_concat_twos:
  "concat (map uv_twos xs) = replicate (34 * length xs) 2"
  by (induction xs) (simp_all add: replicate_add mult_Suc)

lemma uv_stage3_explicit:
  "uv_stage3 xs @ [10] =
    [8,7,11] @ replicate (34 * length xs + 32) 2 @ [3,10]"
proof -
  have pre: "map (\<lambda>_. (2::nat)) (take 6 uv_u0) = replicate 6 2"
    by (simp add: uv_map_constant uv_u0_def uv_source_u_def uv_common_def uv_other_def eval_nat_numeral)
  have post: "map (\<lambda>_. (2::nat)) (take 26 uv_u0) = replicate 26 2"
    by (simp add: uv_map_constant uv_u0_def uv_source_u_def uv_common_def uv_other_def eval_nat_numeral)
  have middle: "replicate 6 (2::nat) @ replicate (34 * length xs) 2 @ replicate 26 2 =
      replicate (34 * length xs + 32) 2"
    by (simp only: replicate_add[symmetric]) (simp add: algebra_simps)
  have expanded: "uv_stage3 xs @ [10] =
      [8,7,11] @ (replicate 6 2 @ replicate (34 * length xs) 2 @ replicate 26 2) @ [3,10]"
    by (simp only: uv_stage3_def uv_head3_def uv_tail3_def uv_concat_twos
        pre post append_assoc append_Cons append_Nil)
  show ?thesis using expanded middle by simp
qed


theorem uv_guard_physical_three_steps:
  assumes accepted: "fold (uv_next uv_source_u uv_source_v) encoded ScanStart = ScanAccept"
  shows "\<exists>xs b. encoded = [19] @ uv_stage0 xs b @ [21] \<and>
    run step 3 (uv_stage0 xs b @ rev (uv_stage0 xs b)) =
      (uv_stage3 xs @ [10]) @ rev (uv_stage3 xs @ [10])"
proof -
  obtain xs b where encoded: "encoded = [19] @ uv_stage0 xs b @ [21]"
    using uv_guard_source_half[OF accepted] by blast
  have three: "(3::nat) = Suc (Suc (Suc 0))" by simp
  have steps: "run step 3 (uv_stage0 xs b @ rev (uv_stage0 xs b)) =
      (uv_stage3 xs @ [10]) @ rev (uv_stage3 xs @ [10])"
    by (simp only: three run.simps uv_actual_three_steps)
  show ?thesis using encoded steps by blast
qed

ML \<open>
  val checked = @{thms uv_stages_receipts uv_actual_three_steps
    uv_guard_source_half uv_guard_physical_three_steps};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "U/V contraction depends on an oracle";
  val _ = if not (Thm_Deps.has_skip_proof checked) then ()
    else error "U/V contraction has skipped proofs";
\<close>

end
