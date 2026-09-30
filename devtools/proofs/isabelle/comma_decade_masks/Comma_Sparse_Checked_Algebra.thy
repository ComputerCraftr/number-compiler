theory Comma_Sparse_Checked_Algebra
  imports Comma_Sparse_Temporal_Composition
begin

unbundle bit_operations_syntax

text \<open>These certificates retain a mask scope while constructing sparse
rows. A scheduling hint is not a semantic premise: publication still requires
that the checked union of emitted scopes is the full phase mask. Exact stop
height and terminal kind form the complete label used by local OR merging.\<close>

definition comma_sparse_partial ::
  "(nat \<Rightarrow> comma_word_result) \<Rightarrow> nat \<Rightarrow> comma_sparse_word \<Rightarrow> bool" where
  "comma_sparse_partial F scope rows =
    ((\<forall>r. comma_phase_member scope r =
      (\<exists>out bits. (out,bits)\<in>set rows \<and> comma_phase_member bits r)) \<and>
     (\<forall>out bits r. (out,bits)\<in>set rows \<longrightarrow>
       comma_phase_member bits r \<longrightarrow> F r=out))"

lemma comma_sparse_partial_singleton:
  assumes "\<And>r. comma_phase_member bits r \<Longrightarrow> F r=out"
  shows "comma_sparse_partial F bits [(out,bits)]"
  using assms by (auto simp: comma_sparse_partial_def)

lemma comma_sparse_partial_value:
  assumes "comma_sparse_partial F bits [(out,bits)]" "comma_phase_member bits r"
  shows "F r=out"
  using assms by (auto simp: comma_sparse_partial_def)

lemma comma_sparse_partial_join:
  assumes "comma_sparse_partial F a A" "comma_sparse_partial F b B" "a OR b=c"
  shows "comma_sparse_partial F c (A@B)"
  using assms by (auto simp: comma_sparse_partial_def comma_phase_member_or; blast)

lemma comma_sparse_partial_merge:
  assumes "comma_sparse_partial F a [(out,a)]"
    "comma_sparse_partial F b [(out,b)]" "a OR b=c"
  shows "comma_sparse_partial F c [(out,c)]"
  apply (rule comma_sparse_partial_singleton)
  using assms comma_sparse_partial_value
  by (auto simp: comma_phase_member_or)

lemma comma_sparse_partial_full_refines:
  assumes "comma_sparse_partial F (mask 924) rows"
  shows "comma_sparse_refines F rows"
  using assms unfolding comma_sparse_partial_def comma_sparse_refines_def
    comma_sparse_has_def
  by (auto simp: comma_phase_full_mask; blast)

lemma comma_sparse_partial_first:
  assumes first: "comma_sparse_partial (\<lambda>r. A r i) bits [(out,bits)]"
    and stopped: "\<And>j. out\<noteq>Comma_Word_Live j"
  shows "comma_sparse_partial (\<lambda>r. comma_word_then n A B r i) bits [(out,bits)]"
proof (rule comma_sparse_partial_singleton)
  fix r assume "comma_phase_member bits r"
  then have "A r i=out" by (rule comma_sparse_partial_value[OF first])
  then show "comma_word_then n A B r i=out"
    using stopped by (cases out) (auto simp: comma_word_then_def)
qed

ML \<open>val _ = Comma_Fast_Kernel.report "sparse_algebra_partial_first_checked";\<close>

lemma comma_sparse_partial_live:
  assumes first: "comma_sparse_partial (\<lambda>r. A r i) a [(Comma_Word_Live j,a)]"
    and second: "comma_sparse_partial (\<lambda>r. B r j) b [(out,b)]"
    and mask: "a AND comma_rotate_phase n b=c"
  shows "comma_sparse_partial (\<lambda>r. comma_word_then n A B r i)
    c [(comma_sparse_shift n out,c)]"
proof (rule comma_sparse_partial_singleton)
  fix r assume "comma_phase_member c r"
  then have first_bit: "comma_phase_member a r"
    and rotated_bit: "comma_phase_member (comma_rotate_phase n b) r"
    by (auto simp: mask[symmetric] comma_phase_member_and)
  have phase: "r<924" using first_bit by (simp add: comma_phase_member_def)
  have tail_bit: "comma_phase_member b ((r+n) mod 924)"
    using rotated_bit phase by (simp add: comma_rotate_phase_member)
  have head: "A r i=Comma_Word_Live j"
    by (rule comma_sparse_partial_value[OF first first_bit])
  have tail: "B ((r+n) mod 924) j=out"
    by (rule comma_sparse_partial_value[OF second tail_bit])
  show "comma_word_then n A B r i=comma_sparse_shift n out"
    by (cases out) (simp_all add: comma_word_then_def head tail)
qed

ML \<open>val _ = Comma_Fast_Kernel.report "sparse_algebra_live_checked";\<close>

lemma comma_sparse_partial_orbit_square:
  assumes "comma_sparse_partial
    (\<lambda>r. comma_word_then (2^k) (comma_orbit_word k) (comma_orbit_word k) r i) bits rows"
  shows "comma_sparse_partial (\<lambda>r. comma_orbit_word (Suc k) r i) bits rows"
  using assms unfolding comma_sparse_partial_def
  by (intro conjI allI impI; use comma_orbit_word_square_all in
    \<open>auto simp: comma_phase_member_def\<close>)

lemma comma_sparse_partial_base:
  assumes index: "i<46"
    and exact: "comma_sector_rows_refine
      (comma_sector_mask_value 1 (comma_offset_representatives!i)) bits [(out,bits)]"
    and admitted: "comma_sector_base_admitted out"
  shows "comma_sparse_partial (\<lambda>r. comma_orbit_word 0 r i)
    bits [(comma_sector_base_project out,bits)]"
proof (rule comma_sparse_partial_singleton)
  fix r assume member: "comma_phase_member bits r"
  have phase: "r<924" using member by (simp add: comma_phase_member_def)
  have source: "comma_sector_mask_value 1 (comma_offset_representatives!i) r=out"
    using exact member by (auto simp: comma_sector_rows_refine_def)
  have offset: "comma_offset_representatives!i\<le>90"
    by (rule comma_orbit_representative_index(1)[OF index])
  have projected: "comma_sector_base_project out=
    comma_word_project comma_offset_orbit
      (comma_decade_block_atom (Comma_Decade r (comma_offset_representatives!i)))"
    by (rule comma_sector_base_project_refines[OF phase offset source admitted])
  show "comma_orbit_word 0 r i=comma_sector_base_project out"
    using phase index projected
    by (simp only: comma_orbit_word_def comma_decade_block_power.simps; simp)
qed

lemma comma_sparse_partial_height_cover:
  assumes rows: "comma_sparse_partial (\<lambda>r. comma_orbit_word k r i) (mask 924) word"
    and stops: "\<And>out bits. (out,bits)\<in>set word \<Longrightarrow>
      \<exists>h terminal. out=Comma_Word_Stop h terminal \<and> h\<le>26"
    and phase: "r<924"
  shows "\<exists>h terminal. comma_orbit_word k r i=Comma_Word_Stop h terminal \<and> h\<le>26"
proof -
  obtain out bits where member: "(out,bits)\<in>set word" "comma_phase_member bits r"
    using rows phase by (auto simp: comma_sparse_partial_def comma_phase_full_mask)
  have exact: "comma_orbit_word k r i=out"
    using rows member by (auto simp: comma_sparse_partial_def)
  show ?thesis using stops[OF member(1)] exact by blast
qed

ML \<open>val _ = Comma_Fast_Kernel.report "sparse_algebra_base_and_cover_checked";\<close>


definition comma_sparse_base_row_checked :: "nat \<Rightarrow> comma_sector_rows \<Rightarrow> bool" where
  "comma_sparse_base_row_checked i row =
    (comma_sector_rows_refine
      (comma_sector_mask_value 1 (comma_offset_representatives!i)) (mask 924) row \<and>
     list_all (\<lambda>(out,bits). comma_sector_base_admitted out) row)"

lemma comma_sparse_base_table_nil:
  "list_all2 comma_sparse_base_row_checked [] []"
  by simp

lemma comma_sparse_base_table_cons:
  assumes "comma_sparse_base_row_checked i row"
    "list_all2 comma_sparse_base_row_checked indices rows"
  shows "list_all2 comma_sparse_base_row_checked (i#indices) (row#rows)"
  using assms by simp

lemma comma_sparse_base_table_nth:
  assumes "list_all2 comma_sparse_base_row_checked [0..<46] rows" "i<46"
  shows "comma_sparse_base_row_checked i (rows!i)"
  using assms by (auto simp: list_all2_conv_all_nth)

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_sparse_partial_join comma_sparse_partial_merge
      comma_sparse_partial_live comma_sparse_partial_first
      comma_sparse_partial_orbit_square comma_sparse_partial_base
      comma_sparse_partial_height_cover}) then ()
    else error "Checked sparse row algebra depends on an oracle";
\<close>
end
