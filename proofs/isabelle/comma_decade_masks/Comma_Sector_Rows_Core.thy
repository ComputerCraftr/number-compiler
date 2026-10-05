theory Comma_Sector_Rows_Core
  imports Comma_Sector_Response_Check
    "HOL-Library.List_Lexorder"
begin

ML_file "../shared/proof_profile.ML"
ML \<open>val comma_sector_rows_core_checkpoint =
  Comma_Proof_Profile.timer "Sector rows core"\<close>

unbundle bit_operations_syntax

text \<open>This theory owns the generic row representation, semantic transport
laws, and a proof-producing list-spine conversion shared by row producers. It
contains no family-specific producer or semantic authority.\<close>

type_synonym comma_sector_rows = "(comma_round_result \<times> nat) list"

text \<open>A shared, label-parametric row normalizer. Rows are sorted by a
caller-supplied injective natural-list key, then equal adjacent labels are
merged by OR and zero masks are pruned. The observer theorem is independent
of the chosen ordering key; the key supplies deterministic, near-linear
normalization rather than semantic authority.\<close>

definition comma_mask_rows_has :: "('a \<times> nat) list \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> bool" where
  "comma_mask_rows_has rows r out =
    (\<exists>bits. (out,bits)\<in>set rows \<and> comma_phase_member bits r)"

function comma_mask_rows_merge_sorted :: "('a::equal \<times> nat) list \<Rightarrow> ('a \<times> nat) list" where
  "comma_mask_rows_merge_sorted [] = []"
| "comma_mask_rows_merge_sorted [(out,bits)] = [(out,bits)]"
| "comma_mask_rows_merge_sorted ((out,bits)#(out',bits')#rows) =
    (if out=out' then
       comma_mask_rows_merge_sorted ((out,bits OR bits')#rows)
     else
       (out,bits)#comma_mask_rows_merge_sorted ((out',bits')#rows))"
  by pat_completeness auto
termination by (relation "measure length") auto

ML \<open>val _ = comma_sector_rows_core_checkpoint "merge-proof-start"\<close>

lemma comma_mask_rows_merge_sorted_has:
  "comma_mask_rows_has (comma_mask_rows_merge_sorted rows) r out =
    comma_mask_rows_has rows r out"
proof (induction rows arbitrary: r out rule: comma_mask_rows_merge_sorted.induct
    [case_names empty single join])
  case empty
  then show ?case by (simp add: comma_mask_rows_has_def)
next
  case (single label bits)
  then show ?case by (simp add: comma_mask_rows_has_def)
next
  case (join label bits label' bits' rows)
  show ?case
  proof (cases "label=label'")
    case True
    have ih:
      "comma_mask_rows_has
          (comma_mask_rows_merge_sorted ((label,bits OR bits')#rows)) r out =
        comma_mask_rows_has ((label,bits OR bits')#rows) r out"
      by (rule join.IH(1)[OF True])
    show ?thesis using ih
      by (auto simp: comma_mask_rows_merge_sorted.simps
        comma_mask_rows_has_def comma_phase_member_or True)
  next
    case False
    have ih:
      "comma_mask_rows_has
          (comma_mask_rows_merge_sorted ((label',bits')#rows)) r out =
        comma_mask_rows_has ((label',bits')#rows) r out"
      by (rule join.IH(2)[OF False])
    show ?thesis using ih
      by (auto simp: comma_mask_rows_merge_sorted.simps
        comma_mask_rows_has_def False)
  qed
qed

ML \<open>val _ = comma_sector_rows_core_checkpoint "merge-refinement"\<close>

function comma_mask_rows_merge ::
  "('a \<Rightarrow> nat list) \<Rightarrow> ('a \<times> nat) list \<Rightarrow>
    ('a \<times> nat) list \<Rightarrow> ('a \<times> nat) list" where
  "comma_mask_rows_merge label_key [] right = right"
| "comma_mask_rows_merge label_key left [] = left"
| "comma_mask_rows_merge label_key (left#lefts) (right#rights) =
    (if label_key (fst left) \<le> label_key (fst right)
     then left # comma_mask_rows_merge label_key lefts (right#rights)
     else right # comma_mask_rows_merge label_key (left#lefts) rights)"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(label_key,left,right). length left + length right)") auto

lemma comma_mask_rows_merge_set:
  "set (comma_mask_rows_merge label_key left right) = set left \<union> set right"
  by (induction label_key left right rule: comma_mask_rows_merge.induct)
    (auto split: if_splits)

lemma comma_rows_take_half_strict:
  "length (take (length rows div 2) rows) < length rows"
  if "2 \<le> length rows"
  using that by (simp add: div_less_dividend)

lemma comma_rows_drop_half_strict:
  "length (drop (length rows div 2) rows) < length rows"
  if "2 \<le> length rows"
  using that by (simp add: div_2_gt_zero)

lemma comma_rows_take_drop_set:
  "set (take n rows) \<union> set (drop n rows) = set rows"
  by (metis append_take_drop_id set_append)

function comma_mask_rows_sort ::
  "('a \<Rightarrow> nat list) \<Rightarrow> ('a \<times> nat) list \<Rightarrow> ('a \<times> nat) list" where
  "comma_mask_rows_sort label_key [] = []"
| "comma_mask_rows_sort label_key [row] = [row]"
| "comma_mask_rows_sort label_key (first#second#rest) =
    comma_mask_rows_merge label_key
      (comma_mask_rows_sort label_key
        (take (length (first#second#rest) div 2) (first#second#rest)))
      (comma_mask_rows_sort label_key
        (drop (length (first#second#rest) div 2) (first#second#rest)))"
  by pat_completeness auto
termination
  apply (relation "measure (\<lambda>(label_key,rows). length rows)")
   apply (rule wf_measure)
   apply (simp only: in_measure split_beta snd_conv)
   apply (rule comma_rows_take_half_strict)
   apply simp
  apply (simp only: in_measure split_beta snd_conv)
  apply (rule comma_rows_drop_half_strict)
  apply simp
  done

lemma comma_mask_rows_sort_set:
  "set (comma_mask_rows_sort label_key rows) = set rows"
  by (induction label_key rows rule: comma_mask_rows_sort.induct)
    (simp_all add: comma_mask_rows_sort.simps comma_mask_rows_merge_set
      comma_rows_take_drop_set)

definition comma_mask_rows_prune :: "('a \<times> nat) list \<Rightarrow> ('a \<times> nat) list" where
  "comma_mask_rows_prune rows = filter (\<lambda>item. snd item\<noteq>0) rows"

lemma comma_mask_rows_prune_has:
  "comma_mask_rows_has (comma_mask_rows_prune rows) r out =
    comma_mask_rows_has rows r out"
proof -
  have nonzero: "comma_phase_member bits r \<Longrightarrow> bits\<noteq>0" for bits
    by (metis comma_phase_member_zero)
  show ?thesis
    by (auto simp: comma_mask_rows_prune_def comma_mask_rows_has_def
      dest: nonzero)
qed

definition comma_mask_rows_normalize :: "('a::equal \<Rightarrow> nat list) \<Rightarrow> ('a \<times> nat) list \<Rightarrow> ('a \<times> nat) list" where
  "comma_mask_rows_normalize label_key rows =
    comma_mask_rows_prune (comma_mask_rows_merge_sorted
      (comma_mask_rows_sort label_key rows))"

ML \<open>val _ = comma_sector_rows_core_checkpoint "normalizer-proof-start"\<close>

lemma comma_mask_rows_normalize_has:
  "comma_mask_rows_has (comma_mask_rows_normalize label_key rows) r out =
    comma_mask_rows_has rows r out"
  by (simp only: comma_mask_rows_normalize_def comma_mask_rows_prune_has
    comma_mask_rows_merge_sorted_has)
    (simp add: comma_mask_rows_has_def comma_mask_rows_sort_set)

definition comma_sector_rows_refine ::
  "(nat \<Rightarrow> comma_round_result) \<Rightarrow> nat \<Rightarrow> comma_sector_rows \<Rightarrow> bool" where
  "comma_sector_rows_refine F scope rows =
    ((\<forall>r. comma_phase_member scope r =
      (\<exists>out bits. (out,bits)\<in>set rows \<and> comma_phase_member bits r)) \<and>
     (\<forall>out bits r. (out,bits)\<in>set rows \<longrightarrow>
       comma_phase_member bits r \<longrightarrow> F r=out))"

definition comma_sector_mask_value :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> comma_round_result" where
  "comma_sector_mask_value f x r=comma_fast_round_aux (10-f) r (Comma_Entry f 0 x)"

definition comma_sector_rows_restrict :: "nat \<Rightarrow> comma_sector_rows \<Rightarrow> comma_sector_rows" where
  "comma_sector_rows_restrict guard rows=map (\<lambda>(out,bits). (out,guard AND bits)) rows"

definition comma_sector_rows_filter_nonzero :: "comma_sector_rows \<Rightarrow> comma_sector_rows" where
  "comma_sector_rows_filter_nonzero rows = filter (\<lambda>(out,bits). bits\<noteq>0) rows"

lemma comma_sector_rows_filter_restrict_empty:
  "comma_sector_rows_filter_nonzero (comma_sector_rows_restrict guard []) = []"
  by (simp add: comma_sector_rows_filter_nonzero_def comma_sector_rows_restrict_def)

lemma comma_sector_rows_filter_restrict_cons:
  "comma_sector_rows_filter_nonzero
      (comma_sector_rows_restrict guard ((out,bits)#rows)) =
    (if guard AND bits = 0 then
       comma_sector_rows_filter_nonzero (comma_sector_rows_restrict guard rows)
     else (out,guard AND bits)#
       comma_sector_rows_filter_nonzero (comma_sector_rows_restrict guard rows))"
  by (simp add: comma_sector_rows_filter_nonzero_def comma_sector_rows_restrict_def)

lemma comma_sector_rows_filter_restrict_zero:
  "comma_sector_rows_filter_nonzero (comma_sector_rows_restrict 0 rows) = []"
  by (induction rows)
    (auto simp: comma_sector_rows_filter_nonzero_def comma_sector_rows_restrict_def
      split: prod.splits)

ML \<open>val _ = comma_sector_rows_core_checkpoint "row-refinement-start"\<close>

lemma comma_sector_rows_singleton:
  assumes equation: "\<And>r. comma_phase_member scope r \<Longrightarrow> F r=out"
  shows "comma_sector_rows_refine F scope [(out,scope)]"
  using equation by (auto simp: comma_sector_rows_refine_def)

lemma comma_sector_rows_restrict_member:
  "(out,bits)\<in>set (comma_sector_rows_restrict guard rows) =
    (\<exists>old. (out,old)\<in>set rows \<and> bits=guard AND old)"
proof
  assume member: "(out,bits)\<in>set (comma_sector_rows_restrict guard rows)"
  then obtain item where item: "item\<in>set rows"
    "(out,bits)=(case item of (a,b) \<Rightarrow> (a,guard AND b))"
    unfolding comma_sector_rows_restrict_def by auto
  obtain a b where pair: "item=(a,b)" by (cases item) auto
  have equal: "out=a" "bits=guard AND b" using item(2) by (simp_all add: pair)
  show "\<exists>old. (out,old)\<in>set rows \<and> bits=guard AND old"
    apply (rule exI[where x=b])
    using item(1) equal by (simp add: pair)
next
  assume "\<exists>old. (out,old)\<in>set rows \<and> bits=guard AND old"
  then obtain old where old: "(out,old)\<in>set rows" "bits=guard AND old" by blast
  have image: "(out,bits)\<in>
    (\<lambda>(a,b). (a,guard AND b)) ` set rows"
    apply (rule image_eqI[where x="(out,old)"])
     using old(2) apply simp
    using old(1) by assumption
  show "(out,bits)\<in>set (comma_sector_rows_restrict guard rows)"
    using image by (simp only: comma_sector_rows_restrict_def set_map)
qed

lemma comma_sector_rows_restrict_refines:
  assumes rows: "comma_sector_rows_refine G scope rows"
    and transport: "\<And>r. comma_phase_member guard r \<Longrightarrow> F r=G r"
  shows "comma_sector_rows_refine F (guard AND scope) (comma_sector_rows_restrict guard rows)"
proof -
  have cover: "\<And>r. comma_phase_member scope r =
    (\<exists>out bits. (out,bits)\<in>set rows \<and> comma_phase_member bits r)"
    using rows by (simp only: comma_sector_rows_refine_def; blast)
  have exact_value: "\<And>out bits r. (out,bits)\<in>set rows \<Longrightarrow>
    comma_phase_member bits r \<Longrightarrow> G r=out"
    using rows by (simp only: comma_sector_rows_refine_def; blast)
  have covered: "comma_phase_member (guard AND scope) r =
    (\<exists>out bits. (out,bits)\<in>set (comma_sector_rows_restrict guard rows) \<and>
      comma_phase_member bits r)" for r
  proof
    assume input: "comma_phase_member (guard AND scope) r"
    have both: "comma_phase_member guard r \<and> comma_phase_member scope r"
      using input by (simp only: comma_phase_member_and)
    have guard: "comma_phase_member guard r" by (rule conjunct1[OF both])
    have scope: "comma_phase_member scope r" by (rule conjunct2[OF both])
    obtain out bits where member: "(out,bits)\<in>set rows" "comma_phase_member bits r"
      using scope cover[of r] by blast
    have target: "(out,guard AND bits)\<in>set (comma_sector_rows_restrict guard rows)"
      by (simp only: comma_sector_rows_restrict_member; rule exI[where x=bits]; simp add: member(1))
    have bit: "comma_phase_member (guard AND bits) r"
      using guard member(2) by (simp only: comma_phase_member_and)
    show "\<exists>out bits. (out,bits)\<in>set (comma_sector_rows_restrict guard rows) \<and>
      comma_phase_member bits r" using target bit by blast
  next
    assume "\<exists>out bits. (out,bits)\<in>set (comma_sector_rows_restrict guard rows) \<and>
      comma_phase_member bits r"
    then obtain out bits where member: "(out,bits)\<in>set (comma_sector_rows_restrict guard rows)"
      "comma_phase_member bits r" by blast
    obtain old where old: "(out,old)\<in>set rows" "bits=guard AND old"
      using member(1) by (simp only: comma_sector_rows_restrict_member; blast)
    have both: "comma_phase_member guard r \<and> comma_phase_member old r"
      using member(2) by (simp only: old(2) comma_phase_member_and)
    have guard: "comma_phase_member guard r" by (rule conjunct1[OF both])
    have oldbit: "comma_phase_member old r" by (rule conjunct2[OF both])
    have scope: "comma_phase_member scope r" using cover[of r] old(1) oldbit by blast
    show "comma_phase_member (guard AND scope) r" using guard scope by (simp only: comma_phase_member_and)
  qed
  have exact_rows: "\<And>out bits r. (out,bits)\<in>set (comma_sector_rows_restrict guard rows) \<Longrightarrow>
    comma_phase_member bits r \<Longrightarrow> F r=out"
  proof -
    fix out bits r
    assume member: "(out,bits)\<in>set (comma_sector_rows_restrict guard rows)"
      and bit: "comma_phase_member bits r"
    obtain old where old: "(out,old)\<in>set rows" "bits=guard AND old"
      using member by (simp only: comma_sector_rows_restrict_member; blast)
    have both: "comma_phase_member guard r \<and> comma_phase_member old r"
      using bit by (simp only: old(2) comma_phase_member_and)
    have guard: "comma_phase_member guard r" by (rule conjunct1[OF both])
    have oldbit: "comma_phase_member old r" by (rule conjunct2[OF both])
    show "F r=out" using transport[OF guard] exact_value[OF old(1) oldbit] by simp
  qed
  show ?thesis unfolding comma_sector_rows_refine_def
    by (intro conjI allI impI; use covered exact_rows in blast)
qed

ML \<open>val _ = comma_sector_rows_core_checkpoint "restriction-refinement"\<close>

lemma comma_sector_rows_filter_nonzero_member:
  "(\<exists>out bits. (out,bits)\<in>set (comma_sector_rows_filter_nonzero rows) \<and>
      comma_phase_member bits r) =
    (\<exists>out bits. (out,bits)\<in>set rows \<and> comma_phase_member bits r)"
proof -
  have nonzero: "comma_phase_member bits r \<Longrightarrow> bits\<noteq>0" for bits
    by (metis comma_phase_member_zero)
  show ?thesis
    by (auto simp: comma_sector_rows_filter_nonzero_def dest: nonzero)
qed

lemma comma_sector_rows_filter_nonzero_refines:
  assumes exact: "comma_sector_rows_refine F scope rows"
  shows "comma_sector_rows_refine F scope (comma_sector_rows_filter_nonzero rows)"
proof -
  have cover: "\<forall>r. comma_phase_member scope r =
      (\<exists>out bits. (out,bits)\<in>set rows \<and> comma_phase_member bits r)"
    using exact unfolding comma_sector_rows_refine_def by blast
  have filtered_cover: "\<forall>r. comma_phase_member scope r =
      (\<exists>out bits. (out,bits)\<in>set (comma_sector_rows_filter_nonzero rows) \<and>
        comma_phase_member bits r)"
    using cover by (simp only: comma_sector_rows_filter_nonzero_member; blast)
  have filtered_values: "\<forall>out bits r.
      (out,bits)\<in>set (comma_sector_rows_filter_nonzero rows) \<longrightarrow>
      comma_phase_member bits r \<longrightarrow> F r=out"
    using exact by (auto simp: comma_sector_rows_refine_def
      comma_sector_rows_filter_nonzero_def)
  show ?thesis unfolding comma_sector_rows_refine_def
    using filtered_cover filtered_values by blast
qed

ML \<open>val _ = comma_sector_rows_core_checkpoint "filter-refinement"\<close>

lemma comma_sector_rows_join:
  assumes left: "comma_sector_rows_refine F a A"
    and right: "comma_sector_rows_refine F b B"
  shows "comma_sector_rows_refine F (a OR b) (A@B)"
  using left right
  by (auto simp: comma_sector_rows_refine_def comma_phase_member_or)

text \<open>The packed producer supplies closed arithmetic equations explicitly.
These rules only transport their checked results into row certificates.\<close>
lemma comma_sector_rows_join_checked:
  assumes left: "comma_sector_rows_refine F a A"
    and right: "comma_sector_rows_refine F b B"
    and mask: "a OR b=c"
  shows "comma_sector_rows_refine F c (A@B)"
  using comma_sector_rows_join[OF left right] by (simp only: mask)

lemma comma_sector_rows_refine_by_outputs:
  "comma_sector_rows_refine F scope rows =
    ((\<forall>r. comma_phase_member scope r =
      (\<exists>out bits. (out,bits)\<in>set rows \<and> comma_phase_member bits r)) \<and>
     (\<forall>out r. (\<exists>bits. (out,bits)\<in>set rows \<and> comma_phase_member bits r) \<longrightarrow> F r=out))"
  unfolding comma_sector_rows_refine_def by blast

lemma comma_mask_rows_normalize_refines:
  "comma_sector_rows_refine F scope (comma_mask_rows_normalize label_key rows) =
    comma_sector_rows_refine F scope rows"
  by (simp only: comma_sector_rows_refine_by_outputs
      comma_mask_rows_normalize_has[unfolded comma_mask_rows_has_def])

ML \<open>val _ = comma_sector_rows_core_checkpoint "normalizer-refinement"\<close>

lemma comma_sector_rows_cons_member:
  "(\<exists>bits. (target,bits)\<in>set ((out,word)#rows) \<and> comma_phase_member bits r) =
    ((target=out \<and> comma_phase_member word r) \<or>
     (\<exists>bits. (target,bits)\<in>set rows \<and> comma_phase_member bits r))"
  by auto

text \<open>Equal terminal outcomes may be merged by OR of their phase words.
No response tree or ancestor trace is needed by this rule. The result equality
is exact: crossing position, fork digit and exponent delta all remain present.\<close>
lemma comma_sector_rows_merge_equal:
  "comma_sector_rows_refine F scope ((out,a)#(out,b)#rows) =
    comma_sector_rows_refine F scope ((out,a OR b)#rows)"
proof -
  have members: "(\<exists>bits. (target,bits)\<in>set ((out,a)#(out,b)#rows) \<and> comma_phase_member bits r) =
    (\<exists>bits. (target,bits)\<in>set ((out,a OR b)#rows) \<and> comma_phase_member bits r)" for target r
    by (simp only: comma_sector_rows_cons_member comma_phase_member_or; blast)
  show ?thesis by (simp only: comma_sector_rows_refine_by_outputs members)
qed

lemma comma_sector_rows_merge_singletons:
  assumes A: "comma_sector_rows_refine F a [(out,a)]"
    and B: "comma_sector_rows_refine F b [(out,b)]"
    and mask: "a OR b=c"
  shows "comma_sector_rows_refine F c [(out,c)]"
proof -
  have joined: "comma_sector_rows_refine F (a OR b) [(out,a),(out,b)]"
    using comma_sector_rows_join[OF A B] by (simp only: append_Cons append_Nil)
  have merged: "comma_sector_rows_refine F (a OR b) [(out,a OR b)]"
    using joined by (simp only: comma_sector_rows_merge_equal)
  show ?thesis using merged by (simp only: mask)
qed

lemma comma_sector_rows_concat:
  assumes clauses: "\<And>scope rows. (scope,rows)\<in>set pieces \<Longrightarrow>
    comma_sector_rows_refine F scope rows"
  shows "comma_sector_rows_refine F (comma_mask_union (map fst pieces))
    (concat (map snd pieces))"
  using clauses
proof (induction pieces)
  case Nil
  show ?case by (simp add: comma_sector_rows_refine_def)
next
  case (Cons item pieces)
  obtain scope rows where item: "item=(scope,rows)" by (cases item) auto
  have head: "comma_sector_rows_refine F scope rows" using Cons.prems by (simp add: item)
  have tail: "comma_sector_rows_refine F (comma_mask_union (map fst pieces))
    (concat (map snd pieces))" by (rule Cons.IH) (use Cons.prems in auto)
  show ?case using comma_sector_rows_join[OF head tail] by (simp add: item)
qed

ML \<open>val _ = comma_sector_rows_core_checkpoint "join-and-concat-refinement"\<close>

lemma comma_sector_rows_rebind:
  assumes "F=G" "comma_sector_rows_refine G scope rows"
  shows "comma_sector_rows_refine F scope rows"
  using assms by simp

ML_file "sector_rows_conversion.ML"

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_sector_rows_restrict_refines comma_sector_rows_filter_nonzero_refines
      comma_sector_rows_join_checked comma_sector_rows_merge_equal
      comma_sector_rows_merge_singletons comma_sector_rows_concat
      comma_sector_rows_rebind comma_mask_rows_merge_sorted_has
      comma_mask_rows_normalize_has comma_mask_rows_normalize_refines}) then ()
    else error "Response row refinement depends on an oracle";
\<close>

end
