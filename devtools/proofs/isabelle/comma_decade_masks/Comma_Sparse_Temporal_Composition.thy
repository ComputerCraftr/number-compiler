theory Comma_Sparse_Temporal_Composition
  imports Comma_Sector_Base_Masks
begin

unbundle bit_operations_syntax

type_synonym comma_sparse_word = "(comma_word_result \<times> nat) list"

definition comma_sparse_has :: "comma_sparse_word \<Rightarrow> nat \<Rightarrow> comma_word_result \<Rightarrow> bool" where
  "comma_sparse_has rows r out =
    (\<exists>bits. (out,bits)\<in>set rows \<and> comma_phase_member bits r)"

text \<open>Composition emits only guarded child rows and removes zero masks.
An external producer may merge equal labels using the local binary OR law
below; no repeated scan by output label is part of this executable square.\<close>
definition comma_sparse_prune :: "comma_sparse_word \<Rightarrow> comma_sparse_word" where
  "comma_sparse_prune rows = filter (\<lambda>item. snd item\<noteq>0) rows"

lemma comma_sparse_prune_has:
  "comma_sparse_has (comma_sparse_prune rows) r out = comma_sparse_has rows r out"
proof -
  have nonzero: "\<And>bits. comma_phase_member bits r \<Longrightarrow> bits\<noteq>0"
  proof -
    fix bits
    assume member: "comma_phase_member bits r"
    show "bits\<noteq>0"
    proof
      assume zero: "bits=0"
      show False using member by (simp only: zero comma_phase_member_zero)
    qed
  qed
  have positive: "\<And>bits. comma_phase_member bits r \<Longrightarrow> 0<bits"
    using nonzero by (simp only: neq0_conv)
  show ?thesis using positive
    by (auto simp: comma_sparse_prune_def comma_sparse_has_def; blast)
qed

lemma comma_sparse_merge_has:
  "comma_sparse_has ((label,a OR b)#rows) r out =
    comma_sparse_has ((label,a)#(label,b)#rows) r out"
  by (auto simp: comma_sparse_has_def comma_phase_member_or)

fun comma_sparse_shift :: "nat \<Rightarrow> comma_word_result \<Rightarrow> comma_word_result" where
  "comma_sparse_shift n (Comma_Word_Stop h terminal)=Comma_Word_Stop (n+h) terminal"
| "comma_sparse_shift n (Comma_Word_Live j)=Comma_Word_Live j"
| "comma_sparse_shift n Comma_Word_Invalid=Comma_Word_Invalid"

fun comma_sparse_branch ::
  "nat \<Rightarrow> (nat \<Rightarrow> comma_sparse_word) \<Rightarrow>
    (comma_word_result \<times> nat) \<Rightarrow> comma_sparse_word" where
  "comma_sparse_branch n right (Comma_Word_Live j,bits)=
    map (\<lambda>(out,word). (comma_sparse_shift n out,bits AND comma_rotate_phase n word)) (right j)"
| "comma_sparse_branch n right (Comma_Word_Stop h terminal,bits)=[(Comma_Word_Stop h terminal,bits)]"
| "comma_sparse_branch n right (Comma_Word_Invalid,bits)=[(Comma_Word_Invalid,bits)]"

definition comma_sparse_compose ::
  "nat \<Rightarrow> comma_sparse_word \<Rightarrow> (nat \<Rightarrow> comma_sparse_word) \<Rightarrow> comma_sparse_word" where
  "comma_sparse_compose n left right =
    comma_sparse_prune (concat (map (comma_sparse_branch n right) left))"

lemma comma_sparse_branch_has:
  assumes "r<924"
  shows "comma_sparse_has (comma_sparse_branch n right (left,bits)) r out =
    (comma_phase_member bits r \<and>
      (case left of Comma_Word_Live j \<Rightarrow>
        (\<exists>tail. comma_sparse_has (right j) ((r+n) mod 924) tail \<and>
          out=comma_sparse_shift n tail)
      | other \<Rightarrow> out=other))"
  using assms
  by (cases left; auto simp: comma_sparse_has_def comma_phase_member_and comma_rotate_phase_member; blast)

lemma comma_sparse_compose_has:
  assumes "r<924"
  shows "comma_sparse_has (comma_sparse_compose n left right) r out =
    (\<exists>head. comma_sparse_has left r head \<and>
      (case head of Comma_Word_Live j \<Rightarrow>
        (\<exists>tail. comma_sparse_has (right j) ((r+n) mod 924) tail \<and>
          out=comma_sparse_shift n tail)
      | other \<Rightarrow> out=other))"
proof -
  have flatten: "comma_sparse_has (concat (map (comma_sparse_branch n right) left)) r out =
    (\<exists>head bits. (head,bits)\<in>set left \<and>
      comma_sparse_has (comma_sparse_branch n right (head,bits)) r out)"
    by (auto simp: comma_sparse_has_def)
  show ?thesis
    unfolding comma_sparse_compose_def
    by (simp only: comma_sparse_prune_has flatten comma_sparse_branch_has[OF assms];
      auto simp: comma_sparse_has_def)
qed

definition comma_sparse_refines ::
  "(nat \<Rightarrow> comma_word_result) \<Rightarrow> comma_sparse_word \<Rightarrow> bool" where
  "comma_sparse_refines F rows = (\<forall>r<924. \<forall>out. comma_sparse_has rows r out = (F r=out))"

lemma comma_sparse_refines_at:
  assumes "comma_sparse_refines F rows" "r<924"
  shows "comma_sparse_has rows r out = (F r=out)"
  using assms unfolding comma_sparse_refines_def by blast

lemma comma_sparse_refines_cover:
  assumes "comma_sparse_refines F rows" "r<924"
  shows "\<exists>out bits. (out,bits)\<in>set rows \<and> comma_phase_member bits r"
  using assms by (auto simp: comma_sparse_refines_def comma_sparse_has_def)

lemma comma_sparse_refines_disjoint:
  assumes "comma_sparse_refines F rows" "comma_sparse_has rows r a"
    "comma_sparse_has rows r b"
  shows "a=b"
proof -
  have phase: "r<924"
    using assms(2) by (auto simp: comma_sparse_has_def comma_phase_member_def)
  have exact: "\<forall>out. comma_sparse_has rows r out = (F r=out)"
    using assms(1) phase unfolding comma_sparse_refines_def by blast
  have a: "F r=a" using exact assms(2) by blast
  have b: "F r=b" using exact assms(3) by blast
  show ?thesis by (rule trans[OF a[symmetric] b])
qed

text \<open>Exact first stops are carried unchanged from the left row. A stop
in the right row gains the full positive span, while only its phase lookup is
reduced modulo 924. The result has complete phase coverage whenever both
input actions have it.\<close>
theorem comma_sparse_compose_refines:
  assumes left: "comma_sparse_refines (\<lambda>r. A r i) rows"
    and right: "\<And>j. comma_sparse_refines (\<lambda>r. B r j) (tails j)"
  shows "comma_sparse_refines (\<lambda>r. comma_word_then n A B r i)
    (comma_sparse_compose n rows tails)"
proof -
  have l: "\<And>r out. r<924 \<Longrightarrow> comma_sparse_has rows r out = (A r i=out)"
    by (rule comma_sparse_refines_at[OF left]; assumption)
  have rr: "\<And>r j out. comma_sparse_has (tails j) ((r+n) mod 924) out =
    (B ((r+n) mod 924) j=out)"
    by (rule comma_sparse_refines_at[OF right]; simp)
  show ?thesis unfolding comma_sparse_refines_def
    by (intro allI impI; simp only: comma_sparse_compose_has l rr;
      auto simp: comma_word_then_def split: comma_word_result.splits)
qed

definition comma_sparse_sector_base ::
  "(nat \<Rightarrow> comma_sector_rows) \<Rightarrow> nat \<Rightarrow> comma_sparse_word" where
  "comma_sparse_sector_base rows i = comma_sparse_prune
    (map (\<lambda>(out,bits). (comma_sector_base_project out,bits)) (rows i))"

lemma comma_sparse_sector_base_has:
  "comma_sparse_has (comma_sparse_sector_base rows i) r desired =
    comma_phase_member (comma_sector_output_mask comma_sector_base_project desired (rows i)) r"
  by (simp only: comma_sparse_sector_base_def comma_sparse_prune_has;
    auto simp: comma_sparse_has_def comma_sector_output_mask_member)

theorem comma_sparse_sector_base_refines:
  assumes rows: "\<And>i. i<46 \<Longrightarrow> comma_sector_rows_refine
    (comma_sector_mask_value 1 (comma_offset_representatives!i)) (mask 924) (rows i)"
    and admitted: "\<And>i out bits r. i<46 \<Longrightarrow> (out,bits)\<in>set (rows i) \<Longrightarrow>
      comma_phase_member bits r \<Longrightarrow> comma_sector_base_admitted out"
    and index: "i<46"
  shows "comma_sparse_refines (\<lambda>r. comma_orbit_word 0 r i) (comma_sparse_sector_base rows i)"
  unfolding comma_sparse_refines_def
  apply (intro allI impI)
  apply (simp only: comma_sparse_sector_base_has)
  apply (rule comma_sector_base_rows_refine[OF index])
    apply assumption
   apply (rule rows[OF index])
  apply (rule admitted[OF index]; assumption)
  done

primrec comma_sparse_power ::
  "(nat \<Rightarrow> comma_sparse_word) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> comma_sparse_word" where
  "comma_sparse_power base 0 = base"
| "comma_sparse_power base (Suc k) = (\<lambda>i.
    comma_sparse_compose (2^k) (comma_sparse_power base k i) (comma_sparse_power base k))"

text \<open>Outside the admitted 46 fibers a singleton invalid row makes the
semantic family total. Concrete base producers need certify only admitted
fibers; higher levels use this sparse square exclusively.\<close>
definition comma_sparse_admit ::
  "(nat \<Rightarrow> comma_sparse_word) \<Rightarrow> nat \<Rightarrow> comma_sparse_word" where
  "comma_sparse_admit base i = (if i<46 then base i else [(Comma_Word_Invalid,mask 924)])"

lemma comma_sparse_admit_refines:
  assumes "\<And>i. i<46 \<Longrightarrow> comma_sparse_refines (\<lambda>r. comma_orbit_word 0 r i) (base i)"
  shows "comma_sparse_refines (\<lambda>r. comma_orbit_word 0 r i) (comma_sparse_admit base i)"
  using assms[of i]
  by (cases "i<46"; auto simp: comma_sparse_admit_def comma_sparse_refines_def
    comma_sparse_has_def comma_phase_full_mask comma_orbit_word_def)

theorem comma_sparse_power_refines:
  assumes base: "\<And>i. i<46 \<Longrightarrow> comma_sparse_refines (\<lambda>r. comma_orbit_word 0 r i) (rows i)"
  shows "comma_sparse_refines (\<lambda>r. comma_orbit_word k r i)
    (comma_sparse_power (comma_sparse_admit rows) k i)"
proof (induction k arbitrary: i)
  case 0
  show ?case by (simp only: comma_sparse_power.simps; rule comma_sparse_admit_refines[OF base])
next
  case (Suc k)
  have composed: "comma_sparse_refines
    (\<lambda>r. comma_word_then (2^k) (comma_orbit_word k) (comma_orbit_word k) r i)
    (comma_sparse_compose (2^k) (comma_sparse_power (comma_sparse_admit rows) k i)
      (comma_sparse_power (comma_sparse_admit rows) k))"
    by (rule comma_sparse_compose_refines; rule Suc.IH)
  show ?case using composed
    by (simp add: comma_sparse_refines_def comma_orbit_word_square_all)
qed

corollary comma_sparse_power_exact_stop:
  assumes base: "\<And>i. i<46 \<Longrightarrow> comma_sparse_refines (\<lambda>r. comma_orbit_word 0 r i) (rows i)"
    and phase: "r<924"
  shows "comma_sparse_has (comma_sparse_power (comma_sparse_admit rows) k i) r
    (Comma_Word_Stop h terminal) = (comma_orbit_word k r i=Comma_Word_Stop h terminal)"
  by (rule comma_sparse_refines_at[OF comma_sparse_power_refines[OF base] phase])

corollary comma_sparse_power_coverage:
  assumes base: "\<And>i. i<46 \<Longrightarrow> comma_sparse_refines (\<lambda>r. comma_orbit_word 0 r i) (rows i)"
    and phase: "r<924"
  shows "\<exists>out bits. (out,bits)\<in>set (comma_sparse_power (comma_sparse_admit rows) k i) \<and>
    comma_phase_member bits r"
  by (rule comma_sparse_refines_cover[OF comma_sparse_power_refines[OF base] phase])

text \<open>These are conditional producer integration theorems. They do not
assert a concrete all-stop level, a finite classification, or weighted lifting.\<close>

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_sparse_prune_has comma_sparse_merge_has comma_sparse_compose_refines
      comma_sparse_sector_base_refines
      comma_sparse_power_refines comma_sparse_power_exact_stop comma_sparse_power_coverage})
    then () else error "Sparse temporal composition depends on an oracle";
\<close>
end
