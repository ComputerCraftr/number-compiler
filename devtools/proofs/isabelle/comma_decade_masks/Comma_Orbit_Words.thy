theory Comma_Orbit_Words
  imports Comma_Decade_Masks Comma_Decade_Orbit.Comma_Decade_Orbit_Quotient
begin

declare comma_decade_block_power.simps [simp del]

text \<open>The checked orbit quotient preserves the actual next decade
occurrence, not only a terminal observation. It therefore remains a congruence
under every subsequent powered block. Raw phase remains occurrence transport.\<close>

lemma comma_decade_atom_orbit_congruent:
  assumes phase: "r<924" and x: "x\<le>90" and y: "y\<le>90"
    and same: "comma_offset_orbit x=comma_offset_orbit y"
  shows "comma_decade_block_atom (Comma_Decade r x)=
    comma_decade_block_atom (Comma_Decade r y)"
proof -
  have control: "comma_fast_decade_control (Comma_Decade r x)=
    comma_fast_decade_control (Comma_Decade r y)"
    by (rule comma_decade_control_orbit_congruent[OF x y same])
  have left: "comma_decade_admitted (Comma_Decade r x)" using phase x by simp
  have right: "comma_decade_admitted (Comma_Decade r y)" using phase y by simp
  show ?thesis by (simp only: comma_decade_block_atom_def left right if_True control)
qed

theorem comma_decade_power_orbit_congruent:
  assumes "r<924" "x\<le>90" "y\<le>90" "comma_offset_orbit x=comma_offset_orbit y"
  shows "comma_decade_block_power k (Comma_Decade r x)=
    comma_decade_block_power k (Comma_Decade r y)"
proof (induction k)
  case 0
  show ?case by (simp only: comma_decade_block_power.simps
    comma_decade_atom_orbit_congruent[OF assms])
next
  case (Suc k)
  show ?case by (simp only: comma_decade_block_power.simps Suc.IH)
qed

definition comma_orbit_word :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> comma_word_result" where
  "comma_orbit_word k r i =
    (if r<924 \<and> i<46 then
      comma_word_project comma_offset_orbit
        (comma_decade_block_power k (Comma_Decade r (comma_offset_representatives!i)))
     else Comma_Word_Invalid)"

lemma comma_orbit_word_refines:
  assumes valid: "comma_decade_admitted (Comma_Decade r x)"
  shows "comma_word_project comma_offset_orbit (comma_decade_block_power k (Comma_Decade r x))=
    comma_orbit_word k r (comma_offset_orbit x)"
proof -
  have phase: "r<924" and offset: "x\<le>90" using valid by simp_all
  have rep: "comma_offset_representative x\<le>90"
    "comma_offset_orbit x=comma_offset_orbit (comma_offset_representative x)"
    using comma_offset_representative_admitted[of x] by auto
  have power: "comma_decade_block_power k (Comma_Decade r x)=
    comma_decade_block_power k (Comma_Decade r (comma_offset_representative x))"
    by (rule comma_decade_power_orbit_congruent[OF phase offset rep])
  have guard: "r<924 \<and> comma_offset_orbit x<46"
    using phase comma_offset_orbit_bound[of x] by simp
  show ?thesis
    by (simp only: comma_orbit_word_def guard if_True power comma_offset_representative_def;
      simp)
qed

lemma comma_orbit_representative_index:
  assumes "i<46"
  shows "comma_offset_representatives!i\<le>90"
    "comma_offset_orbit (comma_offset_representatives!i)=i"
  using comma_offset_representatives_checked assms by (auto simp: list_all_iff)

theorem comma_orbit_word_square:
  assumes phase: "r<924" and index: "i<46"
  shows "comma_orbit_word (Suc k) r i=
    comma_word_then (2^k) (comma_orbit_word k) (comma_orbit_word k) r i"
proof -
  let ?x = "comma_offset_representatives!i"
  have offset: "?x\<le>90" and fiber: "comma_offset_orbit ?x=i"
    using comma_orbit_representative_index[OF index] by auto
  have valid: "comma_decade_admitted (Comma_Decade r ?x)" using phase offset by simp
  have square: "comma_word_project comma_offset_orbit
      (comma_decade_block_power (Suc k) (Comma_Decade r ?x))=
    comma_word_then (2^k) (comma_orbit_word k) (comma_orbit_word k) r (comma_offset_orbit ?x)"
    by (rule comma_word_project_square[OF valid]) (rule comma_orbit_word_refines)
  have guard: "r<924 \<and> i<46" using assms by simp
  show ?thesis using square
    by (simp only: comma_orbit_word_def guard if_True fiber; simp)
qed

lemma comma_orbit_word_live_bound:
  assumes "comma_orbit_word k r i=Comma_Word_Live j"
  shows "j<46"
proof -
  have projected: "\<And>result. comma_word_project comma_offset_orbit result=Comma_Word_Live j
      \<Longrightarrow> j<46"
  proof -
    fix result
    assume live: "comma_word_project comma_offset_orbit result=Comma_Word_Live j"
    show "j<46"
    proof (cases result)
      case (Comma_Block_Live source)
      then show ?thesis using live comma_offset_orbit_bound
        by (cases source) (simp; blast)
    next
      case (Comma_Block_Stop h terminal)
      then show ?thesis using live by simp
    next
      case Comma_Block_Invalid
      then show ?thesis using live by simp
    qed
  qed
  show ?thesis using assms projected by (auto simp: comma_orbit_word_def split: if_splits)
qed

lemma comma_orbit_word_square_all:
  assumes "r<924"
  shows "comma_orbit_word (Suc k) r i=
    comma_word_then (2^k) (comma_orbit_word k) (comma_orbit_word k) r i"
proof (cases "i<46")
  case True
  show ?thesis by (rule comma_orbit_word_square[OF assms True])
next
  case False
  then show ?thesis by (simp add: comma_orbit_word_def comma_word_then_def)
qed

text \<open>The packed recurrence below powers already constructed words.
Only its base refers to the semantic one-decade specification. It does not
evaluate representative raw blocks again at higher powers. A concrete base
mask certificate and its sharing/cost bound are separate obligations.\<close>
primrec comma_orbit_live_masks :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_orbit_live_masks 0 = (\<lambda>i j.
    comma_phase_mask (\<lambda>r. comma_orbit_word 0 r i=Comma_Word_Live j))"
| "comma_orbit_live_masks (Suc k) =
    comma_live_mask_compose 46 (2^k) (comma_orbit_live_masks k) (comma_orbit_live_masks k)"

primrec comma_orbit_stop_masks ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> comma_decade_terminal \<Rightarrow> nat" where
  "comma_orbit_stop_masks 0 = (\<lambda>i h terminal.
    comma_phase_mask (\<lambda>r. comma_orbit_word 0 r i=Comma_Word_Stop h terminal))"
| "comma_orbit_stop_masks (Suc k) =
    comma_stop_mask_compose 46 (2^k) (comma_orbit_live_masks k)
      (comma_orbit_stop_masks k) (comma_orbit_stop_masks k)"

theorem comma_orbit_masks_refine:
  "comma_word_masks_correct (comma_orbit_word k)
    (comma_orbit_live_masks k) (comma_orbit_stop_masks k)"
proof (induction k)
  case 0
  show ?case by (simp add: comma_word_masks_correct_def comma_phase_mask_member)
next
  case (Suc k)
  have composed: "comma_word_masks_correct
      (comma_word_then (2^k) (comma_orbit_word k) (comma_orbit_word k))
      (comma_live_mask_compose 46 (2^k) (comma_orbit_live_masks k) (comma_orbit_live_masks k))
      (comma_stop_mask_compose 46 (2^k) (comma_orbit_live_masks k)
        (comma_orbit_stop_masks k) (comma_orbit_stop_masks k))"
    by (rule comma_word_masks_compose_correct[OF Suc.IH Suc.IH])
      (rule comma_orbit_word_live_bound, assumption)
  show ?case using composed
    by (auto simp: comma_word_masks_correct_def comma_orbit_word_square_all)
qed

text \<open>This discharges the generic word-square refinement premise for
all admitted sources and all powers. It supplies no concrete base masks,
all-stop coverage, constructor bound, future-safety rank, or live-cycle check.\<close>

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_decade_atom_orbit_congruent comma_decade_power_orbit_congruent
      comma_orbit_word_refines comma_orbit_word_square comma_orbit_masks_refine})
    then () else error "Orbit word refinement depends on an oracle";
\<close>
end
