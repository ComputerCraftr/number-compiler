theory Comma_Canonical_Domain
  imports Comma_Decade_Control
begin

ML \<open>val comma_canonical_checkpoint = Comma_Proof_Profile.timer "Canonical domain"\<close>

text \<open>
The round kernel deliberately admits the coarse Entry range
\(x \<le> 98\) for every sector.  A published sector response has the
smaller canonical slice \(x \<le> 89+f\).  These predicates are kept separate:
changing the former would change the finite transition semantics.
\<close>

lemma comma_sector_entry_admitted_f1 [simp]:
  "comma_sector_entry_admitted (Comma_Entry 1 delta x) = (x \<le> 90)"
  by (simp add: comma_sector_entry_admitted_def comma_sector_entry_bound_def)

lemma comma_sector_entry_admitted_f2 [simp]:
  "comma_sector_entry_admitted (Comma_Entry 2 delta x) = (x \<le> 91)"
  by (simp add: comma_sector_entry_admitted_def comma_sector_entry_bound_def)

lemma comma_sector_entry_admitted_f9 [simp]:
  "comma_sector_entry_admitted (Comma_Entry 9 delta x) = (x \<le> 98)"
  by (simp add: comma_sector_entry_admitted_def comma_sector_entry_bound_def)

ML \<open>comma_canonical_checkpoint "comma_sector_entry_admitted_implies_round_admitted"\<close>

lemma comma_sector_entry_admitted_implies_round_admitted:
  assumes "comma_sector_entry_admitted position"
  shows "comma_round_admitted position"
proof (cases position)
  case (Comma_Entry f delta x)
  then show ?thesis
    using assms
    by (simp add: comma_sector_entry_admitted_def comma_sector_entry_bound_def
      comma_round_admitted.simps; arith)
next
  case (Comma_Near f delta h)
  then show ?thesis
    using assms by (simp add: comma_sector_entry_admitted_def)
qed

lemma comma_decade_root_admitted_implies_sector_entry:
  assumes "comma_decade_root_admitted position"
  shows "comma_sector_entry_admitted position"
proof (cases position)
  case (Comma_Entry f delta x)
  then show ?thesis
    using assms
    by (simp add: comma_decade_root_admitted_def
      comma_sector_entry_admitted_def comma_sector_entry_bound_def; arith)
next
  case (Comma_Near f delta h)
  then show ?thesis
    using assms by (simp add: comma_decade_root_admitted_def)
qed

lemma comma_sector_entry_admitted_not_fabricated:
  "\<not> comma_sector_entry_admitted (Comma_Entry 1 delta 98)"
  by simp

lemma comma_sector_entry_admitted_not_fabricated_f2:
  "\<not> comma_sector_entry_admitted (Comma_Entry 2 delta 92)"
  by simp

lemma comma_crossing_target_sector_entry:
  assumes move: "comma_finite_step (residue mod 924) source =
      Comma_Next target"
    and crossing: "comma_round_crossing source target"
  shows "comma_sector_entry_admitted target"
proof -
  obtain delta headroom offset where source:
      "source = Comma_Near 9 delta headroom"
    and target: "target = Comma_Entry 1 (Suc delta) offset"
    and bound: "offset \<le> 90"
    using comma_round_crossing_offset_bound[OF move crossing] by blast
  show ?thesis
    using target bound by (simp add: comma_sector_entry_admitted_def
      comma_sector_entry_bound_def)
qed

ML \<open>comma_canonical_checkpoint "comma_canonical_next_admitted"\<close>

lemma comma_canonical_next_admitted:
  assumes source: "comma_canonical_position_admitted source"
    and move: "comma_finite_step (residue mod 924) source =
      Comma_Next target"
  shows "comma_canonical_position_admitted target"
proof -
  have coarse_source: "comma_round_admitted source"
    by (rule comma_canonical_position_implies_round_admitted[OF source])
  have coarse_target: "comma_round_admitted target"
    by (rule comma_round_next_admitted[OF coarse_source move])
  show ?thesis
  proof (cases source)
    case (Comma_Entry f delta offset)
    obtain g d h where target: "target=Comma_Near g d h"
      using move by (auto simp: Comma_Entry comma_finite_step_def
        comma_weighted_step_def Let_def split: if_splits)
    show ?thesis using coarse_target by (simp add: target)
  next
    case (Comma_Near f delta headroom)
    have bounds: "1 \<le> f" "f \<le> 9" "1 \<le> headroom"
        "headroom \<le> 540"
      using coarse_source by (simp_all add: Comma_Near)
    show ?thesis
      by (rule comma_near_next_canonical[OF bounds])
        (use move in \<open>simp only: Comma_Near\<close>)
  qed
qed

ML \<open>comma_canonical_checkpoint "comma_crossing_canonical_root"\<close>

lemma comma_crossing_canonical_root:
  assumes "comma_finite_step (residue mod 924) source=Comma_Next target"
    "comma_round_crossing source target"
  shows "comma_decade_root_admitted target"
  using comma_round_crossing_offset_bound[OF assms]
  by (auto simp: comma_decade_root_admitted_def)

lemma comma_decade_decode_rejects_nonroot_entry:
  assumes "\<not>comma_decade_root_admitted (Comma_Entry f d x)"
  shows "comma_decade_decode r (Comma_Round_Cross (Comma_Entry f d x))=
    Comma_Decade_Invalid"
  using assms by simp

lemma comma_decade_decode_fabricated_entry:
  "comma_decade_decode r (Comma_Round_Cross (Comma_Entry 1 d 98))=
    Comma_Decade_Invalid"
  by simp

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_sector_entry_admitted_f1 comma_sector_entry_admitted_f9
      comma_sector_entry_admitted_implies_round_admitted
      comma_decade_root_admitted_implies_sector_entry
      comma_canonical_next_admitted comma_crossing_canonical_root
      comma_decade_decode_rejects_nonroot_entry comma_decade_decode_fabricated_entry})
    then () else error "Canonical comma domains depend on an oracle"
\<close>

ML \<open>comma_canonical_checkpoint "complete"\<close>
end
