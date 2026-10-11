theory Comma_Endpoint_Orbit_Interface
  imports Comma_Decade_Masks Comma_Decade_Orbit.Comma_Decade_Orbit_Quotient
begin

ML \<open>
structure Comma_Endpoint_Orbit_Interface_Profile =
struct
  val report = Comma_Proof_Profile.timer "Endpoint orbit interface"
end
val _ = Comma_Endpoint_Orbit_Interface_Profile.report "entered"
\<close>

text \<open>
This interface contains the orbit-word declarations consumed by the
decisive endpoint quotient.  The sparse recurrence theory imports this
interface and adds the powered mask refinements; keeping the shared source
facts here lets endpoint consumers depend on the semantic word boundary
without importing those sparse recurrences.
\<close>

definition comma_orbit_word :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> comma_word_result" where
  "comma_orbit_word k r i =
    (if r<924 \<and> i<46 then
      comma_word_project comma_offset_orbit
        (comma_decade_block_power k (Comma_Decade r (comma_offset_representatives!i)))
     else Comma_Word_Invalid)"

lemma comma_orbit_representative_index:
  assumes "i<46"
  shows "comma_offset_representatives!i\<le>90"
    "comma_offset_orbit (comma_offset_representatives!i)=i"
  using comma_offset_representatives_checked assms by (auto simp: list_all_iff)

text \<open>Round-output admission and projection belong to the orbit-word
interface, independently of any response-row constructor.\<close>
fun comma_sector_base_admitted :: "comma_round_result \<Rightarrow> bool" where
  "comma_sector_base_admitted (Comma_Round_Cross (Comma_Entry f d x)) =
    (comma_decade_root_admitted (Comma_Entry f d x) \<and> d=1)"
| "comma_sector_base_admitted (Comma_Round_Cross (Comma_Near f d h)) = False"
| "comma_sector_base_admitted (Comma_Round_Fork a d) = (d=0)"
| "comma_sector_base_admitted (Comma_Round_Landmine d) = (d=0)"
| "comma_sector_base_admitted Comma_Round_Invalid = False"

fun comma_sector_base_project :: "comma_round_result \<Rightarrow> comma_word_result" where
  "comma_sector_base_project (Comma_Round_Cross (Comma_Entry f d x)) =
    (if comma_decade_root_admitted (Comma_Entry f d x) \<and> d=1
     then Comma_Word_Live (comma_offset_orbit x)
     else Comma_Word_Invalid)"
| "comma_sector_base_project (Comma_Round_Cross (Comma_Near f d h)) = Comma_Word_Invalid"
| "comma_sector_base_project (Comma_Round_Fork a d) =
    (if d=0 then Comma_Word_Stop 0 (Comma_Terminal_Fork a) else Comma_Word_Invalid)"
| "comma_sector_base_project (Comma_Round_Landmine d) =
    (if d=0 then Comma_Word_Stop 0 Comma_Terminal_Landmine else Comma_Word_Invalid)"
| "comma_sector_base_project Comma_Round_Invalid = Comma_Word_Invalid"

text \<open>This fuel-indexed projection bridge is retained as a legacy
comparison audit for sparse response-table clients. Native B1 uses the direct
close-based bridge below.\<close>

lemma comma_sector_base_project_refines:
  assumes source: "r<924" "x\<le>90"
    and exact: "comma_fast_round_aux 9 r (Comma_Entry 1 0 x)=out"
    and admitted: "comma_sector_base_admitted out"
  shows "comma_sector_base_project out =
    comma_word_project comma_offset_orbit (comma_decade_block_atom (Comma_Decade r x))"
proof -
  have fast_control:
    "comma_fast_decade_control (Comma_Decade r x)=comma_decade_decode r out"
    using exact by (simp add: comma_fast_decade_control.simps)
  have valid: "comma_decade_admitted (Comma_Decade r x)" using source by simp
  have control: "comma_decade_control (Comma_Decade r x)=comma_decade_decode r out"
    using fast_control comma_fast_decade_control_correct[OF valid] by metis
  show ?thesis
    apply (simp only: comma_decade_block_atom_def valid if_True control)
    using admitted
    apply (cases out; auto)
    subgoal for target by (cases target) auto
    done
qed

lemma comma_sector_base_project_refines_close:
  assumes source: "r<924" "x\<le>90"
    and close: "comma_round_close r (Comma_Entry 1 0 x)=(steps,terminal,out)"
    and admitted: "comma_sector_base_admitted out"
  shows "comma_sector_base_project out =
    comma_word_project comma_offset_orbit (comma_decade_block_atom (Comma_Decade r x))"
proof -
  ML_prf \<open>Comma_Endpoint_Orbit_Interface_Profile.report "close-projection entered"\<close>
  have control: "comma_decade_control (Comma_Decade r x)=comma_decade_decode r out"
    by (simp only: comma_decade_control.simps close prod.case)
  have valid: "comma_decade_admitted (Comma_Decade r x)" using source by simp
  ML_prf \<open>Comma_Endpoint_Orbit_Interface_Profile.report "close-projection control bridge reached"\<close>
  show ?thesis
    apply (simp only: comma_decade_block_atom_def valid if_True control)
    using admitted
    apply (cases out; auto)
    subgoal for target by (cases target) auto
    done
qed
ML \<open>
  val _ = Comma_Endpoint_Orbit_Interface_Profile.report
    "close-projection submitted"
\<close>

lemma comma_sector_base_output_admitted:
  assumes offset: "x\<le>90"
    and observed_result: "comma_fast_round_aux 9 r (Comma_Entry 1 0 x)=out"
  shows "comma_sector_base_admitted out"
proof -
  have valid: "comma_round_admitted (Comma_Entry 1 0 x)"
    using offset by simp
  have enough: "Suc (9-comma_sector_number (Comma_Entry 1 0 x))\<le>9"
    by simp
  have fast:
    "comma_fast_round_aux 9 r (Comma_Entry 1 0 x) =
      snd (snd (comma_round_close r (Comma_Entry 1 0 x)))"
    by (rule comma_fast_round_aux_correct[OF valid enough])
  obtain steps terminal result where close:
    "comma_round_close r (Comma_Entry 1 0 x)=(steps,terminal,result)"
    by (metis surj_pair)
  have result_eq: "result=out"
    using fast observed_result close by simp
  have trace: "comma_round_prefix_steps steps r (Comma_Entry 1 0 x) terminal \<and>
      (case result of
        Comma_Round_Fork a delta \<Rightarrow>
          comma_finite_step (r mod 924) terminal=Comma_Fork a delta
      | Comma_Round_Landmine delta \<Rightarrow>
          comma_finite_step (r mod 924) terminal=Comma_Landmine delta
      | Comma_Round_Cross target \<Rightarrow>
          comma_finite_step (r mod 924) terminal=Comma_Next target \<and>
            comma_round_crossing terminal target
      | Comma_Round_Invalid \<Rightarrow>
          comma_finite_step (r mod 924) terminal=Comma_Invalid)"
    by (rule comma_round_close_refines_trace[OF close])
  have result_not_invalid: "result\<noteq>Comma_Round_Invalid"
    by (rule comma_round_close_admitted(2)[OF close valid])
  have delta: "comma_round_delta terminal=0"
    using comma_round_close_delta[OF close valid] by simp
  show ?thesis
  proof (cases out)
    case (Comma_Round_Fork a d)
    have event:
      "comma_finite_step (r mod 924) terminal=Comma_Fork a d"
      using trace result_eq Comma_Round_Fork by auto
    have d_zero: "d=0"
      using event delta
      by (cases terminal)
        (auto simp: comma_finite_step_def comma_weighted_step_def Let_def
          split: if_splits)
    show ?thesis using Comma_Round_Fork d_zero
      by (simp add: comma_sector_base_admitted.simps)
  next
    case (Comma_Round_Landmine d)
    have event:
      "comma_finite_step (r mod 924) terminal=Comma_Landmine d"
      using trace result_eq Comma_Round_Landmine by auto
    have d_zero: "d=0"
      using event delta
      by (cases terminal)
        (auto simp: comma_finite_step_def comma_weighted_step_def Let_def
          split: if_splits)
    show ?thesis using Comma_Round_Landmine d_zero
      by (simp add: comma_sector_base_admitted.simps)
  next
    case (Comma_Round_Cross target)
    obtain d h next_offset where terminal:
        "terminal=Comma_Near 9 d h"
      and target: "target=Comma_Entry 1 (Suc d) next_offset"
      and next_bound: "next_offset\<le>90"
      using comma_round_close_crossing_shape[of r "Comma_Entry 1 0 x"
        steps terminal target] close result_eq Comma_Round_Cross by blast
    have d_zero: "d=0" using delta terminal by simp
    show ?thesis using Comma_Round_Cross target next_bound d_zero
      by (simp add: comma_sector_base_admitted.simps
        comma_decade_root_admitted_def)
  next
    case Comma_Round_Invalid
    then show ?thesis using result_not_invalid result_eq by simp
  qed
qed

lemma comma_sector_base_output_admitted_close:
  assumes offset: "x\<le>90"
    and close: "comma_round_close r (Comma_Entry 1 0 x)=(steps,terminal,out)"
  shows "comma_sector_base_admitted out"
proof -
  ML_prf \<open>Comma_Endpoint_Orbit_Interface_Profile.report "close-admission entered"\<close>
  have valid: "comma_round_admitted (Comma_Entry 1 0 x)"
    using offset by simp
  have trace: "comma_round_prefix_steps steps r (Comma_Entry 1 0 x) terminal \<and>
      (case out of
        Comma_Round_Fork a delta \<Rightarrow>
          comma_finite_step (r mod 924) terminal=Comma_Fork a delta
      | Comma_Round_Landmine delta \<Rightarrow>
          comma_finite_step (r mod 924) terminal=Comma_Landmine delta
      | Comma_Round_Cross target \<Rightarrow>
          comma_finite_step (r mod 924) terminal=Comma_Next target \<and>
            comma_round_crossing terminal target
      | Comma_Round_Invalid \<Rightarrow>
          comma_finite_step (r mod 924) terminal=Comma_Invalid)"
    by (rule comma_round_close_refines_trace[OF close])
  ML_prf \<open>Comma_Endpoint_Orbit_Interface_Profile.report "close-admission trace reached"\<close>
  have result_not_invalid: "out\<noteq>Comma_Round_Invalid"
    by (rule comma_round_close_admitted(2)[OF close valid])
  have delta: "comma_round_delta terminal=0"
    using comma_round_close_delta[OF close valid] by simp
  ML_prf \<open>Comma_Endpoint_Orbit_Interface_Profile.report "close-admission invariants reached"\<close>
  show ?thesis
  proof (cases out)
    case (Comma_Round_Fork a d)
    have event: "comma_finite_step (r mod 924) terminal=Comma_Fork a d"
      using trace Comma_Round_Fork by auto
    have d_zero: "d=0"
      using event delta
      by (cases terminal)
        (auto simp: comma_finite_step_def comma_weighted_step_def Let_def
          split: if_splits)
    ML_prf \<open>Comma_Endpoint_Orbit_Interface_Profile.report "close-admission fork reached"\<close>
    then show ?thesis using Comma_Round_Fork
      by (simp add: comma_sector_base_admitted.simps)
  next
    case (Comma_Round_Landmine d)
    have event: "comma_finite_step (r mod 924) terminal=Comma_Landmine d"
      using trace Comma_Round_Landmine by auto
    have d_zero: "d=0"
      using event delta
      by (cases terminal)
        (auto simp: comma_finite_step_def comma_weighted_step_def Let_def
          split: if_splits)
    ML_prf \<open>Comma_Endpoint_Orbit_Interface_Profile.report "close-admission landmine reached"\<close>
    then show ?thesis using Comma_Round_Landmine
      by (simp add: comma_sector_base_admitted.simps)
  next
    case (Comma_Round_Cross target)
    obtain d h next_offset where terminal_shape:
        "terminal=Comma_Near 9 d h"
      and target_shape: "target=Comma_Entry 1 (Suc d) next_offset"
      and next_bound: "next_offset\<le>90"
      using comma_round_close_crossing_shape[of r "Comma_Entry 1 0 x"
        steps terminal target] close Comma_Round_Cross by blast
    ML_prf \<open>Comma_Endpoint_Orbit_Interface_Profile.report "close-admission crossing shape reached"\<close>
    have d_zero: "d=0" using delta terminal_shape by simp
    show ?thesis using Comma_Round_Cross target_shape next_bound d_zero
      by (simp add: comma_sector_base_admitted.simps
        comma_decade_root_admitted_def)
  next
    case Comma_Round_Invalid
    then show ?thesis using result_not_invalid by simp
  qed
qed
ML \<open>
  val _ = Comma_Endpoint_Orbit_Interface_Profile.report
    "close-admission submitted"
\<close>

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
  have control: "comma_decade_control (Comma_Decade r x)=
    comma_decade_control (Comma_Decade r y)"
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

ML \<open>
  val _ = Comma_Endpoint_Orbit_Interface_Profile.report
    "final-oracle-audit entered"
  val _ = if null (Thm_Deps.all_oracles @{thms
      comma_orbit_representative_index comma_decade_atom_orbit_congruent
      comma_decade_power_orbit_congruent comma_orbit_word_refines
      comma_orbit_word_square comma_orbit_word_live_bound comma_orbit_word_square_all
      comma_sector_base_project_refines_close comma_sector_base_output_admitted_close
      comma_sector_base_project_refines comma_sector_base_output_admitted})
    then () else error "Endpoint orbit interface depends on an oracle"
  val _ = Comma_Endpoint_Orbit_Interface_Profile.report
    "final-oracle-audit checked"
\<close>

end
