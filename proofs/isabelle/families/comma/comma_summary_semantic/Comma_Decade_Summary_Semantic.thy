theory Comma_Decade_Summary_Semantic
  imports Comma_Decade_Residual_Core.Comma_Decade_Residual_Core
begin

text \<open>The decade summary is the semantic owner of a boundary result.  A
literal round closure either returns its terminal event immediately, or
crosses into an admitted decade whose inductive exact summary supplies the
remaining terminal and exponent gain.  The semantic result is established
from literal round control and the inductive summary relation itself.\<close>

fun comma_decade_summary_resume ::
  "(comma_decade_state \<Rightarrow> nat) \<Rightarrow>
   (comma_decade_state \<Rightarrow> comma_decade_terminal) \<Rightarrow>
   nat \<Rightarrow> comma_round_result \<Rightarrow> comma_finite_outcome option" where
  "comma_decade_summary_resume height terminal r (Comma_Round_Fork a d)=Some (Comma_Fork_At a d)"
| "comma_decade_summary_resume height terminal r (Comma_Round_Landmine d)=Some (Comma_Landmine_At d)"
| "comma_decade_summary_resume height terminal r (Comma_Round_Cross (Comma_Entry f d x))=
    (let s=Comma_Decade ((r+d) mod 924) x in
      if f=1 \<and> comma_decade_admitted s then
        Some (comma_summary_outcome (height s+d) (terminal s)) else None)"
| "comma_decade_summary_resume height terminal r (Comma_Round_Cross (Comma_Near f d h))=None"
| "comma_decade_summary_resume height terminal r Comma_Round_Invalid=None"

definition comma_fast_total_boundary ::
  "(comma_decade_state \<Rightarrow> nat) \<Rightarrow>
   (comma_decade_state \<Rightarrow> comma_decade_terminal) \<Rightarrow>
   comma_boundary_state \<Rightarrow> comma_finite_outcome option" where
  "comma_fast_total_boundary height terminal q =
    (if comma_boundary_valid q then
      comma_decade_summary_resume height terminal (snd (snd q))
        (comma_fast_round_aux 9 (snd (snd q)) (comma_finite_initial q))
     else None)"

definition comma_boundary_summary_semantics ::
  "comma_boundary_state \<Rightarrow> comma_finite_outcome \<Rightarrow> bool" where
  "comma_boundary_summary_semantics q outcome =
    (case q of (kind,a,r) \<Rightarrow>
      if \<not> comma_boundary_valid q then False else
      (case comma_round_close r (comma_finite_initial q) of
        (n,t,Comma_Round_Fork b d) \<Rightarrow> outcome=Comma_Fork_At b d
      | (n,t,Comma_Round_Landmine d) \<Rightarrow> outcome=Comma_Landmine_At d
      | (n,t,Comma_Round_Cross (Comma_Entry f d x)) \<Rightarrow>
          (let s=Comma_Decade ((r+d) mod 924) x in
            f=1 \<and> comma_decade_admitted s \<and>
            (\<exists>h tau. comma_decade_exact_summary s h tau \<and>
              outcome=comma_summary_outcome (h+d) tau))
      | (n,t,Comma_Round_Cross (Comma_Near f d h)) \<Rightarrow> False
      | (n,t,Comma_Round_Invalid) \<Rightarrow> False))"

text \<open>This direct summary refinement relates the executable per-round
shortcut to literal round control and the inductive summary relation.  The
separate child-list completeness and weighted lifting bridges remain to be
proved before this owner supports a full future-semantics cutover.\<close>

theorem comma_fast_total_boundary_recurrence_semantic:
  assumes recurrence: "\<And>s. comma_decade_admitted s \<Longrightarrow>
      comma_fast_decade_summary_step height terminal s"
    and valid: "comma_boundary_valid q"
  obtains outcome where
    "comma_fast_total_boundary height terminal q=Some outcome"
    "comma_boundary_summary_semantics q outcome"
proof -
  obtain kind a r where q: "q=(kind,a,r)" by (cases q) auto
  let ?source="comma_finite_initial q"
  have admitted: "comma_round_admitted ?source"
    and delta: "comma_round_delta ?source=0"
    and phase: "r mod 924=r"
    using valid by (cases kind; auto simp: q comma_boundary_valid_def
      comma_finite_initial_def)+
  obtain n t event where close: "comma_round_close r ?source=(n,t,event)"
    by (cases "comma_round_close r ?source") auto
  have budget: "Suc (9-comma_sector_number ?source)\<le>9"
    using admitted by (cases ?source) auto
  have fast_round:
    "comma_fast_round_aux 9 r ?source=snd (snd (comma_round_close r ?source))"
    by (rule comma_fast_round_aux_correct[OF admitted budget])
  have event_not_invalid: "event\<noteq>Comma_Round_Invalid"
    by (rule comma_round_close_admitted(2)[OF close admitted])
  show thesis
  proof (cases event)
    case (Comma_Round_Fork b d)
    let ?outcome="Comma_Fork_At b d"
    have computed:
      "comma_fast_total_boundary height terminal q=Some ?outcome"
      using valid fast_round close Comma_Round_Fork
      by (simp add: comma_fast_total_boundary_def comma_decade_summary_resume.simps q)
    have semantic: "comma_boundary_summary_semantics q ?outcome"
      using valid close Comma_Round_Fork
      by (simp add: comma_boundary_summary_semantics_def q)
    show thesis by (rule that[OF computed semantic])
  next
    case (Comma_Round_Landmine d)
    let ?outcome="Comma_Landmine_At d"
    have computed:
      "comma_fast_total_boundary height terminal q=Some ?outcome"
      using valid fast_round close Comma_Round_Landmine
      by (simp add: comma_fast_total_boundary_def comma_decade_summary_resume.simps q)
    have semantic: "comma_boundary_summary_semantics q ?outcome"
      using valid close Comma_Round_Landmine
      by (simp add: comma_boundary_summary_semantics_def q)
    show thesis by (rule that[OF computed semantic])
  next
    case (Comma_Round_Cross target)
    obtain x where x: "x\<le>90" "target=Comma_Entry 1 1 x"
      using comma_round_close_crossing_phase[of r ?source n t target]
        close Comma_Round_Cross admitted delta by auto
    let ?s="Comma_Decade ((r+1) mod 924) x"
    have state: "comma_decade_admitted ?s" using x by simp
    have summary: "comma_decade_exact_summary ?s (height ?s) (terminal ?s)"
      by (rule comma_fast_decade_summary_recurrence_sound[OF recurrence state])
    let ?outcome="comma_summary_outcome (height ?s+1) (terminal ?s)"
    have computed:
      "comma_fast_total_boundary height terminal q=Some ?outcome"
      using valid fast_round close Comma_Round_Cross x state
      by (simp add: comma_fast_total_boundary_def comma_decade_summary_resume.simps
          q Let_def)
    have semantic: "comma_boundary_summary_semantics q ?outcome"
      using valid close Comma_Round_Cross x state summary
      by (auto simp: comma_boundary_summary_semantics_def q Let_def)
    show thesis by (rule that[OF computed semantic])
  next
    case Comma_Round_Invalid
    then show thesis using event_not_invalid by contradiction
  qed
qed

text \<open>The algebraic constructor discharges the local recurrence law;
no physical rectangle or candidate table is a premise of the primary theorem.
The following compatibility corollary keeps the independent table audit usable.
It does not supply the missing algebraic constructor instance.\<close>

corollary comma_fast_total_boundary_semantic:
  assumes checked: "comma_decade_summary_checked height terminal"
    and valid: "comma_boundary_valid q"
  obtains outcome where
    "comma_fast_total_boundary height terminal q=Some outcome"
    "comma_boundary_summary_semantics q outcome"
proof -
  have recurrence: "comma_fast_decade_summary_step height terminal s"
    if "comma_decade_admitted s" for s
    by (rule comma_decade_summary_row[OF checked that])
  show thesis
    by (rule comma_fast_total_boundary_recurrence_semantic[OF recurrence valid that])
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_fast_total_boundary_recurrence_semantic
      comma_fast_total_boundary_semantic})
    then () else error "Direct decade-summary semantics depends on an oracle";
\<close>

end
