theory Comma_Continue_Frontier_Induction
  imports Comma_Continue_Image_Bridge
begin

text \<open>
A compact frontier checker supplies one initial predicate and one checked
backward-transfer equation per round.  This induction transports those
equations to the existing exact Continue power.  It does not construct the
legacy output columns or enumerate phase/source occurrences.
\<close>

lemma comma_continue_frontier_exact:
  fixes step :: "nat \<Rightarrow> 'c \<Rightarrow> 'c comma_phase_class_action"
    and valid :: "nat \<Rightarrow> 'c \<Rightarrow> bool"
    and bad :: "nat \<Rightarrow> nat \<Rightarrow> 'c \<Rightarrow> bool"
  assumes closed: "\<And>p c q d. valid p c \<Longrightarrow>
      step p c = Comma_Phase_Class_Continue q d \<Longrightarrow> valid q d"
    and initial: "\<And>p c. valid p c \<Longrightarrow>
      bad 0 p c = ((p,c) \<notin> accepted)"
    and successor: "\<And>n p c. n < limit \<Longrightarrow> valid p c \<Longrightarrow>
      bad (Suc n) p c = (case step p c of
        Comma_Phase_Class_Continue q d \<Rightarrow> bad n q d | _ \<Rightarrow> False)"
    and bound: "n \<le> limit"
    and admitted: "valid p c"
  shows "bad n p c = (\<exists>terminal.
    comma_phase_class_continue_power step n (p,c) = Some terminal \<and>
    terminal \<notin> accepted)"
  using bound admitted
proof (induction n arbitrary: p c)
  case 0
  then show ?case using initial by simp
next
  case (Suc n)
  have smaller: "n \<le> limit" and strict: "n < limit"
    using Suc.prems(1) by auto
  have recurrence: "bad (Suc n) p c = (case step p c of
      Comma_Phase_Class_Continue q d \<Rightarrow> bad n q d | _ \<Rightarrow> False)"
    by (rule successor[OF strict Suc.prems(2)])
  show ?case
  proof (cases "step p c")
    case Comma_Phase_Class_Invalid
    then show ?thesis using recurrence
      by (simp add: comma_phase_class_continue_power_Suc
          comma_phase_class_continue_option_step_def)
  next
    case (Comma_Phase_Class_Fork a d)
    then show ?thesis using recurrence
      by (simp add: comma_phase_class_continue_power_Suc
          comma_phase_class_continue_option_step_def)
  next
    case (Comma_Phase_Class_Landmine d)
    then show ?thesis using recurrence
      by (simp add: comma_phase_class_continue_power_Suc
          comma_phase_class_continue_option_step_def)
  next
    case (Comma_Phase_Class_Continue q d)
    have next_valid: "valid q d"
      by (rule closed[OF Suc.prems(2) Comma_Phase_Class_Continue])
    have exact: "bad n q d = (\<exists>terminal.
        comma_phase_class_continue_power step n (q,d) = Some terminal \<and>
        terminal \<notin> accepted)"
      by (rule Suc.IH[OF smaller next_valid])
    show ?thesis using recurrence exact Comma_Phase_Class_Continue
      by (simp add: comma_phase_class_continue_power_Suc
          comma_phase_class_continue_option_step_def)
  qed
qed

theorem comma_continue_frontier_empty_implies_image:
  fixes step :: "nat \<Rightarrow> 'c \<Rightarrow> 'c comma_phase_class_action"
    and valid :: "nat \<Rightarrow> 'c \<Rightarrow> bool"
    and bad :: "nat \<Rightarrow> nat \<Rightarrow> 'c \<Rightarrow> bool"
  assumes closed: "\<And>p c q d. valid p c \<Longrightarrow>
      step p c = Comma_Phase_Class_Continue q d \<Longrightarrow> valid q d"
    and initial: "\<And>p c. valid p c \<Longrightarrow>
      bad 0 p c = ((p,c) \<notin> accepted)"
    and successor: "\<And>n p c. n < limit \<Longrightarrow> valid p c \<Longrightarrow>
      bad (Suc n) p c = (case step p c of
        Comma_Phase_Class_Continue q d \<Rightarrow> bad n q d | _ \<Rightarrow> False)"
    and empty: "\<And>p c. valid p c \<Longrightarrow> \<not> bad limit p c"
    and admitted: "valid p c"
    and reaches: "comma_phase_class_continue_power step limit (p,c) = Some terminal"
  shows "terminal \<in> accepted"
proof -
  have exact: "bad limit p c = (\<exists>t.
      comma_phase_class_continue_power step limit (p,c) = Some t \<and>
      t \<notin> accepted)"
    by (rule comma_continue_frontier_exact
      [where step=step and valid=valid and bad=bad and accepted=accepted
        and limit=limit and n=limit, OF closed initial successor order_refl admitted])
  show ?thesis using exact reaches empty[OF admitted] by blast
qed

ML \<open>
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Backward frontier induction preserves exact Continue image"
    @{thms comma_continue_frontier_exact
      comma_continue_frontier_empty_implies_image};
\<close>

end
