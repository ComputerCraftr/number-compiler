theory Comma_Branch_Induction
  imports Comma_Future_Check.Comma_Future_Losing_Lift
begin

text \<open>Local termination certificates retain the checked macro and every
child. They do not require a global totality table or an exact depth. Their
literal interpretation is uniform over every admitted exponent in the phase.\<close>

inductive comma_boundary_terminates :: "comma_boundary_state \<Rightarrow> bool" where
  terminal: "comma_boundary_valid q \<Longrightarrow> comma_macro_defined q \<Longrightarrow>
    comma_total_macro q=Comma_Landmine_At d \<Longrightarrow> comma_boundary_terminates q"
| branch: "comma_boundary_valid q \<Longrightarrow> comma_macro_defined q \<Longrightarrow>
    comma_total_macro q=Comma_Fork_At a d \<Longrightarrow>
    (\<And>child. child\<in>set (comma_total_children q) \<Longrightarrow>
      comma_boundary_terminates child) \<Longrightarrow> comma_boundary_terminates q"

lemma comma_boundary_terminates_valid:
  "comma_boundary_terminates q \<Longrightarrow> comma_boundary_valid q"
  by (erule comma_boundary_terminates.cases) auto

lemma comma_boundary_terminates_fork:
  assumes valid: "comma_boundary_valid q"
    and defined: "comma_macro_defined q"
    and fork: "comma_total_macro q=Comma_Fork_At a d"
    and near: "comma_boundary_terminates
      (Comma_N,a,(snd (snd q)+d) mod 924)"
    and zero: "comma_boundary_terminates
      (Comma_Z,a,(snd (snd q)+d) mod 924)"
  shows "comma_boundary_terminates q"
proof (rule comma_boundary_terminates.branch[OF valid defined fork])
  fix child
  assume "child\<in>set (comma_total_children q)"
  then show "comma_boundary_terminates child"
    using near zero fork by (auto simp: comma_total_children_def)
qed

theorem comma_boundary_terminates_literal:
  assumes finite: "comma_boundary_terminates q"
    and exponent: "5\<le>p" and phase: "p mod 924=snd (snd q)"
  shows "\<not>(\<exists>path :: nat \<Rightarrow> nat. path 0=comma_boundary_value q p \<and>
    (\<forall>j. comma_child (path j) (path (Suc j))))"
  using finite exponent phase
proof (induction arbitrary: p rule: comma_boundary_terminates.induct)
  case (terminal q d)
  obtain weight last where prefix:
      "comma_unique_literal_path weight (comma_boundary_value q p) last"
    and stop: "\<nexists>v. comma_child last v"
    using comma_total_macro_unique_landmine_prefix
      [OF terminal.hyps(2,1) terminal.prems terminal.hyps(3)] by blast
  show ?case
  proof
    assume "\<exists>path :: nat \<Rightarrow> nat. path 0=comma_boundary_value q p \<and>
      (\<forall>j. comma_child (path j) (path (Suc j)))"
    then obtain path where initial: "path 0=comma_boundary_value q p"
      and edges: "\<And>j. comma_child (path j) (path (Suc j))" by blast
    have actual: "comma_literal_path weight (comma_boundary_value q p) (path weight)"
      using comma_infinite_literal_prefix[where path=path and n=weight, OF edges] initial by simp
    have "path weight=last"
      by (rule comma_unique_literal_path_endpoint[OF prefix actual])
    then show False using stop edges[of weight] by simp
  qed
next
  case (branch q a d)
  obtain weight last where prefix:
      "comma_unique_literal_path weight (comma_boundary_value q p) last"
    and children: "\<forall>v. comma_child last v \<longleftrightarrow>
      v=comma_near_boundary a (p+d) \<or> v=comma_zero_boundary a (p+d)"
    using comma_total_macro_unique_fork_prefix
      [OF branch.hyps(2,1) branch.prems branch.hyps(3)] by blast
  show ?case
  proof
    assume "\<exists>path :: nat \<Rightarrow> nat. path 0=comma_boundary_value q p \<and>
      (\<forall>j. comma_child (path j) (path (Suc j)))"
    then obtain path where initial: "path 0=comma_boundary_value q p"
      and edges: "\<And>j. comma_child (path j) (path (Suc j))" by blast
    have actual: "comma_literal_path weight (comma_boundary_value q p) (path weight)"
      using comma_infinite_literal_prefix[where path=path and n=weight, OF edges] initial by simp
    have last: "path weight=last"
      by (rule comma_unique_literal_path_endpoint[OF prefix actual])
    have alternatives: "path (Suc weight)=comma_near_boundary a (p+d) \<or>
        path (Suc weight)=comma_zero_boundary a (p+d)"
      using children edges[of weight] last by blast
    have target_exists: "\<exists>child. child\<in>set (comma_total_children q) \<and>
        path (Suc weight)=comma_boundary_value child (p+d)"
    proof (cases "path (Suc weight)=comma_near_boundary a (p+d)")
      case True
      show ?thesis
        by (rule exI[of _ "(Comma_N,a,(snd (snd q)+d) mod 924)"])
          (use True in \<open>simp add: comma_total_children_def branch.hyps(3)
            comma_boundary_value_def comma_near_boundary_def\<close>)
    next
      case False
      have zero: "path (Suc weight)=comma_zero_boundary a (p+d)"
        using alternatives False by blast
      show ?thesis
        by (rule exI[of _ "(Comma_Z,a,(snd (snd q)+d) mod 924)"])
          (use zero in \<open>simp add: comma_total_children_def branch.hyps(3)
            comma_boundary_value_def comma_zero_boundary_def\<close>)
    qed
    obtain child where selected: "child\<in>set (comma_total_children q)"
      and successor_value: "path (Suc weight)=comma_boundary_value child (p+d)"
      using target_exists by blast
    have next_phase: "(p+d) mod 924=snd (snd child)"
      by (rule comma_total_macro_selected_literal_path(2)
        [OF branch.hyps(2,1) branch.prems branch.hyps(3) selected])
    have next_exponent: "5\<le>p+d" using branch.prems(1) by arith
    have impossible: "\<not>(\<exists>tail :: nat \<Rightarrow> nat.
        tail 0=comma_boundary_value child (p+d) \<and>
        (\<forall>j. comma_child (tail j) (tail (Suc j))))"
      by (rule branch.IH[OF selected next_exponent next_phase])
    have "\<exists>tail :: nat \<Rightarrow> nat.
        tail 0=comma_boundary_value child (p+d) \<and>
        (\<forall>j. comma_child (tail j) (tail (Suc j)))"
      by (rule exI[of _ "\<lambda>j. path (Suc weight+j)"])
        (use successor_value edges in simp)
    then show False using impossible by contradiction
  qed
qed

corollary comma_boundary_terminates_every_period:
  assumes "comma_boundary_terminates q" "5\<le>p" "p mod 924=snd (snd q)"
  shows "\<not>(\<exists>path :: nat \<Rightarrow> nat.
    path 0=comma_boundary_value q (p+924*k) \<and>
    (\<forall>j. comma_child (path j) (path (Suc j))))"
  by (rule comma_boundary_terminates_literal[OF assms(1)]) (use assms in auto)

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_boundary_terminates_literal comma_boundary_terminates_every_period})
    then () else error "Local comma termination depends on an oracle";
\<close>
end
