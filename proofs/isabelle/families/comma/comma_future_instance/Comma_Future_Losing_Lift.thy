theory Comma_Future_Losing_Lift
  imports Comma_Future_Literal_Bridge Comma_Arithmetic.Comma_Literal_Path
begin

lemma comma_indexed_trace_terminal_landmine:
  assumes "comma_indexed_trace p source rows (Comma_Landmine_At d) terminal"
  shows "comma_weighted_step (p mod 924) terminal = Comma_WLandmine terminal d"
  using assms by (induction p source rows "Comma_Landmine_At d" terminal
    rule: comma_indexed_trace.induct) auto

lemma comma_weighted_landmine_no_literal_child:
  assumes exponent: "5\<le>p"
    and stop: "comma_weighted_step (p mod 924) terminal = Comma_WLandmine terminal d"
  shows "\<nexists>v. comma_child (comma_chart_value p terminal) v"
proof -
  obtain f h where terminal: "terminal = Comma_Near f d h"
    and valid: "1\<le>f" "f\<le>9" "1\<le>h" "h\<le>540"
    using stop by (cases terminal)
      (auto simp: comma_weighted_step_def Let_def split: if_splits)
  have step: "comma_finite_step (p mod 924) (Comma_Near f d h) = Comma_Landmine d"
    using stop by (simp add: terminal comma_finite_step_def)
  have sector: "comma_sector f (p+d) (comma_chart_value p (Comma_Near f d h))"
    by (rule comma_near_chart_checked_sector[OF valid(1,2) exponent valid(3,4)])
  have large: "2\<le>p+d" using exponent by arith
  show ?thesis using comma_near_chart_landmine(2)[OF sector large refl refl step]
    by (simp add: terminal)
qed

lemma comma_total_macro_unique_landmine_prefix:
  assumes defined: "comma_macro_defined q"
    and valid: "comma_boundary_valid q"
    and exponent: "5\<le>p" and phase: "p mod 924 = snd (snd q)"
    and outcome: "comma_total_macro q = Comma_Landmine_At d"
  shows "\<exists>weight terminal.
    comma_unique_literal_path weight (comma_boundary_value q p) terminal \<and>
    (\<nexists>v. comma_child terminal v)"
proof -
  obtain fuel where run: "comma_finite_weighted_macro fuel p q =
      Some (comma_total_weighted_macro p q)"
    using comma_total_weighted_macro_correct[OF
      comma_macro_defined_weighted[OF defined exponent phase]] by blast
  obtain weight terminal where weighted:
      "comma_total_weighted_macro p q = (Comma_Landmine_At d,weight,terminal)"
    using comma_total_weighted_macro_erasure[OF defined exponent phase] outcome
    by (cases "comma_total_weighted_macro p q") auto
  have finite: "comma_finite_weighted_run fuel p (comma_finite_initial q) =
      Some (Comma_Landmine_At d,weight,terminal)"
    using run valid exponent phase by (simp add: comma_finite_weighted_macro_def weighted)
  obtain rows where trace:
      "comma_indexed_trace p (comma_finite_initial q) rows (Comma_Landmine_At d) terminal"
    and weight: "sum_list (map fst rows) = weight"
    using comma_weighted_run_indexed_trace[OF finite] by blast
  have unique: "comma_unique_literal_path weight
      (comma_boundary_value q p) (comma_chart_value p terminal)"
    using comma_source_indexed_unique_path[OF trace exponent]
      comma_chart_initial_refines_boundary[OF valid, of p] weight by simp
  have stop: "\<nexists>v. comma_child (comma_chart_value p terminal) v"
    by (rule comma_weighted_landmine_no_literal_child[OF exponent
      comma_indexed_trace_terminal_landmine[OF trace]])
  show ?thesis using unique stop by blast
qed

theorem comma_descending_loser_no_infinite_literal_path:
  assumes defined_all: "\<And>q. comma_boundary_valid q \<Longrightarrow> comma_macro_defined q"
    and lower: "\<And>q n child. comma_boundary_valid q \<Longrightarrow> rank q=Some n \<Longrightarrow>
      child\<in>set (comma_total_children q) \<Longrightarrow>
      comma_boundary_valid child \<and> (\<exists>m<n. rank child=Some m)"
    and valid: "comma_boundary_valid q" and ranked: "rank q = Some (n::nat)"
    and exponent: "5\<le>p" and phase: "p mod 924 = snd (snd q)"
  shows "\<not>(\<exists>path :: nat \<Rightarrow> nat.
    path 0 = comma_boundary_value q p \<and>
    (\<forall>j. comma_child (path j) (path (Suc j))))"
  using valid ranked exponent phase
proof (induction n arbitrary: q p rule: less_induct)
  case (less n)
  have defined: "comma_macro_defined q"
    by (rule defined_all[OF less.prems(1)])
  show ?case
  proof
    assume "\<exists>path :: nat \<Rightarrow> nat.
      path 0 = comma_boundary_value q p \<and>
      (\<forall>j. comma_child (path j) (path (Suc j)))"
    then obtain path :: "nat \<Rightarrow> nat" where initial:
        "path 0 = comma_boundary_value q p"
      and edges: "\<And>j. comma_child (path j) (path (Suc j))" by blast
    show False
    proof (cases "comma_total_macro q")
      case (Comma_Landmine_At d)
      obtain weight terminal where prefix:
          "comma_unique_literal_path weight (comma_boundary_value q p) terminal"
        and stop: "\<nexists>v. comma_child terminal v"
        using comma_total_macro_unique_landmine_prefix
          [OF defined less.prems(1,3,4) Comma_Landmine_At] by blast
      have actual: "comma_literal_path weight (comma_boundary_value q p) (path weight)"
        using comma_infinite_literal_prefix[where path=path and n=weight, OF edges] initial by simp
      have "path weight = terminal"
        by (rule comma_unique_literal_path_endpoint[OF prefix actual])
      then show False using stop edges[of weight] by simp
    next
      case (Comma_Fork_At a d)
      obtain weight terminal where prefix:
          "comma_unique_literal_path weight (comma_boundary_value q p) terminal"
        and children: "\<forall>v. comma_child terminal v \<longleftrightarrow>
          v = comma_near_boundary a (p+d) \<or> v = comma_zero_boundary a (p+d)"
        using comma_total_macro_unique_fork_prefix
          [OF defined less.prems(1,3,4) Comma_Fork_At] by blast
      have actual: "comma_literal_path weight (comma_boundary_value q p) (path weight)"
        using comma_infinite_literal_prefix[where path=path and n=weight, OF edges] initial by simp
      have terminal: "path weight = terminal"
        by (rule comma_unique_literal_path_endpoint[OF prefix actual])
      have literal_child: "comma_child terminal (path (Suc weight))"
        using edges[of weight] by (simp only: terminal)
      have alternatives: "path (Suc weight) = comma_near_boundary a (p+d) \<or>
          path (Suc weight) = comma_zero_boundary a (p+d)"
        by (rule iffD1[OF spec[OF children, of "path (Suc weight)"] literal_child])
      have target_exists: "\<exists>target. target \<in> set (comma_total_children q) \<and>
          path (Suc weight) = comma_boundary_value target (p+d)"
      proof (cases "path (Suc weight) = comma_near_boundary a (p+d)")
        case True
        show ?thesis
          by (rule exI[of _ "(Comma_N,a,(snd (snd q)+d) mod 924)"])
            (use True in \<open>simp add: comma_total_children_def Comma_Fork_At
              comma_boundary_value_def comma_near_boundary_def\<close>)
      next
        case False
        have zero: "path (Suc weight) = comma_zero_boundary a (p+d)"
          using alternatives False by blast
        show ?thesis
          by (rule exI[of _ "(Comma_Z,a,(snd (snd q)+d) mod 924)"])
            (use zero in \<open>simp add: comma_total_children_def Comma_Fork_At
              comma_boundary_value_def comma_zero_boundary_def\<close>)
      qed
      obtain target where child: "target \<in> set (comma_total_children q)"
        and successor_value: "path (Suc weight) = comma_boundary_value target (p+d)"
        using target_exists by blast
      obtain m where below: "m<n" and ranked: "rank target = Some m"
        using lower[OF less.prems(1,2) child] by blast
      have valid: "comma_boundary_valid target"
        using lower[OF less.prems(1,2) child] by blast
      have exponent: "5\<le>p+d" using less.prems(3) by arith
      have phase: "(p+d) mod 924 = snd (snd target)"
        by (rule comma_total_macro_selected_literal_path(2)
          [OF defined less.prems(1,3,4) Comma_Fork_At child])
      have impossible: "\<not>(\<exists>tail :: nat \<Rightarrow> nat.
        tail 0 = comma_boundary_value target (p+d) \<and>
        (\<forall>j. comma_child (tail j) (tail (Suc j))))"
        by (rule less.IH[OF below valid ranked exponent phase])
      have "\<exists>tail :: nat \<Rightarrow> nat.
        tail 0 = comma_boundary_value target (p+d) \<and>
        (\<forall>j. comma_child (tail j) (tail (Suc j)))"
        by (rule exI[of _ "\<lambda>j. path (Suc weight+j)"])
          (use successor_value edges in simp)
      then show False using impossible by contradiction
    qed
  qed
qed

corollary comma_checked_loser_no_infinite_literal_path:
  assumes checked: "comma_future_rank_check rounds rank"
    and valid: "comma_boundary_valid q" and ranked: "rank q = Some n"
    and exponent: "5\<le>p" and phase: "p mod 924 = snd (snd q)"
  shows "\<not>(\<exists>path :: nat \<Rightarrow> nat.
    path 0 = comma_boundary_value q p \<and>
    (\<forall>j. comma_child (path j) (path (Suc j))))"
proof -
  have cert: "comma_rank_witness comma_total_children (set comma_boundary_states) rank"
    by (rule comma_future_rank_check_sound[OF checked])
  have lower: "\<And>q n child. comma_boundary_valid q \<Longrightarrow> rank q=Some n \<Longrightarrow>
      child\<in>set (comma_total_children q) \<Longrightarrow>
      comma_boundary_valid child \<and> (\<exists>m<n. rank child=Some m)"
  proof -
    fix q n child
    assume valid: "comma_boundary_valid q" and ranked: "rank q=Some n"
      and child: "child\<in>set (comma_total_children q)"
    have state: "q\<in>set comma_boundary_states"
      using valid by (simp add: comma_boundary_states_set)
    have positive: "0<n"
      using comma_rank_zero_terminal[OF cert state] ranked child by (cases n) auto
    have descent: "\<exists>m<n. rank child=Some m"
      using comma_rank_positive_children(2)[OF cert state ranked positive] child by blast
    have closed: "comma_boundary_valid child"
      using comma_rank_witness_closed[OF cert state] child
      by (auto simp: comma_boundary_states_set)
    show "comma_boundary_valid child \<and> (\<exists>m<n. rank child=Some m)"
      using descent closed by blast
  qed
  show ?thesis by (rule comma_descending_loser_no_infinite_literal_path
    [OF comma_future_rank_check_defined[OF checked] lower valid ranked exponent phase])
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_descending_loser_no_infinite_literal_path
      comma_total_macro_unique_landmine_prefix
      comma_checked_loser_no_infinite_literal_path})
    then () else error "Comma losing lift depends on an oracle";
\<close>
end
