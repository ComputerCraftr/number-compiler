theory Comma_Future_Infinite_Lift
  imports Comma_Future_Losing_Lift
begin

text \<open>The unbounded-path and finite-branching graph lemmas are owned by
the fuel-free literal-path theory. This instance retains only the bridge from
its selected cycle certificate to unboundedness.\<close>

theorem comma_checked_cycle_unbounded:
  assumes cert: "comma_rank_witness comma_total_children (set comma_boundary_states) rank"
    and cycle: "comma_surviving_delta_path rank 314 q q 924"
    and valid: "comma_boundary_valid q"
    and exponent: "5\<le>p" and phase: "p mod 924 = snd (snd q)"
  shows "comma_literal_unbounded (comma_boundary_value q p)"
  unfolding comma_literal_unbounded_def
proof (intro allI)
  fix bound
  obtain weight where large: "bound*314\<le>weight"
    and path: "comma_literal_path weight (comma_boundary_value q p)
      (comma_boundary_value q (p+bound*924))"
    using comma_checked_cycle_literal_returns[where k=bound, OF assms] by blast
  have "bound\<le>weight" using large by arith
  then show "\<exists>weight\<ge>bound. \<exists>target.
      comma_literal_path weight (comma_boundary_value q p) target"
    using path by blast
qed

corollary comma_checked_cycle_infinite_literal_path:
  assumes "comma_rank_witness comma_total_children (set comma_boundary_states) rank"
    "comma_surviving_delta_path rank 314 q q 924"
    "comma_boundary_valid q" "5\<le>p" "p mod 924 = snd (snd q)"
  shows "\<exists>path :: nat \<Rightarrow> nat. path 0=comma_boundary_value q p \<and>
    (\<forall>j. comma_child (path j) (path (Suc j)))"
  by (rule comma_literal_unbounded_infinite_path[OF comma_checked_cycle_unbounded[OF assms]])

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_literal_unbounded_infinite_path comma_checked_cycle_unbounded
      comma_checked_cycle_infinite_literal_path})
    then () else error "Comma infinite lift depends on an oracle";
\<close>
end
