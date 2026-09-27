theory Comma_Decade_Rank_Check
  imports Comma_Decade_Rank_Rules
begin

text \<open>The candidate is only a ranking function. Every transition used below
must be obtained by the checked observation constructor. Bounded conjunctions
retain one proposition per batch, without storing a list of full round outputs.\<close>

lemma comma_rank_complete_rectangle:
  assumes "\<forall>r<924. \<forall>x<91.
    comma_decade_observed_rank_step rank (Comma_Decade r x)"
  shows "comma_decade_rank_check rank"
  unfolding comma_decade_observed_rank_check
proof (intro allI impI)
  fix s
  assume admitted: "comma_decade_admitted s"
  obtain r x where shape: "s = Comma_Decade r x"
    by (cases s) auto
  have bounds: "r < 924 \<and> x \<le> 90"
    using admitted by (simp add: shape)
  have r: "r < 924" using bounds by simp
  have x: "x < 91" using bounds by arith
  show "comma_decade_observed_rank_step rank s"
    using assms r x by (auto simp: shape)
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_rank_complete_rectangle})
    then () else error "Decade rank coverage lemmas depend on an oracle";
\<close>

ML_file "decade_rank_check.ML"

end
