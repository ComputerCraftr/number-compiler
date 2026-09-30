theory Comma_Return_Source
  imports Comma_Return_Instance.Comma_Return_Instance
    Comma_Future_Source.Comma_Future_Source
    Comma_Branch_Instance.Comma_Branch_Instance
begin

text \<open>The checked source-20 prelude reaches the nine-tail boundary.
The return induction supplies an unbounded continuation without a global rank
or decade-summary certificate. The first rejected zero-tail child is now
checked locally at every compatible exponent. Later branch choices and
least-root exclusion remain separate obligations.\<close>

theorem comma_source20_return_infinite:
  "\<exists>path :: nat \<Rightarrow> nat. path 0=20 \<and>
    (\<forall>j. comma_child (path j) (path (Suc j)))"
proof (rule comma_source20_infinite_from_boundary)
  show "comma_literal_unbounded (comma_boundary_value (Comma_N,2,10) 10)"
    by (rule comma_return_unbounded[OF comma_nine_return_checked]) simp_all
qed


theorem comma_source20_return_first_choice_unique:
  assumes initial: "path 0=20"
    and edges: "\<And>j. comma_child (path j) (path (Suc j))"
  shows "path 412987859=19999999999"
proof (rule comma_source20_first_choice_from_losing[OF _ initial edges])
  show "\<not>(\<exists>tail :: nat \<Rightarrow> nat. tail 0=20000000000 \<and>
    (\<forall>j. comma_child (tail j) (tail (Suc j))))"
    using comma_zero_child_has_no_infinite_literal_path[where p=10]
    by (simp add: comma_boundary_value_def)
qed

theorem comma_return_zero_siblings_terminate:
  "\<not>(\<exists>path :: nat \<Rightarrow> nat. path 0=2*10^(10+924*k) \<and>
    (\<forall>j. comma_child (path j) (path (Suc j))))"
  using comma_boundary_terminates_every_period
    [OF comma_zero_child_terminates, where p=10 and k=k]
  by (simp add: comma_boundary_value_def)

ML \<open>
  val _ = if null (Thm_Deps.all_oracles @{thms comma_source20_return_infinite
      comma_source20_return_first_choice_unique comma_return_zero_siblings_terminate})
    then () else error "Source-20 return proof depends on an oracle";
\<close>
end
