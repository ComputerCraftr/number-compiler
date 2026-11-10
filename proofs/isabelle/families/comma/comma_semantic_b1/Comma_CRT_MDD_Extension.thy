theory Comma_CRT_MDD_Extension
  imports Comma_CRT_MDD
begin

text \<open>
Appending nodes does not change an earlier root: every recursive lookup must
name a smaller identifier. Public evaluation additionally requires admission
of the extended table. A shared integer alone is not a cross-table identity.
\<close>

lemma comma_crt_mdd_eval_raw_append:
  assumes root: "root < length nodes"
  shows "comma_crt_mdd_eval_raw radices (nodes @ added) coordinate root =
    comma_crt_mdd_eval_raw radices nodes coordinate root"
  using root
proof (induction root rule: less_induct)
  case (less root)
  have root_bound: "root < length nodes" by (rule less.prems)
  have extended_bound: "root < length (nodes @ added)"
    using root_bound by simp
  have selected: "(nodes @ added) ! root = nodes ! root"
    using root_bound by (simp add: nth_append)
  have child_exact:
      "comma_crt_mdd_eval_raw radices (nodes @ added) coordinate child =
       comma_crt_mdd_eval_raw radices nodes coordinate child"
    if child: "child < root" for child
  proof -
    have "child < length nodes" using child root_bound by arith
    then show ?thesis by (rule less.IH[OF child])
  qed
  show ?case
    by (subst (1 2) comma_crt_mdd_eval_raw.simps)
      (simp only: root_bound extended_bound if_True selected;
       cases "nodes ! root";
       simp only: comma_crt_mdd_node.case Let_def;
       auto simp only: child_exact split: if_splits)
qed

lemma comma_crt_mdd_eval_append:
  assumes original: "comma_crt_mdd_table_wellformed radices nodes"
    and extension: "comma_crt_mdd_table_wellformed radices (nodes @ added)"
    and root: "root < length nodes"
  shows "comma_crt_mdd_eval radices (nodes @ added) coordinate root =
    comma_crt_mdd_eval radices nodes coordinate root"
  using comma_crt_mdd_eval_raw_append[OF root,
      where radices=radices and added=added and coordinate=coordinate]
    original extension
  by (simp only: comma_crt_mdd_eval_def if_True)

lemma comma_crt_mdd_eval_phase_append:
  assumes original: "comma_crt_mdd_table_wellformed radices nodes"
    and extension: "comma_crt_mdd_table_wellformed radices (nodes @ added)"
    and root: "root < length nodes"
  shows "comma_crt_mdd_eval_phase radices (nodes @ added) phase root =
    comma_crt_mdd_eval_phase radices nodes phase root"
  unfolding comma_crt_mdd_eval_phase_def
  by (rule comma_crt_mdd_eval_append[OF original extension root])

ML \<open>
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Immutable MDD table extension preserves selected roots"
    @{thms comma_crt_mdd_eval_raw_append comma_crt_mdd_eval_append
      comma_crt_mdd_eval_phase_append};
\<close>

end
