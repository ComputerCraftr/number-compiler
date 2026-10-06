theory Comma_Branch_Period
  imports Comma_Branch_Induction.Comma_Branch_Induction
    Comma_Return_Induction.Comma_Return_Induction
begin

text \<open>Literal branch termination and exponent transport are proved by the shared induction theory. The selected-return relation consumes those certificates directly, avoiding a duplicate macro-path encoding.\<close>

text \<open>The selected finite return records exactly the two possible choices.
Taking the smaller N child needs no sibling exclusion. Taking Z is admitted
only with a checked termination proof for its smaller N sibling. Thus this
relation is the local lexicographic safety object, rather than a bare list of
unrelated losing roots.\<close>

inductive comma_earliest_return_path ::
  "bool list \<Rightarrow> nat \<Rightarrow> comma_boundary_state \<Rightarrow>
    comma_boundary_state \<Rightarrow> nat \<Rightarrow> bool" where
  empty: "comma_boundary_valid q \<Longrightarrow>
    comma_earliest_return_path [] 0 q q 0"
| choose_N: "comma_boundary_valid q \<Longrightarrow> comma_macro_defined q \<Longrightarrow>
    comma_total_macro q=Comma_Fork_At a d \<Longrightarrow>
    (Comma_N,a,(snd (snd q)+d) mod 924) \<in> set (comma_total_children q) \<Longrightarrow>
    comma_earliest_return_path choices n
      (Comma_N,a,(snd (snd q)+d) mod 924) final_state delta \<Longrightarrow>
    comma_earliest_return_path (False#choices) (Suc n) q final_state (d+delta)"
| choose_Z: "comma_boundary_valid q \<Longrightarrow> comma_macro_defined q \<Longrightarrow>
    comma_total_macro q=Comma_Fork_At a d \<Longrightarrow>
    (Comma_Z,a,(snd (snd q)+d) mod 924) \<in> set (comma_total_children q) \<Longrightarrow>
    comma_boundary_terminates (Comma_N,a,(snd (snd q)+d) mod 924) \<Longrightarrow>
    comma_earliest_return_path choices n
      (Comma_Z,a,(snd (snd q)+d) mod 924) final_state delta \<Longrightarrow>
    comma_earliest_return_path (True#choices) (Suc n) q final_state (d+delta)"

lemma comma_earliest_return_path_is_return:
  assumes "comma_earliest_return_path choices n q final_state delta"
  shows "comma_return_path n q final_state delta"
  using assms
proof (induction rule: comma_earliest_return_path.induct)
  case (empty q)
  show ?case by (rule comma_return_path.empty[OF empty.hyps])
next
  case (choose_N q a d choices n final_state delta)
  show ?case
    by (rule comma_return_path.step[OF choose_N.hyps(1,2,3,4) choose_N.IH])
next
  case (choose_Z q a d choices n final_state delta)
  show ?case
    by (rule comma_return_path.step[OF choose_Z.hyps(1,2,3,4) choose_Z.IH])
qed

lemma comma_earliest_return_path_append:
  assumes first: "comma_earliest_return_path choices n q middle delta"
    and second: "comma_earliest_return_path choices' m middle final_state delta'"
  shows "comma_earliest_return_path (choices @ choices') (n+m) q final_state
    (delta+delta')"
  using first second
proof (induction arbitrary: choices' m final_state delta'
    rule: comma_earliest_return_path.induct)
  case (empty q)
  then show ?case by simp
next
  case (choose_N q a d choices n middle delta)
  have tail: "comma_earliest_return_path (choices @ choices') (n+m)
      (Comma_N,a,(snd (snd q)+d) mod 924) final_state (delta+delta')"
    by (rule choose_N.IH[OF choose_N.prems])
  have joined: "comma_earliest_return_path
      (False#(choices @ choices')) (Suc (n+m)) q final_state
      (d+(delta+delta'))"
    by (rule comma_earliest_return_path.choose_N
      [OF choose_N.hyps(1,2,3,4) tail])
  show ?case using joined by (simp add: add.assoc)
next
  case (choose_Z q a d choices n middle delta)
  have tail: "comma_earliest_return_path (choices @ choices') (n+m)
      (Comma_Z,a,(snd (snd q)+d) mod 924) final_state (delta+delta')"
    by (rule choose_Z.IH[OF choose_Z.prems])
  have joined: "comma_earliest_return_path
      (True#(choices @ choices')) (Suc (n+m)) q final_state
      (d+(delta+delta'))"
    by (rule comma_earliest_return_path.choose_Z
      [OF choose_Z.hyps(1,2,3,4,5) tail])
  show ?case using joined by (simp add: add.assoc)
qed

lemma comma_earliest_return_path_repeat:
  assumes route: "comma_earliest_return_path choices n q q delta"
  shows "comma_earliest_return_path (concat (replicate k choices))
    (k*n) q q (k*delta)"
proof (induction k)
  case 0
  have ret: "comma_return_path n q q delta"
    by (rule comma_earliest_return_path_is_return[OF route])
  have valid: "comma_boundary_valid q"
    by (rule comma_return_path_valid[OF ret])
  show ?case
    using comma_earliest_return_path.empty[OF valid]
    by simp
next
  case (Suc k)
  have joined: "comma_earliest_return_path
      (choices @ concat (replicate k choices)) (n+k*n) q q
      (delta+k*delta)"
    by (rule comma_earliest_return_path_append[OF route Suc.IH])
  show ?case using joined by (simp add: algebra_simps)
qed

lemma comma_earliest_return_path_unbounded:
  assumes route: "comma_earliest_return_path choices n q q delta"
    and positive: "0<n"
    and exponent: "5\<le>p"
    and phase: "p mod 924=snd (snd q)"
  shows "comma_literal_unbounded (comma_boundary_value q p)"
  unfolding comma_literal_unbounded_def
proof (intro allI)
  fix bound
  have repeated:
    "comma_earliest_return_path (concat (replicate bound choices))
      (bound*n) q q (bound*delta)"
    by (rule comma_earliest_return_path_repeat[OF route])
  have returns: "comma_return_path (bound*n) q q (bound*delta)"
    by (rule comma_earliest_return_path_is_return[OF repeated])
  obtain weight where large: "bound*n\<le>weight" and path:
    "comma_literal_path weight (comma_boundary_value q p)
      (comma_boundary_value q (p+bound*delta))"
    using comma_return_path_literal[OF returns exponent phase] by blast
  have "bound\<le>bound*n" using positive by (simp add: mult_le_cancel_left1)
  then show "\<exists>weight\<ge>bound. \<exists>target.
      comma_literal_path weight (comma_boundary_value q p) target"
    using large path by (meson order_trans)
qed

lemma comma_earliest_return_path_has_infinite_continuation:
  assumes route: "comma_earliest_return_path choices n q q delta"
    and positive: "0<n"
    and exponent: "5\<le>p"
    and phase: "p mod 924=snd (snd q)"
  shows "\<exists>path :: nat \<Rightarrow> nat. path 0=comma_boundary_value q p \<and>
    (\<forall>j. comma_child (path j) (path (Suc j)))"
proof -
  have unbounded: "comma_literal_unbounded (comma_boundary_value q p)"
    by (rule comma_earliest_return_path_unbounded[OF route positive exponent phase])
  show ?thesis using comma_literal_unbounded_infinite_path[OF unbounded]
    by (simp add: comma_boundary_value_def comma_near_boundary_def)
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_earliest_return_path_is_return
      comma_earliest_return_path_append comma_earliest_return_path_repeat
      comma_earliest_return_path_unbounded
      comma_earliest_return_path_has_infinite_continuation})
    then () else error "Comma branch-period safety imports an oracle";
\<close>
end
