theory Comma_Literal_Path
  imports Comma_Boundary_Primitives
begin

text \<open>Literal path concatenation and safe-cycle paths independent of
any scalar or weighted boundary macro implementation.\<close>

inductive comma_literal_path :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  zero: "comma_literal_path 0 k k"
| step: "comma_child k k' \<Longrightarrow>
    comma_literal_path n k' target \<Longrightarrow>
    comma_literal_path (Suc n) k target"

lemma comma_literal_path_append:
  assumes first: "comma_literal_path n source middle"
    and second: "comma_literal_path m middle target"
  shows "comma_literal_path (n + m) source target"
  using first second
proof (induction arbitrary: m target rule: comma_literal_path.induct)
  case (zero k)
  then show ?case by simp
next
  case (step k k' n middle)
  then show ?case
    by (simp add: comma_literal_path.step)
qed

lemma comma_literal_path_snoc:
  assumes path: "comma_literal_path n source middle"
    and edge: "comma_child middle target"
  shows "comma_literal_path (Suc n) source target"
proof -
  have one: "comma_literal_path 1 middle target"
    using edge by (auto intro: comma_literal_path.intros)
  have "comma_literal_path (n + 1) source target"
    using comma_literal_path_append[OF path one] .
  then show ?thesis by simp
qed

lemma comma_fixed_iter_literal_path:
  assumes edges: "\<forall>j<N. comma_child (comma_fixed_iter f j k)
      (comma_fixed_iter f (Suc j) k)"
  shows "\<forall>n\<le>N. comma_literal_path n k (comma_fixed_iter f n k)"
proof -
  have path: "comma_literal_path n k (comma_fixed_iter f n k)"
    if n: "n \<le> N" for n
    using n
  proof (induction n)
    case 0
    then show ?case by (simp add: comma_literal_path.zero)
  next
    case (Suc n)
    have prefix: "n \<le> N" using Suc.prems by simp
    have edge: "comma_child (comma_fixed_iter f n k)
        (comma_fixed_iter f (Suc n) k)"
      using edges Suc.prems by auto
    show ?case using comma_literal_path_snoc[OF Suc.IH[OF prefix] edge] .
  qed
  then show ?thesis by blast
qed

lemma comma_safe_cycles_literal_path:
  fixes H G P c target :: nat
  assumes source: "comma_sector f p k" and exponent: "2 \<le> p"
    and closes: "10 dvd L * f" and period: "0 < L"
    and displacement: "0 < comma_period_displacement f (k mod 10) L"
  defines "H \<equiv> comma_headroom f p k"
    and "P \<equiv> comma_period_displacement f (k mod 10) L"
    and "G \<equiv> comma_phase_max_guard f (k mod 10) L"
    and "c \<equiv> comma_safe_cycle_count H G P target"
  shows "comma_literal_path (c * L) k (k + c * P)"
    "comma_sector f p (k + c * P)"
proof -
  have guarded: "\<forall>j<c * L. comma_child (comma_fixed_iter f j k)
      (comma_fixed_iter f (Suc j) k)"
    using comma_safe_complete_cycles_refine(3)
      [OF source exponent closes period displacement,
        where target=target]
    by (simp add: H_def P_def G_def c_def)
  have end_sector: "comma_sector f p (comma_fixed_iter f (c * L) k)"
    using comma_safe_complete_cycles_refine(2)
      [OF source exponent closes period displacement,
        where target=target]
    by (simp add: H_def P_def G_def c_def)
  have endpoint: "comma_fixed_iter f (c * L) k = k + c * P"
    using comma_fixed_iter_complete_cycles[OF closes]
    by (simp add: P_def)
  show "comma_literal_path (c * L) k (k + c * P)"
    using comma_fixed_iter_literal_path[OF guarded] endpoint by auto
  show "comma_sector f p (k + c * P)"
    using end_sector endpoint by simp
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_literal_path_append comma_literal_path_snoc
      comma_fixed_iter_literal_path comma_safe_cycles_literal_path})
    then () else error "Comma literal-path proof depends on an oracle";
\<close>

end
