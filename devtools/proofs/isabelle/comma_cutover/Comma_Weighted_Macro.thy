theory Comma_Weighted_Macro
  imports Comma_Macro_Refinement
begin

text \<open>A macro weight counts literal transitions, not boundary visits.\<close>

lemma comma_boundary_state_population:
  "card {q :: comma_boundary_state. comma_boundary_valid q} = 14784"
proof -
  have kinds: "(UNIV :: comma_boundary_kind set) = {Comma_N,Comma_Z}"
    by (auto, metis comma_boundary_kind.exhaust)
  have cart: "{q :: comma_boundary_state. comma_boundary_valid q} =
      (UNIV :: comma_boundary_kind set) \<times> ({2..9} \<times> {..<924})"
    by (auto simp: comma_boundary_valid_def split: prod.splits)
  show ?thesis by (simp add: cart kinds card_cartesian_product)
qed

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

theorem comma_macro_run_literal_refinement:
  assumes source: "comma_sector f p k" and exponent: "2 \<le> p"
    and run: "comma_macro_run fuel f p k w =
      Some (f',p',endpoint,weight,children)"
  shows "\<exists>n. weight = w + n \<and>
    comma_literal_path n k endpoint \<and>
    comma_sector f' p' endpoint \<and> 2 \<le> p' \<and>
    children = comma_large_children f' p' endpoint \<and>
    length children \<noteq> 1"
  using source exponent run
proof (induction fuel arbitrary: f p k w f' p' endpoint weight children)
  case 0
  then show ?case by simp
next
  case (Suc fuel)
  define current where "current = comma_large_children f p k"
  show ?case
  proof (cases "length current = 1")
    case False
    have result: "(f',p',endpoint,weight,children) = (f,p,k,w,current)"
      using Suc.prems(3) False by (auto simp: current_def Let_def)
    have [simp]: "f' = f" "p' = p" "endpoint = k"
      "weight = w" "children = current"
      using result by auto
    show ?thesis
      using Suc.prems(1,2) False
      by (intro exI[where x=0])
        (simp add: current_def comma_literal_path.zero)
  next
    case True
    obtain target where singleton: "current = [target]"
      using True by (cases current) auto
    have singleton_source: "comma_large_children f p k = [target]"
      using singleton by (simp add: current_def)
    define L where "L = comma_cycle_length f"
    define P where "P = comma_period_displacement f (k mod 10) L"
    define G where "G = comma_phase_max_guard f (k mod 10) L"
    define H where "H = comma_headroom f p k"
    define c where "c = comma_safe_cycle_count H G P (H + 1)"
    have f_bounds: "1 \<le> f" "f \<le> 9"
      using Suc.prems(1) by (auto simp: comma_sector_def)
    have Lpos: "0 < L" and closes: "10 dvd L * f"
      using comma_cycle_length_admitted[OF f_bounds]
      by (simp_all add: L_def)
    have Ppos: "0 < P"
      using comma_period_displacement_admitted[of f L "k mod 10"]
        f_bounds(1) Lpos by (simp add: P_def)
    show ?thesis
    proof (cases "c = 0")
      case False
      have cpos: "0 < c" using False by simp
      have jump_path: "comma_literal_path (c * L) k (k + c * P)"
        and jump_chart: "comma_sector f p (k + c * P)"
        using comma_safe_cycles_literal_path
          [OF Suc.prems(1,2) closes Lpos, where target="H + 1"] Ppos
        by (simp_all add: H_def P_def G_def c_def)
      have recursive: "comma_macro_run fuel f p (k + c * P)
          (w + c * L) = Some (f',p',endpoint,weight,children)"
        using Suc.prems(3) singleton cpos
        by (simp add: current_def singleton_source L_def P_def G_def
            H_def c_def Let_def)
      obtain n where tail: "weight = (w + c * L) + n"
          "comma_literal_path n (k + c * P) endpoint"
          "comma_sector f' p' endpoint" "2 \<le> p'"
          "children = comma_large_children f' p' endpoint"
          "length children \<noteq> 1"
        using Suc.IH[OF jump_chart Suc.prems(2) recursive] by blast
      have "comma_literal_path (c * L + n) k endpoint"
        using comma_literal_path_append[OF jump_path tail(2)] .
      then show ?thesis using tail
        by (intro exI[where x="c * L + n"]) (simp add: add.assoc)
    next
      case True
      define same where "same = (if f < 9 then
          H > 10 * (k mod 10) + f + 1
          else H > 10 * (k mod 10) + 9)"
      define f1 where "f1 = (if same then f else if f < 9 then f + 1 else 1)"
      define p1 where "p1 = (if same \<or> f < 9 then p else Suc p)"
      have edge: "comma_child k target"
        using comma_singleton_step_chart(1)
          [OF Suc.prems(1,2) singleton_source] .
      have next_chart: "comma_sector f1 p1 target"
        using comma_singleton_step_chart(2)
          [OF Suc.prems(1,2) singleton_source]
        by (simp only: H_def same_def f1_def p1_def)
      have next_exp: "2 \<le> p1"
        using comma_singleton_step_chart(3)
          [OF Suc.prems(1,2) singleton_source]
        by (simp only: H_def same_def f1_def p1_def)
      have c_zero_raw: "comma_safe_cycle_count
          (comma_headroom f p k)
          (comma_phase_max_guard f (k mod 10) (comma_cycle_length f))
          (comma_period_displacement f (k mod 10)
            (comma_cycle_length f))
          (comma_headroom f p k + 1) = 0"
        using True by (simp add: c_def H_def G_def P_def L_def)
      have macro_equation: "comma_macro_run (Suc fuel) f p k w =
          comma_macro_run fuel f1 p1 target (Suc w)"
        using singleton_source c_zero_raw
        by (simp add: comma_macro_run.simps Let_def
            f1_def p1_def same_def H_def)
      have recursive: "comma_macro_run fuel f1 p1 target (Suc w) =
          Some (f',p',endpoint,weight,children)"
        using macro_equation Suc.prems(3) by simp
      obtain n where tail: "weight = Suc w + n"
          "comma_literal_path n target endpoint"
          "comma_sector f' p' endpoint" "2 \<le> p'"
          "children = comma_large_children f' p' endpoint"
          "length children \<noteq> 1"
        using Suc.IH[OF next_chart next_exp recursive] by blast
      have one: "comma_literal_path 1 k target"
        using edge by (auto intro: comma_literal_path.intros)
      have "comma_literal_path (1 + n) k endpoint"
        using comma_literal_path_append[OF one tail(2)] .
      then show ?thesis using tail
        by (intro exI[where x="1 + n"]) simp
    qed
  qed
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_boundary_state_population comma_literal_path_append
      comma_literal_path_snoc comma_fixed_iter_literal_path
      comma_safe_cycles_literal_path comma_macro_run_literal_refinement})
    then () else error "Comma weighted macro lemmas depend on an oracle";
\<close>

end
