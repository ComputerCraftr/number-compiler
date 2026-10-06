theory Comma_Return_Induction
  imports Comma_Future_Check.Comma_Future_Infinite_Lift
begin

text \<open>A return carries its actual exponent displacement. Neither its
construction nor its repetition needs a global rank table. This proves legal
infinite continuation only; excluding smaller siblings is a separate theorem.
The nine-sector local bound is arithmetic, not a bound on future decades.\<close>

inductive comma_round_reaches ::
  "nat \<Rightarrow> comma_finite_position \<Rightarrow> comma_finite_outcome \<Rightarrow> bool"
  for r where
  fork: "comma_fast_round_aux 9 r source=Comma_Round_Fork a d \<Longrightarrow>
    comma_round_reaches r source (Comma_Fork_At a d)"
| landmine: "comma_fast_round_aux 9 r source=Comma_Round_Landmine d \<Longrightarrow>
    comma_round_reaches r source (Comma_Landmine_At d)"
| crossing: "comma_fast_round_aux 9 r source=Comma_Round_Cross target \<Longrightarrow>
    comma_round_reaches r target outcome \<Longrightarrow> comma_round_reaches r source outcome"

text \<open>Occurrence delta is transported into the phase before evaluating a
complete boundary tail. The outcome shift is retained explicitly: a cached
canonical tail may be reused at another occurrence only after restoring its
exact fork or landmine offset. This is a transport theorem, not an equality of
the unshifted outcomes.\<close>

fun comma_return_shift_outcome :: "nat \<Rightarrow> comma_finite_outcome \<Rightarrow>
    comma_finite_outcome" where
  "comma_return_shift_outcome k (Comma_Fork_At a d)=Comma_Fork_At a (d+k)"
| "comma_return_shift_outcome k (Comma_Landmine_At d)=Comma_Landmine_At (d+k)"

lemma comma_return_shift_admitted:
  "comma_round_admitted source \<Longrightarrow>
    comma_round_admitted (comma_shift_position k source)"
  by (cases source) simp_all

lemma comma_return_round_budget:
  assumes "comma_round_admitted source"
  shows "Suc (9-comma_sector_number source) \<le> 9"
proof (cases source)
  case (Comma_Entry f delta x)
  then show ?thesis using assms
    by (simp add: comma_round_admitted.simps comma_sector_number.simps; arith)
next
  case (Comma_Near f delta headroom)
  then show ?thesis using assms
    by (simp add: comma_round_admitted.simps comma_sector_number.simps; arith)
qed

lemma comma_return_fast_round_shift:
  assumes valid: "comma_round_admitted source"
  shows "comma_fast_round_aux 9 r (comma_shift_position k source) =
    comma_shift_round_result k
      (comma_fast_round_aux 9 ((r+k) mod 924) source)"
proof -
  have shifted_valid: "comma_round_admitted (comma_shift_position k source)"
    by (rule comma_return_shift_admitted[OF valid])
  have budget: "Suc (9-comma_sector_number source) \<le> 9"
    by (rule comma_return_round_budget[OF valid])
  have shifted_budget:
    "Suc (9-comma_sector_number (comma_shift_position k source)) \<le> 9"
    by (rule comma_return_round_budget[OF shifted_valid])
  have left: "comma_fast_round_aux 9 r (comma_shift_position k source) =
      snd (snd (comma_round_close r (comma_shift_position k source)))"
    by (rule comma_fast_round_aux_correct[OF shifted_valid shifted_budget])
  have right: "comma_fast_round_aux 9 ((r+k) mod 924) source =
      snd (snd (comma_round_close ((r+k) mod 924) source))"
    by (rule comma_fast_round_aux_correct[OF valid budget])
  show ?thesis
    using left right comma_round_close_phase_shift[of r k source]
    by (cases "comma_round_close ((r+k) mod 924) source")
      (simp add: comma_shift_round_close_def)
qed

lemma comma_round_reaches_phase_transport:
  assumes reaches: "comma_round_reaches phase source outcome"
  shows "\<forall>r k. phase=(r+k) mod 924 \<longrightarrow>
    comma_round_admitted source \<longrightarrow>
    comma_round_reaches r (comma_shift_position k source)
      (comma_return_shift_outcome k outcome)"
  using reaches
proof (induction rule: comma_round_reaches.induct)
  case (fork source a d)
  show ?case
  proof (intro allI impI)
    fix r k
    assume phase: "phase=(r+k) mod 924"
      and valid: "comma_round_admitted source"
    have shifted:
      "comma_fast_round_aux 9 r (comma_shift_position k source) =
        Comma_Round_Fork a (d+k)"
      using comma_return_fast_round_shift[OF valid, of r k] phase fork.hyps
      by simp
    show "comma_round_reaches r (comma_shift_position k source)
        (comma_return_shift_outcome k (Comma_Fork_At a d))"
      by (simp only: comma_return_shift_outcome.simps;
        rule comma_round_reaches.fork[OF shifted])
  qed
next
  case (landmine source d)
  show ?case
  proof (intro allI impI)
    fix r k
    assume phase: "phase=(r+k) mod 924"
      and valid: "comma_round_admitted source"
    have shifted:
      "comma_fast_round_aux 9 r (comma_shift_position k source) =
        Comma_Round_Landmine (d+k)"
      using comma_return_fast_round_shift[OF valid, of r k] phase landmine.hyps
      by simp
    show "comma_round_reaches r (comma_shift_position k source)
        (comma_return_shift_outcome k (Comma_Landmine_At d))"
      by (simp only: comma_return_shift_outcome.simps;
        rule comma_round_reaches.landmine[OF shifted])
  qed
next
  case (crossing source target outcome)
  show ?case
  proof (intro allI impI)
    fix r k
    assume phase: "phase=(r+k) mod 924"
      and valid: "comma_round_admitted source"
    have enough: "Suc (9-comma_sector_number source) \<le> 9"
      by (rule comma_return_round_budget[OF valid])
    have close_eq: "comma_fast_round_aux 9 phase source =
        snd (snd (comma_round_close phase source))"
      by (rule comma_fast_round_aux_correct[OF valid enough])
    obtain steps terminal result where close:
      "comma_round_close phase source=(steps,terminal,result)"
      by (cases "comma_round_close phase source") auto
    have result: "result=Comma_Round_Cross target"
      using crossing.hyps(1) close_eq close by simp
    have close_cross:
      "comma_round_close phase source=(steps,terminal,Comma_Round_Cross target)"
      using close result by simp
    have prefix: "comma_round_prefix_steps (Suc steps) phase source target"
      by (rule comma_round_close_cross_prefix[OF close_cross])
    have target_valid: "comma_round_admitted target"
      by (rule comma_round_prefix_admitted[OF prefix valid])
    have tail: "comma_round_reaches r (comma_shift_position k target)
        (comma_return_shift_outcome k outcome)"
      using crossing.IH[rule_format, of r k] phase target_valid by blast
    have shifted:
      "comma_fast_round_aux 9 r (comma_shift_position k source) =
        Comma_Round_Cross (comma_shift_position k target)"
      using comma_return_fast_round_shift[OF valid, of r k] phase crossing.hyps(1)
      by simp
    show "comma_round_reaches r (comma_shift_position k source)
        (comma_return_shift_outcome k outcome)"
      by (rule comma_round_reaches.crossing[OF shifted tail])
  qed
qed

corollary comma_round_reaches_entry_rebased:
  assumes valid: "comma_round_admitted (Comma_Entry f 0 x)"
    and tail: "comma_round_reaches ((r+d) mod 924)
      (Comma_Entry f 0 x) outcome"
  shows "comma_round_reaches r (Comma_Entry f d x)
    (comma_return_shift_outcome d outcome)"
  using comma_round_reaches_phase_transport[OF tail, rule_format, of r d]
    valid by simp

lemma comma_round_reaches_run:
  assumes "comma_round_reaches r source outcome"
  shows "\<exists>rounds. comma_fast_boundary_run rounds r source=Some outcome"
  using assms
proof (induction rule: comma_round_reaches.induct)
  case (fork source a d)
  show ?case by (rule exI[of _ 1]) (simp add: fork)
next
  case (landmine source d)
  show ?case by (rule exI[of _ 1]) (simp add: landmine)
next
  case (crossing source target outcome)
  obtain rounds where tail: "comma_fast_boundary_run rounds r target=Some outcome"
    using crossing.IH by blast
  show ?case by (rule exI[of _ "Suc rounds"]) (simp add: crossing.hyps(1) tail)
qed

lemma comma_round_reaches_macro:
  assumes valid: "comma_boundary_valid q"
    and trace: "comma_round_reaches (snd (snd q)) (comma_finite_initial q) outcome"
  shows "comma_macro_defined q" "comma_total_macro q=outcome"
proof -
  obtain rounds where run: "comma_fast_boundary_run rounds (snd (snd q))
      (comma_finite_initial q)=Some outcome"
    using comma_round_reaches_run[OF trace] by blast
  have macro: "comma_fast_boundary_macro rounds q=Some outcome"
    using valid run by (simp add: comma_fast_boundary_macro_def)
  show "comma_macro_defined q" "comma_total_macro q=outcome"
    using comma_fast_boundary_macro_total[OF macro] by auto
qed

inductive comma_return_path ::
  "nat \<Rightarrow> comma_boundary_state \<Rightarrow> comma_boundary_state \<Rightarrow> nat \<Rightarrow> bool" where
  empty: "comma_boundary_valid q \<Longrightarrow> comma_return_path 0 q q 0"
| step: "comma_boundary_valid q \<Longrightarrow> comma_macro_defined q \<Longrightarrow>
    comma_total_macro q=Comma_Fork_At a d \<Longrightarrow>
    target\<in>set (comma_total_children q) \<Longrightarrow>
    comma_return_path n target final_state delta \<Longrightarrow>
    comma_return_path (Suc n) q final_state (d+delta)"

lemma comma_return_path_valid:
  "comma_return_path n q target delta \<Longrightarrow> comma_boundary_valid q"
  by (erule comma_return_path.cases) auto

lemma comma_return_path_append:
  assumes "comma_return_path n q middle a" "comma_return_path m middle target b"
  shows "comma_return_path (n+m) q target (a+b)"
  using assms by (induction rule: comma_return_path.induct)
    (auto intro: comma_return_path.intros simp: add.assoc)

lemma comma_return_path_repeat:
  assumes return: "comma_return_path n q q delta"
  shows "comma_return_path (k*n) q q (k*delta)"
proof (induction k)
  case 0
  show ?case using comma_return_path_valid[OF return]
    by (simp add: comma_return_path.empty)
next
  case (Suc k)
  show ?case using comma_return_path_append[OF Suc.IH return] by (simp add: add.commute)
qed

lemma comma_return_path_literal:
  assumes path: "comma_return_path n q target delta"
    and exponent: "5\<le>p" and phase: "p mod 924=snd (snd q)"
  shows "\<exists>weight\<ge>n. comma_literal_path weight
    (comma_boundary_value q p) (comma_boundary_value target (p+delta))"
  using path exponent phase
proof (induction arbitrary: p rule: comma_return_path.induct)
  case (empty q)
  show ?case by (auto intro: comma_literal_path.zero)
next
  case (step q a d middle n target delta)
  obtain head where positive: "0<head" and head:
    "comma_literal_path head (comma_boundary_value q p)
      (comma_boundary_value middle (p+d))"
    using comma_total_macro_selected_literal_path(1)
      [OF step.hyps(2,1) step.prems step.hyps(3,4)] by blast
  have phase: "(p+d) mod 924=snd (snd middle)"
    by (rule comma_total_macro_selected_literal_path(2)
      [OF step.hyps(2,1) step.prems step.hyps(3,4)])
  have large: "5\<le>p+d" using step.prems(1) by arith
  obtain tail where bound: "n\<le>tail" and tail:
    "comma_literal_path tail (comma_boundary_value middle (p+d))
      (comma_boundary_value target (p+d+delta))"
    using step.IH[OF large phase] by blast
  have joined: "comma_literal_path (head+tail) (comma_boundary_value q p)
      (comma_boundary_value target (p+(d+delta)))"
    using comma_literal_path_append[OF head tail] by (simp add: add.assoc)
  have "Suc n\<le>head+tail" using bound positive by arith
  then show ?case using joined by blast
qed

theorem comma_return_unbounded:
  assumes return: "comma_return_path n q q delta" and progress: "0<n"
    and exponent: "5\<le>p" and phase: "p mod 924=snd (snd q)"
  shows "comma_literal_unbounded (comma_boundary_value q p)"
  unfolding comma_literal_unbounded_def
proof (intro allI)
  fix bound
  have repeated: "comma_return_path (bound*n) q q (bound*delta)"
    by (rule comma_return_path_repeat[OF return])
  obtain weight where large: "bound*n\<le>weight" and path:
    "comma_literal_path weight (comma_boundary_value q p)
      (comma_boundary_value q (p+bound*delta))"
    using comma_return_path_literal[OF repeated exponent phase] by blast
  have "bound\<le>bound*n" using progress by (simp add: mult_le_cancel_left1)
  then show "\<exists>weight\<ge>bound. \<exists>target.
      comma_literal_path weight (comma_boundary_value q p) target"
    using large path by (meson order_trans)
qed

corollary comma_nine_return_infinite:
  assumes "comma_return_path 314 (Comma_N,2,10) (Comma_N,2,10) 924"
  shows "\<exists>path :: nat \<Rightarrow> nat. path 0=19999999999 \<and>
    (\<forall>j. comma_child (path j) (path (Suc j)))"
proof -
  have "comma_literal_unbounded (comma_boundary_value (Comma_N,2,10) 10)"
    by (rule comma_return_unbounded[OF assms]) simp_all
  then show ?thesis using comma_literal_unbounded_infinite_path
    by (simp add: comma_boundary_value_def comma_near_boundary_def)
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_return_shift_admitted comma_return_round_budget
      comma_return_fast_round_shift
      comma_round_reaches_phase_transport comma_round_reaches_entry_rebased
      comma_round_reaches_run comma_round_reaches_macro
      comma_return_path_append comma_return_path_repeat comma_return_path_literal
      comma_return_unbounded comma_nine_return_infinite})
    then () else error "Comma return induction depends on an oracle";
\<close>
end
