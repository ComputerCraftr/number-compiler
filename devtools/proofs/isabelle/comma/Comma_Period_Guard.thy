theory Comma_Period_Guard
  imports Comma_Exact_Phase_Guard
begin

text \<open>One closed phase period transports every guard by its exact
displacement.  The production PrefixSafety transfer uses this law when
it powers a sector cycle.\<close>

lemma comma_phase_digit_periodic:
  assumes closes: "10 dvd L * f"
  shows "comma_phase_digit f d (L + j) = comma_phase_digit f d j"
proof -
  have zero: "(L * f) mod 10 = 0" using closes by simp
  have rearranged: "d + (L + j) * f = (d + j * f) + L * f"
    by (simp add: algebra_simps)
  have reduced: "((d + j * f) + L * f) mod 10 =
      ((d + j * f) + (L * f mod 10)) mod 10"
    by (rule mod_add_right_eq[symmetric])
  show ?thesis
    unfolding comma_phase_digit_def
    using rearranged reduced zero by (simp add: add.assoc)
qed

lemma comma_period_displacement_succ:
  "comma_period_displacement f d (Suc j) =
    comma_period_displacement f d j +
      10 * comma_phase_digit f d j + f"
  by (simp add: comma_period_displacement_def comma_phase_digit_def
      sum.lessThan_Suc)

lemma comma_period_displacement_shift:
  assumes closes: "10 dvd L * f"
  shows "comma_period_displacement f d (L + j) =
      comma_period_displacement f d L +
        comma_period_displacement f d j"
proof (induction j)
  case 0
  then show ?case by (simp add: comma_period_displacement_def)
next
  case (Suc j)
  have phase: "comma_phase_digit f d (L + j) = comma_phase_digit f d j"
    using comma_phase_digit_periodic[OF closes] .
  show ?case using Suc.IH phase
    by (simp add: comma_period_displacement_succ add.assoc)
qed

lemma comma_period_displacement_repeated:
  assumes closes: "10 dvd L * f"
  shows "comma_period_displacement f d (t * L + j) =
      t * comma_period_displacement f d L +
        comma_period_displacement f d j"
proof (induction t)
  case 0
  then show ?case by (simp add: comma_period_displacement_def)
next
  case (Suc t)
  have shifted: "comma_period_displacement f d
      (L + (t * L + j)) = comma_period_displacement f d L +
      comma_period_displacement f d (t * L + j)"
    using comma_period_displacement_shift[OF closes] .
  show ?case using Suc.IH shifted by (simp add: algebra_simps)
qed

lemma comma_phase_guard_periodic:
  assumes closes: "10 dvd L * f"
  shows "comma_phase_guard_at f d (t * L + j) =
    t * comma_period_displacement f d L + comma_phase_guard_at f d j"
proof -
  have phase: "comma_phase_digit f d (t * L + j) =
      comma_phase_digit f d j"
  proof -
    obtain q where q: "L * f = 10 * q"
      using closes unfolding dvd_def by blast
    have factor: "(t * L) * f = 10 * (t * q)"
      using q by (simp add: algebra_simps)
    have cycle: "10 dvd (t * L) * f"
      using factor unfolding dvd_def by blast
    show ?thesis using comma_phase_digit_periodic[OF cycle] by simp
  qed
  show ?thesis
    using comma_period_displacement_repeated[OF closes, of d t j] phase
    by (simp add: comma_phase_guard_at_def algebra_simps)
qed

text \<open>A phase period has one strict seam guard for each of its
steps.  The largest guard in the last repeated period is the largest
guard of one period plus the displacement of all earlier periods.\<close>

lemma comma_phase_guard_positive:
  "0 < comma_phase_guard_at f d j"
  by (simp add: comma_phase_guard_at_def)

lemma comma_phase_guard_next_displacement:
  assumes "f \<le> 9"
  shows "comma_phase_guard_at f d j =
    comma_period_displacement f d (Suc j) + (if f < 9 then 1 else 0)"
  using assms
  by (auto simp: comma_phase_guard_at_def
      comma_period_displacement_succ)

lemma comma_period_displacement_mono:
  assumes "i \<le> j"
  shows "comma_period_displacement f d i \<le>
    comma_period_displacement f d j"
  using assms
proof (induction j arbitrary: i)
  case 0
  then show ?case by simp
next
  case (Suc j)
  show ?case
  proof (cases "i = Suc j")
    case True
    then show ?thesis by simp
  next
    case False
    then have "i \<le> j" using Suc.prems by arith
    then show ?thesis
      using Suc.IH[of i]
      by (simp add: comma_period_displacement_succ)
  qed
qed

lemma comma_phase_max_guard_closed:
  assumes positive: "0 < steps" and digit: "f \<le> 9"
  shows "comma_phase_max_guard f d steps =
    comma_period_displacement f d steps + (if f < 9 then 1 else 0)"
proof -
  obtain n where steps: "steps = Suc n"
    using positive by (cases steps) auto
  let ?T = "insert 0 (comma_phase_guard_at f d ` {..<steps})"
  let ?last = "comma_phase_guard_at f d n"
  have member: "?last \<in> ?T" by (simp add: steps)
  have finite: "finite ?T" by simp
  have nonempty: "?T \<noteq> {}" by simp
  have lower: "?last \<le> comma_phase_max_guard f d steps"
    using Max_ge[OF finite member]
    by (simp add: comma_phase_max_guard_def)
  have point_bound: "\<And>x. x \<in> ?T \<Longrightarrow> x \<le> ?last"
  proof -
    fix x
    assume x: "x \<in> ?T"
    show "x \<le> ?last"
    proof (cases "x = 0")
      case True
      then show ?thesis by simp
    next
      case False
      obtain j where j: "j < steps" "x = comma_phase_guard_at f d j"
        using x False by auto
      have "Suc j \<le> Suc n" using j by (simp add: steps)
      then show ?thesis
        using comma_period_displacement_mono[of "Suc j" "Suc n" f d]
          comma_phase_guard_next_displacement[OF digit, of d j]
          comma_phase_guard_next_displacement[OF digit, of d n] j
        by simp
    qed
  qed
  have upper: "comma_phase_max_guard f d steps \<le> ?last"
  proof -
    have "Max ?T \<le> ?last"
      by (rule Max.boundedI[OF finite nonempty point_bound])
    then show ?thesis by (simp add: comma_phase_max_guard_def)
  qed
  show ?thesis
    using lower upper comma_phase_guard_next_displacement[OF digit, of d n]
    by (simp add: steps)
qed


lemma comma_phase_max_guard_repeated:
  assumes closes: "10 dvd L * f" and positive: "0 < L" and copies: "0 < c"
  shows "comma_phase_max_guard f d (c * L) =
    (c - 1) * comma_period_displacement f d L +
      comma_phase_max_guard f d L"
proof -
  let ?P = "comma_period_displacement f d L"
  let ?G = "comma_phase_max_guard f d L"
  let ?S = "insert 0 (comma_phase_guard_at f d ` {..<L})"
  have finite: "finite ?S" by simp
  have zero: "0 \<in> ?S" by simp
  have nonempty: "?S \<noteq> {}" using zero by blast
  have guard_member: "comma_phase_guard_at f d 0 \<in> ?S"
    using positive by auto
  have large: "0 < ?G"
    using comma_phase_guard_positive[of f d 0]
      Max_ge[OF finite guard_member]
    by (simp add: comma_phase_max_guard_def)
  have attained: "\<exists>j<L. comma_phase_guard_at f d j = ?G"
  proof -
    have "?G \<in> ?S"
      unfolding comma_phase_max_guard_def by (rule Max_in[OF finite nonempty])
    then show ?thesis using large by auto
  qed
  obtain j where j: "j < L" "comma_phase_guard_at f d j = ?G"
    using attained by blast
  obtain t where c: "c = Suc t" using copies by (cases c) auto
  have last: "(c - 1) * L + j < c * L"
    using j by (simp add: c algebra_simps)
  have lower: "(c - 1) * ?P + ?G \<le>
    comma_phase_max_guard f d (c * L)"
    using comma_phase_guard_below_max[OF last, of f d]
      comma_phase_guard_periodic[OF closes, of d "c - 1" j] j
    by simp
  have point_bound: "\<And>x. x \<in>
      insert 0 (comma_phase_guard_at f d ` {..<c * L}) \<Longrightarrow>
      x \<le> (c - 1) * ?P + ?G"
  proof -
    fix x
    assume member: "x \<in> insert 0 (comma_phase_guard_at f d ` {..<c * L})"
    show "x \<le> (c - 1) * ?P + ?G"
    proof (cases "x = 0")
      case True
      then show ?thesis by simp
    next
      case False
      obtain n where guard: "n < c * L"
        "x = comma_phase_guard_at f d n"
        using member False by auto
      let ?t = "n div L"
      let ?j = "n mod L"
      have split: "n = ?t * L + ?j"
        using positive by (simp add: mult.commute)
      have within: "?t < c" and remainder: "?j < L"
        using guard positive by (auto simp: div_less_iff_less_mult)
      have step: "x = ?t * ?P + comma_phase_guard_at f d ?j"
        using guard split comma_phase_guard_periodic[OF closes, of d ?t ?j]
        by simp
      have guard_bound: "comma_phase_guard_at f d ?j \<le> ?G"
        by (rule comma_phase_guard_below_max[OF remainder])
      have tbound: "?t \<le> c - 1" using within by arith
      have product_bound: "?t * ?P \<le> (c - 1) * ?P"
        using tbound by simp
      show ?thesis using step product_bound guard_bound by arith
    qed
  qed
  have upper: "comma_phase_max_guard f d (c * L) \<le>
    (c - 1) * ?P + ?G"
  proof -
    have "Max (insert 0 (comma_phase_guard_at f d ` {..<c * L}))
      \<le> (c - 1) * ?P + ?G"
      by (rule Max.boundedI) (simp, simp, rule point_bound)
    then show ?thesis by (simp add: comma_phase_max_guard_def)
  qed
  show ?thesis using lower upper by simp
qed


lemma comma_phase_guard_endpoint_sector:
  assumes source: "comma_sector f p k"
    and positive: "0 < steps"
    and bound: "comma_phase_max_guard f (k mod 10) steps <
      comma_headroom f p k"
  shows "comma_sector f p (comma_fixed_iter f steps k)"
proof -
  obtain j where steps: "steps = Suc j"
    using positive by (cases steps) auto
  have j: "j < steps" by (simp add: steps)
  have prefix: "comma_period_displacement f (k mod 10) j +
      10 * comma_phase_digit f (k mod 10) j +
      (if f < 9 then f + 1 else 9) < comma_headroom f p k"
    using comma_phase_guard_below_max[OF j, of f "k mod 10"] bound
    by (simp add: comma_phase_guard_at_def; linarith)
  have fle9: "f \<le> 9" using source by (simp add: comma_sector_def)
  have step: "comma_fixed_iter f steps k =
      k + comma_period_displacement f (k mod 10) j +
        10 * comma_phase_digit f (k mod 10) j + f"
    using comma_fixed_iter_displacement[of f j k]
      comma_fixed_iter_phase[of f j k]
    by (simp add: steps comma_phase_digit_def algebra_simps)
  have sum: "k + comma_headroom f p k = (f + 1) * 10 ^ p"
    by (rule comma_sector_headroom[OF source])
  have guard_digit: "f \<le> (if f < 9 then f + 1 else 9)"
    using fle9 by simp
  have outgoing: "comma_period_displacement f (k mod 10) j +
      10 * comma_phase_digit f (k mod 10) j + f <
      comma_headroom f p k"
    using prefix guard_digit by linarith
  have lower: "f * 10 ^ p \<le> comma_fixed_iter f steps k"
    using source step by (auto simp: comma_sector_def)
  have upper: "comma_fixed_iter f steps k < (f + 1) * 10 ^ p"
    using outgoing step sum by linarith
  show ?thesis using source lower upper
    by (auto simp: comma_sector_def)
qed


definition comma_safe_cycle_count :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_safe_cycle_count H G P target =
    min target (if G < H then (H - 1 - G) div P + 1 else 0)"

lemma comma_safe_cycle_count_characterization:
  assumes displacement: "0 < P"
  shows "c \<le> comma_safe_cycle_count H G P target \<longleftrightarrow>
    c \<le> target \<and> (c = 0 \<or> G + (c - 1) * P < H)"
proof (cases "c = 0")
  case True
  then show ?thesis by (simp add: comma_safe_cycle_count_def)
next
  case False
  have positive: "0 < c" using False by simp
  have arith: "c \<le> (H - 1 - G) div P + 1 \<longleftrightarrow>
    G + (c - 1) * P < H" if h: "G < H"
  proof -
    have "c \<le> (H - 1 - G) div P + 1 \<longleftrightarrow>
      c - 1 \<le> (H - 1 - G) div P"
      using positive by arith
    also have "... \<longleftrightarrow> (c - 1) * P \<le> H - 1 - G"
      using displacement by (rule less_eq_div_iff_mult_less_eq)
    also have "... \<longleftrightarrow> G + (c - 1) * P < H"
      using h by arith
    finally show ?thesis .
  qed
  show ?thesis
    using positive arith by (auto simp: comma_safe_cycle_count_def)
qed


theorem comma_safe_cycle_count_maximal:
  fixes H G P target :: nat
  assumes displacement: "0 < P"
  defines "c \<equiv> comma_safe_cycle_count H G P target"
  shows "c \<le> target" "c = 0 \<or> G + (c - 1) * P < H"
    "\<And>larger. c < larger \<Longrightarrow> larger \<le> target \<Longrightarrow>
      G + (larger - 1) * P \<ge> H"
proof -
  have valid: "c \<le> target \<and> (c = 0 \<or> G + (c - 1) * P < H)"
    using comma_safe_cycle_count_characterization[OF displacement,
      of c H G target] by (simp add: c_def)
  then show "c \<le> target" "c = 0 \<or> G + (c - 1) * P < H"
    by auto
  fix larger
  assume greater: "c < larger" and within: "larger \<le> target"
  have "\<not> larger \<le> comma_safe_cycle_count H G P target"
    using greater by (simp add: c_def)
  then show "G + (larger - 1) * P \<ge> H"
    using comma_safe_cycle_count_characterization[OF displacement,
      of larger H G target] within by auto
qed

theorem comma_safe_complete_cycles_refine:
  fixes H G P c target :: nat
  assumes source: "comma_sector f p k" and exponent: "2 \<le> p"
    and closes: "10 dvd L * f" and period: "0 < L"
    and displacement: "0 < comma_period_displacement f (k mod 10) L"
  defines "H \<equiv> comma_headroom f p k"
    and "P \<equiv> comma_period_displacement f (k mod 10) L"
    and "G \<equiv> comma_phase_max_guard f (k mod 10) L"
    and "c \<equiv> comma_safe_cycle_count H G P target"
  shows "c \<le> target"
    "comma_sector f p (comma_fixed_iter f (c * L) k)"
    "\<forall>j<c * L. comma_child (comma_fixed_iter f j k)
      (comma_fixed_iter f (Suc j) k) \<and>
      (\<forall>v. comma_child (comma_fixed_iter f j k) v \<longrightarrow>
        v = comma_fixed_iter f (Suc j) k)"
    "\<forall>j\<le>c * L. rtranclp comma_child k (comma_fixed_iter f j k)"
    "\<And>larger. c < larger \<Longrightarrow> larger \<le> target \<Longrightarrow>
      \<not> comma_phase_max_guard f (k mod 10) (larger * L) < H"
proof -
  have P_positive: "0 < P" using displacement by (simp add: P_def)
  have valid: "c \<le> target \<and> (c = 0 \<or> G + (c - 1) * P < H)"
    using comma_safe_cycle_count_characterization[OF P_positive,
      of c H G target]
    by (simp add: c_def)
  show c_target: "c \<le> target"
    using valid by simp
  have admissible: "c = 0 \<or> G + (c - 1) * P < H"
    using valid by simp
  have bound: "comma_phase_max_guard f (k mod 10) (c * L) < H"
    if positive: "0 < c"
  proof -
    have strict: "G + (c - 1) * P < H"
      using admissible positive by auto
    show ?thesis
      using strict comma_phase_max_guard_repeated[OF closes period positive,
        of "k mod 10"]
      by (simp add: G_def P_def add.commute)
  qed
  have endpoint_sector: "comma_sector f p (comma_fixed_iter f (c * L) k)"
    if "0 < c"
    using comma_phase_guard_endpoint_sector[OF source, of "c * L"]
      bound[OF that] period that by (simp add: H_def)
  show "comma_sector f p (comma_fixed_iter f (c * L) k)"
    using endpoint_sector source by (cases "c = 0") auto
  show edges: "\<forall>j<c * L. comma_child (comma_fixed_iter f j k)
      (comma_fixed_iter f (Suc j) k) \<and>
      (\<forall>v. comma_child (comma_fixed_iter f j k) v \<longrightarrow>
        v = comma_fixed_iter f (Suc j) k)"
  proof (cases "c = 0")
    case True
    then show ?thesis by simp
  next
    case False
    have positive: "0 < c" using False by simp
    have guard: "comma_phase_max_guard f (k mod 10) (c * L) <
        comma_headroom f p k"
      using bound[OF positive] by (simp add: H_def)
    show ?thesis
      by (rule comma_exact_phase_unique_path(1)[OF source exponent guard])
  qed
  show "\<forall>j\<le>c * L. rtranclp comma_child k (comma_fixed_iter f j k)"
  proof (cases "c = 0")
    case True
    then show ?thesis by simp
  next
    case False
    have positive: "0 < c" using False by simp
    have guard: "comma_phase_max_guard f (k mod 10) (c * L) <
        comma_headroom f p k"
      using bound[OF positive] by (simp add: H_def)
    show ?thesis
      by (rule comma_exact_phase_unique_path(2)[OF source exponent guard])
  qed
  fix larger
  assume greater: "c < larger" and within: "larger \<le> target"
  have nonadmitted: "G + (larger - 1) * P \<ge> H"
  proof -
    have "\<not> larger \<le> comma_safe_cycle_count H G P target"
      using greater by (simp add: c_def)
    then show ?thesis
      using comma_safe_cycle_count_characterization[OF P_positive,
        of larger H G target] within by auto
  qed
  have positive: "0 < larger" using greater by simp
  show "\<not> comma_phase_max_guard f (k mod 10) (larger * L) < H"
    using nonadmitted
      comma_phase_max_guard_repeated[OF closes period positive,
        of "k mod 10"]
    by (simp add: G_def P_def)
qed


ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_phase_digit_periodic comma_period_displacement_shift
      comma_period_displacement_repeated comma_phase_guard_periodic
      comma_phase_max_guard_repeated comma_safe_cycle_count_characterization
      comma_phase_guard_endpoint_sector comma_safe_cycle_count_maximal
      comma_safe_complete_cycles_refine})
    then () else error "Comma period guard proof depends on an oracle";
\<close>
end
