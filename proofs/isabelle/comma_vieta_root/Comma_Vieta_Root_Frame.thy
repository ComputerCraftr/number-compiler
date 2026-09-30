theory Comma_Vieta_Root_Frame
  imports Comma_Frobenius_Entry.Comma_Frobenius_Entry
begin

text \<open>The ordered frame reuses the production phase and displacement
arithmetic. Roots are signed; neither a rank candidate nor a generated root
list is an input. A root-point equation does not by itself authenticate an
Entry occurrence's Frobenius phase or its next source.\<close>

definition comma_vieta_root :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int" where
  "comma_vieta_root M f orbit n = 10*int M-int orbit-
    int (comma_period_displacement f orbit n)-
    int (10*comma_phase_digit f orbit n+f+1)"

lemma comma_vieta_root_successor:
  "comma_vieta_root M f orbit (Suc n) = comma_vieta_root M f orbit n-
    int (10*comma_phase_digit f orbit (Suc n)+f)"
  by (simp add: comma_vieta_root_def comma_period_displacement_succ algebra_simps)

lemma comma_vieta_root_strict:
  assumes "1\<le>f"
  shows "comma_vieta_root M f orbit (Suc n)<comma_vieta_root M f orbit n"
proof -
  have f_nat_positive: "0<f" using assms by arith
  have f_positive: "0<int f" using f_nat_positive by simp
  have digit_nonnegative: "0\<le>int (comma_phase_digit f orbit (Suc n))" by simp
  have gap: "int (10*comma_phase_digit f orbit (Suc n)+f)=
    10*int (comma_phase_digit f orbit (Suc n))+int f" by simp
  show ?thesis using comma_vieta_root_successor[of M f orbit n]
    f_positive digit_nonnegative by (simp only: gap; linarith)

qed

lemma comma_vieta_root_headroom:
  assumes fits: "comma_period_displacement f orbit n\<le>H"
    and initial: "int H=10*int M-int orbit-10*int eta"
  shows "10*int eta-comma_vieta_root M f orbit n =
    int (10*comma_phase_digit f orbit n+f+1)-
      int (H-comma_period_displacement f orbit n)"
  using fits initial
  by (simp add: comma_vieta_root_def of_nat_diff; linarith)

text \<open>This is an actual displacement-prefix refinement, not a theorem
about a supplied event word. Its guard certifies every internal physical edge.
The headroom and Frobenius occurrence binding must still be supplied by the
canonical Entry constructor.\<close>

lemma comma_vieta_source_prefix:
  assumes sector: "1\<le>f" "f\<le>9" and initial: "H\<le>540"
    and digit: "orbit<10" and aligned: "(H+orbit) mod 10=0"
    and safe: "comma_period_displacement f orbit n+(if f<9 then 1 else 0)<H"
  shows "comma_near_prefix n f H (H-comma_period_displacement f orbit n)"
    "(10-(H-comma_period_displacement f orbit n) mod 10) mod 10=
      comma_phase_digit f orbit n"
proof -
  show "comma_near_prefix n f H (H-comma_period_displacement f orbit n)"
    by (rule comma_near_prefix_from_displacement[OF sector initial digit aligned safe])
  have fits: "comma_period_displacement f orbit n\<le>H" using safe by arith
  show "(10-(H-comma_period_displacement f orbit n) mod 10) mod 10=
      comma_phase_digit f orbit n"
    by (rule comma_near_phase_headroom_digit[OF digit aligned fits])
qed

definition comma_vieta_root_run :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_vieta_root_run f d u=(10*d+f-u+9) div 10"

text \<open>The small root-entry domain is indispensable. The run skips
translations to the FIRST previous-root boundary. It is not a claim that the
resulting previous root is already the normalized active root.\<close>

lemma comma_vieta_root_run_count:
  assumes "1\<le>f" "f\<le>9" "u<10" "u<10*d+f"
  shows "comma_vieta_root_run f d u=d+(if u<f then 1 else 0)"
proof (cases "u<f")
  case True
  show ?thesis unfolding comma_vieta_root_run_def
    apply (simp only: True if_True)
    apply (rule div_nat_eqI)
    using assms True by arith+
next
  case False
  show ?thesis unfolding comma_vieta_root_run_def
    apply (simp only: False if_False add_0_right)
    apply (rule div_nat_eqI)
    using assms False by arith+
qed

lemma comma_vieta_root_run_first_crossing:
  assumes "1\<le>f" "f\<le>9" "u<10" "u<10*d+f"
  shows "0<comma_vieta_root_run f d u"
    "10*d+f\<le>u+10*comma_vieta_root_run f d u"
    "u+10*comma_vieta_root_run f d u<10*d+f+10"
    "j<comma_vieta_root_run f d u \<Longrightarrow> u+10*j<10*d+f"
proof -
  have count: "comma_vieta_root_run f d u=d+(if u<f then 1 else 0)"
    by (rule comma_vieta_root_run_count[OF assms])
  show "0<comma_vieta_root_run f d u"
    using assms count by (auto split: if_splits; arith)
  show "10*d+f\<le>u+10*comma_vieta_root_run f d u"
    using assms count by (auto split: if_splits; arith)
  show "u+10*comma_vieta_root_run f d u<10*d+f+10"
    using assms count by (auto split: if_splits; arith)
  show "j<comma_vieta_root_run f d u \<Longrightarrow> u+10*j<10*d+f"
    using assms count by (auto split: if_splits; arith)
qed

lemma comma_vieta_root_run_residual:
  assumes "1\<le>f" "f\<le>9" "u<10" "u<10*d+f"
  shows "int u+10*int (comma_vieta_root_run f d u)-int (10*d+f)=
    (int u-int f) mod 10"
proof -
  have count: "comma_vieta_root_run f d u=d+(if u<f then 1 else 0)"
    by (rule comma_vieta_root_run_count[OF assms])
  have f_bound: "int f\<le>9" using assms(2) by simp
  have u_bound: "int u<10" using assms(3) by simp
  have u_nonnegative: "0\<le>int u" by simp
  have f_nonnegative: "0\<le>int f" by simp
  show ?thesis
  proof (cases "u<f")
    case True
    have order: "int u<int f" using True by simp
    have low: "0\<le>int u-int f+10" using f_bound u_nonnegative by linarith
    have high: "int u-int f+10<10" using order by linarith
    have shifted: "(int u-int f) mod 10=(int u-int f+10) mod 10" by simp
    have remainder: "(int u-int f) mod 10=int u-int f+10"
      using shifted mod_pos_pos_trivial[OF low high] by simp
    show ?thesis by (simp add: count True remainder algebra_simps)
  next
    case False
    have order: "int f\<le>int u" using False by simp
    have low: "0\<le>int u-int f" using order by linarith
    have high: "int u-int f<10" using u_bound f_nonnegative by linarith
    have remainder: "(int u-int f) mod 10=int u-int f"
      by (rule mod_pos_pos_trivial[OF low high])
    show ?thesis by (simp add: count False remainder algebra_simps)
  qed
qed

lemma comma_vieta_run_unguarded_counterexample:
  "comma_vieta_root_run 3 2 25=0"
  "(2::nat)+(if 25<(3::nat) then 1 else 0)=2"
  by (simp_all add: comma_vieta_root_run_def)

text \<open>A small digit alone does not characterize a fork. The EXACT
ordered root residual must vanish. These equations retain the actual Fast_Step
consumer and the local digit/headroom admission tests.\<close>

lemma comma_vieta_ordinary_terminal:
  assumes sector: "1\<le>f" "f<9"
    and valid: "1\<le>h" "h\<le>540"
    and digit: "d=(10-h mod 10) mod 10"
    and residual: "h+u=10*d+f+1"
  shows "comma_fast_step r (Comma_Near f delta h)=
    (if u=0 then Comma_Fork (f+1) delta
      else Comma_Next (Comma_Entry (f+1) delta u))"
    "u\<le>98"
proof -
  have bounds: "d<10" using digit by simp
  have admitted: "\<not>(f<1 \<or> 9<f \<or> h=0 \<or> 540<h)"
    using sector valid by arith
  have complement: "(10-h mod 10) mod 10=d" using digit by simp
  have internal: "\<not>(10*d+f+1<h)" using residual by arith
  have fork: "(h=10*d+f+1)=(u=0)" using residual by arith
  have offset: "10*d+f+1-h=u" using residual by arith
  show "comma_fast_step r (Comma_Near f delta h)=
    (if u=0 then Comma_Fork (f+1) delta
      else Comma_Next (Comma_Entry (f+1) delta u))"
    by (simp only: comma_fast_step.simps admitted if_False Let_def
      sector(2) if_True complement internal fork offset)
  show "u\<le>98" using sector valid bounds residual by arith
qed

lemma comma_vieta_sector_nine_terminal:
  assumes valid: "1\<le>h" "h\<le>540"
    and digit: "d=(10-h mod 10) mod 10"
    and upper_residual: "h+u=10*d+9"
  shows "comma_fast_step r (Comma_Near 9 delta h)=
    (if u<8 then Comma_Landmine delta
      else Comma_Next (Comma_Entry 1 (Suc delta) (u-8)))"
    "8\<le>u \<Longrightarrow> u-8\<le>90"
proof -
  have bounds: "d<10" using digit by simp
  have nine_not_lt: "\<not>((9::nat)<9)" by simp
  have nine_not_small: "\<not>((9::nat)<1)" by simp
  have h_nonzero: "h\<noteq>0" using valid(1) by arith
  have h_not_large: "\<not>(540<h)" using valid(2) by arith
  have complement: "(10-h mod 10) mod 10=d" using digit by simp
  have internal: "\<not>(10*d+9<h)" using upper_residual by arith
  have crossing: "(h\<le>10*d+1)=(8\<le>u)" using upper_residual by arith
  show "comma_fast_step r (Comma_Near 9 delta h)=
    (if u<8 then Comma_Landmine delta
      else Comma_Next (Comma_Entry 1 (Suc delta) (u-8)))"
  proof (cases "u<8")
    case True
    have no: "\<not>(8\<le>u)" using True by arith
    show ?thesis by (simp only: comma_fast_step.simps nine_not_small nine_not_lt
      h_nonzero h_not_large HOL.simp_thms if_False Let_def complement internal
      crossing True if_True no)
  next
    case False
    have yes: "8\<le>u" using False by arith
    have offset: "10*d+1-h=u-8" using upper_residual yes by arith
    show ?thesis by (simp only: comma_fast_step.simps nine_not_small nine_not_lt
      h_nonzero h_not_large HOL.simp_thms if_False Let_def complement internal
      crossing False yes if_True offset)
  qed
  show "8\<le>u \<Longrightarrow> u-8\<le>90"
    using valid bounds upper_residual by arith
qed

text \<open>The ordered-frame witness below has a canonical Entry clock:
exponent six and admitted offsets 55/65 produce diagonals nine/ten. These are
actual admitted Entry states, though no source-20 reachability is asserted.
Their translated points can cross more than one neighboring ordered root.\<close>

lemma comma_vieta_admitted_entry_clock:
  "comma_round_admitted (Comma_Entry 1 0 55)"
  "comma_round_admitted (Comma_Entry 1 0 65)"
  "comma_entry_diagonal_key 1 6 0 55=(5,9)"
  "comma_entry_diagonal_key 1 6 0 65=(5,10)"
  "comma_diagonal_headroom 1 460 5 9=365"
  "comma_diagonal_headroom 1 460 5 10=355"
  by (tactic \<open>ALLGOALS (simp_tac
    (Comma_Entry_Arithmetic.natural_context @{context} addsimps
      @{thms of_nat_numeral of_nat_0 of_nat_1 zmod_zminus1_eq_if
        zmod_zminus2_eq_if Num.inc.simps
        comma_round_admitted.simps comma_entry_diagonal_key_def
        comma_entry_diagonal_def comma_entry_alphabet_phase_def
        comma_finite_period_fast_def comma_short_period_def
        comma_power_table_def comma_diagonal_headroom_def nth_Cons'}))\<close>)

lemma comma_vieta_one_row_counterexample:
  "comma_vieta_root 46 1 5 4=99"
  "comma_vieta_root 46 1 5 5=98"
  "comma_vieta_root 46 1 5 6=87"
  "comma_vieta_root 46 1 5 6\<le>10*9 \<and>
    10*9<comma_vieta_root 46 1 5 5"
  "\<not>(comma_vieta_root 46 1 5 5\<le>10*10 \<and>
    10*10<comma_vieta_root 46 1 5 4)"
  by (tactic \<open>
    let
      val arithmetic = Comma_Entry_Arithmetic.natural_context @{context}
        addsimps @{thms of_nat_numeral of_nat_0 of_nat_1
          zmod_zminus1_eq_if zmod_zminus2_eq_if Num.inc.simps}
      val zero = Goal.prove @{context} [] []
        @{prop "comma_period_displacement 1 5 0=0"}
        (fn _ => simp_tac (@{context} addsimps
          @{thms comma_period_displacement_def}) 1)
      val steps = fold (fn step => fn known =>
          Simplifier.simplify
            (arithmetic addsimps known addsimps @{thms comma_phase_digit_def})
            step :: known)
        @{thms comma_period_displacement_succ[of 1 5 0]
          comma_period_displacement_succ[of 1 5 1]
          comma_period_displacement_succ[of 1 5 2]
          comma_period_displacement_succ[of 1 5 3]
          comma_period_displacement_succ[of 1 5 4]
          comma_period_displacement_succ[of 1 5 5]} [zero]
    in ALLGOALS (simp_tac (arithmetic addsimps steps
      addsimps @{thms comma_vieta_root_def comma_phase_digit_def})) end
    \<close>)

text \<open>The normalization unit is the complete ordered root interval.
A row translation may cross several roots. Select its first decisive phase
from the one actual digit period, instead of decrementing the old root once.
The guard offset is one in ordinary sectors and zero at the upper sector-9
wall; the separate lower wall remains in the terminal consumer.\<close>

definition comma_vieta_guard_root ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int" where
  "comma_vieta_guard_root e M f orbit n=comma_vieta_root M f orbit n+1-int e"

definition comma_vieta_root_index ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat option" where
  "comma_vieta_root_index L e M f orbit eta =
    List.find (\<lambda>n. comma_vieta_guard_root e M f orbit n\<le>10*int eta) [0..<L]"

lemma comma_vieta_guard_root_compare:
  assumes frame: "int H=10*int M-int orbit-10*int eta"
  shows "comma_vieta_guard_root e M f orbit n\<le>10*int eta \<longleftrightarrow>
    H\<le>comma_period_displacement f orbit (Suc n)+e"
proof -
  have equation: "comma_vieta_guard_root e M f orbit n=10*int eta+int H-
      int (comma_period_displacement f orbit (Suc n)+e)"
    using frame by (simp add: comma_vieta_guard_root_def comma_vieta_root_def
      comma_period_displacement_succ algebra_simps)
  show ?thesis
  proof
    assume root: "comma_vieta_guard_root e M f orbit n\<le>10*int eta"
    have "int H\<le>int (comma_period_displacement f orbit (Suc n)+e)"
      using root equation by linarith
    then show "H\<le>comma_period_displacement f orbit (Suc n)+e" by simp
  next
    assume bound: "H\<le>comma_period_displacement f orbit (Suc n)+e"
    have "int H\<le>int (comma_period_displacement f orbit (Suc n)+e)"
      using bound by simp
    then show "comma_vieta_guard_root e M f orbit n\<le>10*int eta"
      using equation by linarith
  qed
qed

lemma comma_vieta_root_index_selected:
  assumes "comma_vieta_root_index L e M f orbit eta=Some n"
  shows "n<L \<and> comma_vieta_guard_root e M f orbit n\<le>10*int eta \<and>
    (\<forall>j<n. 10*int eta<comma_vieta_guard_root e M f orbit j)"
  using assms by (auto simp: comma_vieta_root_index_def find_Some_iff)

lemma comma_vieta_root_index_exists:
  assumes length: "0<L" and period: "P=comma_period_displacement f orbit L"
    and frame: "int H=10*int M-int orbit-10*int eta"
    and bounded: "H\<le>P+e"
  shows "\<exists>n<L. comma_vieta_root_index L e M f orbit eta=Some n"
proof -
  have index: "L-1<L" and successor: "Suc (L-1)=L" using length by arith+
  note compare = comma_vieta_guard_root_compare[OF frame, where f=f and e=e]
  have last: "comma_vieta_guard_root e M f orbit (L-1)\<le>10*int eta"
    using compare[of "L-1"] period bounded successor by simp
  have member: "L-1\<in>set [0..<L]" using index by simp
  have not_none: "comma_vieta_root_index L e M f orbit eta\<noteq>None"
    using member last by (auto simp: comma_vieta_root_index_def find_None_iff)
  obtain n where selected: "comma_vieta_root_index L e M f orbit eta=Some n"
    using not_none by (cases "comma_vieta_root_index L e M f orbit eta") auto
  have "n<L" using comma_vieta_root_index_selected[OF selected] by blast
  then show ?thesis using selected by blast
qed

lemma comma_vieta_actual_phase_bound:
  assumes sector: "1\<le>f" "f\<le>9" and digit: "orbit<10"
  shows "0<comma_cycle_length f \<and> comma_cycle_length f\<le>10 \<and>
    comma_finite_period f orbit=
      comma_period_displacement f orbit (comma_cycle_length f)"
proof -
  have positive: "0<comma_cycle_length f"
    by (rule comma_cycle_length_admitted(1)[OF sector])
  have bounded: "comma_cycle_length f\<le>10" by (simp add: comma_cycle_length_def)
  have period: "comma_finite_period f orbit=
      comma_period_displacement f orbit (comma_cycle_length f)"
    by (rule comma_finite_period_refines[OF sector digit])
  show ?thesis using positive bounded period by blast
qed

lemma comma_vieta_root_index_refines_prefix:
  assumes sector: "1\<le>f" "f\<le>9"
    and initial: "H\<le>540" and digit: "orbit<10"
    and aligned: "(H+orbit) mod 10=0"
    and extra: "e=(if f<9 then 1 else 0)" and positive: "e<H"
    and frame: "int H=10*int M-int orbit-10*int eta"
    and selected: "comma_vieta_root_index L e M f orbit eta=Some n"
  shows "comma_near_prefix n f H (H-comma_period_displacement f orbit n) \<and>
    comma_near_germ f H=(n,H-comma_period_displacement f orbit n)"
proof -
  have first: "comma_vieta_guard_root e M f orbit n\<le>10*int eta"
    and earlier: "\<forall>j<n. 10*int eta<comma_vieta_guard_root e M f orbit j"
    using comma_vieta_root_index_selected[OF selected] by blast+
  note compare = comma_vieta_guard_root_compare[OF frame, where f=f and e=e]
  have maximal: "H\<le>comma_period_displacement f orbit (Suc n)+e"
    using first compare[of n] by blast
  have safe: "comma_period_displacement f orbit n+e<H"
  proof (cases n)
    case 0
    then show ?thesis using positive by (simp add: comma_period_displacement_def)
  next
    case (Suc j)
    have prior: "10*int eta<comma_vieta_guard_root e M f orbit j"
      using earlier Suc by auto
    have "\<not>(H\<le>comma_period_displacement f orbit (Suc j)+e)"
      using prior compare[of j] by auto
    then show ?thesis by (simp add: Suc not_le)
  qed
  have safe_actual: "comma_period_displacement f orbit n+(if f<9 then 1 else 0)<H"
    using safe extra by simp
  have maximal_actual: "H\<le>comma_period_displacement f orbit (Suc n)+(if f<9 then 1 else 0)"
    using maximal extra by simp
  have prefix: "comma_near_prefix n f H (H-comma_period_displacement f orbit n)"
    by (rule comma_near_prefix_from_displacement[OF sector initial digit aligned safe_actual])
  have germ: "comma_near_germ f H=(n,H-comma_period_displacement f orbit n)"
    by (rule comma_near_germ_from_maximal_displacement
      [OF sector initial digit aligned safe_actual maximal_actual])
  show ?thesis using prefix germ by blast
qed

corollary comma_vieta_bounded_root_constructor:
  assumes sector: "1\<le>f" "f\<le>9"
    and initial: "H\<le>540" and digit: "orbit<10"
    and aligned: "(H+orbit) mod 10=0"
    and extra: "e=(if f<9 then 1 else 0)" and positive: "e<H"
    and frame: "int H=10*int M-int orbit-10*int eta"
    and bounded: "H\<le>comma_finite_period f orbit+e"
  shows "\<exists>n<10. comma_vieta_root_index (comma_cycle_length f) e M f orbit eta=Some n \<and>
    comma_near_germ f H=(n,H-comma_period_displacement f orbit n)"
proof -
  have phase: "0<comma_cycle_length f" "comma_cycle_length f\<le>10"
    "comma_finite_period f orbit=
      comma_period_displacement f orbit (comma_cycle_length f)"
    using comma_vieta_actual_phase_bound[OF sector digit] by blast+
  obtain n where index: "n<comma_cycle_length f"
    and selected: "comma_vieta_root_index (comma_cycle_length f) e M f orbit eta=Some n"
    using comma_vieta_root_index_exists[OF phase(1,3) frame bounded] by blast
  have germ: "comma_near_germ f H=(n,H-comma_period_displacement f orbit n)"
    using comma_vieta_root_index_refines_prefix
      [OF sector initial digit aligned extra positive frame selected] by blast
  show ?thesis using index selected germ phase(2) by auto
qed

text \<open>The first-hit remainder above is interim. A second crossing may
be required. The next lemma uses the actual adjacent decimal phases; it does
not assume that each individual gap exceeds ten. The ordered finite-period
selector remains authoritative at a cyclic wrap.\<close>

definition comma_vieta_phase_gap :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_vieta_phase_gap f orbit n=10*comma_phase_digit f orbit n+f"

lemma comma_vieta_phase_digit_successor:
  "comma_phase_digit f orbit (Suc n)=(comma_phase_digit f orbit n+f) mod 10"
  by (simp add: comma_phase_digit_def algebra_simps mod_add_left_eq mod_add_right_eq)

lemma comma_vieta_two_gaps:
  assumes sector: "1\<le>f" "f\<le>9"
  shows "12\<le>comma_vieta_phase_gap f orbit n+
    comma_vieta_phase_gap f orbit (Suc n)"
proof (cases "comma_phase_digit f orbit n=0")
  case True
  have small: "f<10" using sector by arith
  have phase_next: "comma_phase_digit f orbit (Suc n)=f"
    using comma_vieta_phase_digit_successor[of f orbit n] True small by simp
  show ?thesis unfolding comma_vieta_phase_gap_def using sector True phase_next by arith
next
  case False
  have digit: "1\<le>comma_phase_digit f orbit n" using False by arith
  show ?thesis unfolding comma_vieta_phase_gap_def using sector digit by arith
qed

text \<open>The returned pair is (ordered-root crossings, residual). This
local port accepts an arbitrary admitted chamber residual u below its first
gap. The separate pumped first-hit count requires u below ten; its formula
must not be promoted to an arbitrary chamber.\<close>

definition comma_vieta_row_port :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat\<times>nat" where
  "comma_vieta_row_port first second u =
    (if u+10<first then (0,u+10)
     else if u+10-first<second then (1,u+10-first)
     else (2,u+10-first-second))"

lemma comma_vieta_row_port_refines:
  assumes sector: "1\<le>f" "f\<le>9"
    and chamber: "u<comma_vieta_phase_gap f orbit (Suc (Suc j))"
    and port: "comma_vieta_row_port
      (comma_vieta_phase_gap f orbit (Suc (Suc j)))
      (comma_vieta_phase_gap f orbit (Suc j)) u=(crossed,residual)"
  shows "crossed\<le>2 \<and>
    residual<comma_vieta_phase_gap f orbit (Suc (Suc j)-crossed) \<and>
    comma_vieta_root M f orbit (Suc (Suc j))+int u+10=
      comma_vieta_root M f orbit (Suc (Suc j)-crossed)+int residual"
proof -
  let ?a = "comma_vieta_phase_gap f orbit (Suc (Suc j))"
  let ?b = "comma_vieta_phase_gap f orbit (Suc j)"
  let ?c = "comma_vieta_phase_gap f orbit j"
  have two: "10<?c+?b" using comma_vieta_two_gaps[OF sector, of orbit j] by arith
  have first_root: "comma_vieta_root M f orbit (Suc (Suc j))=
      comma_vieta_root M f orbit (Suc j)-int ?a"
    by (simp add: comma_vieta_root_successor comma_vieta_phase_gap_def)
  have second_root: "comma_vieta_root M f orbit (Suc j)=
      comma_vieta_root M f orbit j-int ?b"
    by (simp add: comma_vieta_root_successor comma_vieta_phase_gap_def)
  show ?thesis
  proof (cases "u+10<?a")
    case True
    have result: "crossed=0" "residual=u+10"
      using port True by (simp_all add: comma_vieta_row_port_def)
    show ?thesis using True result by simp
  next
    case False
    have fits: "?a\<le>u+10" using False by arith
    have interim: "u+10-?a<10" using chamber fits by arith
    show ?thesis
    proof (cases "u+10-?a<?b")
      case True
      have result: "crossed=1" "residual=u+10-?a"
        using port False True by (simp_all add: comma_vieta_row_port_def)
      have exact: "int (u+10-?a)=int u+10-int ?a"
        using fits by (simp add: of_nat_diff)
      show ?thesis using result True first_root exact by simp
    next
      case False
      have fits_second: "?b\<le>u+10-?a" using False by arith
      have result: "crossed=2" "residual=u+10-?a-?b"
        using port fits False by (simp_all add: comma_vieta_row_port_def not_less)
      have bound: "u+10-?a-?b<?c" using interim two fits_second by arith
      have exact: "int (u+10-?a-?b)=int u+10-int ?a-int ?b"
        using fits fits_second by (simp add: of_nat_diff)
      show ?thesis using result bound first_root second_root exact by simp
    qed
  qed
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_vieta_root_successor comma_vieta_root_strict
      comma_vieta_root_headroom comma_vieta_source_prefix
      comma_vieta_root_run_count comma_vieta_root_run_first_crossing
      comma_vieta_root_run_residual
      comma_vieta_run_unguarded_counterexample comma_vieta_ordinary_terminal
      comma_vieta_sector_nine_terminal comma_vieta_admitted_entry_clock
      comma_vieta_one_row_counterexample comma_vieta_guard_root_compare
      comma_vieta_root_index_selected comma_vieta_root_index_exists
      comma_vieta_actual_phase_bound comma_vieta_root_index_refines_prefix
      comma_vieta_bounded_root_constructor comma_vieta_phase_digit_successor
      comma_vieta_two_gaps comma_vieta_row_port_refines})
    then () else error "Comma Vieta root frame depends on an oracle";
\<close>
end
