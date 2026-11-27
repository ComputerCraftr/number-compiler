theory Reflected_H_Cells
  imports Reflected_Padded_Orbit Overlap_Quarter
begin

text \<open>Physical digits are LSD-first. The predecessor of digit zero is
the padded zero. The multiplication and E laws share the radix quotient q.\<close>

definition reflected_previous :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat" where
  "reflected_previous source index = (if index = 0 then 0 else source (index - 1))"

definition reflected_M_digit :: "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat" where
  "reflected_M_digit multiplier source index =
    multiplier * (source index mod (10 div multiplier)) +
      reflected_previous source index div (10 div multiplier)"

definition reflected_E_digit :: "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat" where
  "reflected_E_digit multiplier source index =
    source index div (10 div multiplier) +
      multiplier * (reflected_previous source index mod (10 div multiplier))"

definition reflected_H_digit :: "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat" where
  "reflected_H_digit multiplier source =
    reflected_E_digit multiplier (reflected_M_digit multiplier source)"

text \<open>The source-relative scan in the diagonal executor checks this exact
 two-tick response at each interior column before allocating a tile table.
 The first two columns retain their physical boundary treatment.\<close>

theorem reflected_H_two_tick_interior:
  assumes "2 \<le> i"
  shows "reflected_H_digit multiplier source i =
    multiplier * ((multiplier * (source (i - 1) mod (10 div multiplier)) +
      source (i - 2) div (10 div multiplier)) mod (10 div multiplier)) +
    (multiplier * (source i mod (10 div multiplier)) +
      source (i - 1) div (10 div multiplier)) div (10 div multiplier)"
proof -
  have nz: "i \<noteq> 0" "i - 1 \<noteq> 0" using assms by arith+
  have sub: "i - 1 - 1 = i - 2" by (simp add: diff_diff_add)
  show ?thesis
    unfolding reflected_H_digit_def reflected_E_digit_def
      reflected_M_digit_def reflected_previous_def
    by (simp only: nz if_False sub add.commute)
qed

lemma reflected_H_two_tick_zero_boundary:
  "reflected_H_digit multiplier source 0 =
    (multiplier * (source 0 mod (10 div multiplier))) div (10 div multiplier)"
  by (simp add: reflected_H_digit_def reflected_E_digit_def reflected_M_digit_def reflected_previous_def)

definition reflected_relative_two ::
  "('a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> (int \<Rightarrow> 'a) \<Rightarrow> int \<Rightarrow> 'a" where
  "reflected_relative_two gate source i = gate (source (i - 2)) (source (i - 1)) (source i)"

text \<open>A checked relative return on every source triple propagates through
 the protected interval.  The left margin charges the full two-cell cone per
 return; the exact source shift remains separate from that safety margin.\<close>

theorem reflected_relative_interval:
  fixes a b shift :: int
  assumes shift: "0 \<le> shift" "shift \<le> 2"
    and returns: "\<And>j. a + 2 \<le> j \<Longrightarrow> j < b \<Longrightarrow>
      reflected_relative_two gate source j = source (j - shift)"
    and bounds: "a + 2 * int n \<le> i" "i < b"
  shows "((reflected_relative_two gate ^^ n) source) i = source (i - int n * shift)"
  using bounds
proof (induction n arbitrary: i)
  case 0
  then show ?case by simp
next
  case (Suc n)
  let ?k = "i - int n * shift"
  have left: "a + 2 * int n \<le> i - 2" using Suc.prems by (simp; linarith)
  have middle: "a + 2 * int n \<le> i - 1" using Suc.prems by (simp; linarith)
  have right: "a + 2 * int n \<le> i" using Suc.prems by (simp; linarith)
  have previous: "i - 2 < b" "i - 1 < b" using Suc.prems by simp_all
  have nonneg: "0 \<le> int n" by simp
  have bounded: "int n * shift \<le> 2 * int n"
    using mult_left_mono[OF shift(2) nonneg] by (simp add: mult.commute)
  have positive: "0 \<le> int n * shift"
    by (rule mult_nonneg_nonneg[OF nonneg shift(1)])
  have lower: "a + 2 \<le> ?k" using Suc.prems bounded by (simp; linarith)
  have upper: "?k < b" using Suc.prems positive by linarith
  have step: "reflected_relative_two gate ((reflected_relative_two gate ^^ n) source) i =
      reflected_relative_two gate source ?k"
    using Suc.IH[OF left previous(1)] Suc.IH[OF middle previous(2)]
      Suc.IH[OF right Suc.prems(2)]
    unfolding reflected_relative_two_def by (simp add: algebra_simps)
  show ?case using step returns[OF lower upper]
    by (simp add: funpow_Suc_right algebra_simps)
qed

theorem reflected_relative_interval_odd:
  fixes a b shift :: int
  assumes shift: "0 \<le> shift" "shift \<le> 2"
    and returns: "\<And>j. a + 2 \<le> j \<Longrightarrow> j < b \<Longrightarrow>
      reflected_relative_two gate source j = source (j - shift)"
    and bounds: "a + 2 * int n + 1 \<le> i" "i < b"
  shows "one (((reflected_relative_two gate ^^ n) source) (i - 1))
      (((reflected_relative_two gate ^^ n) source) i) =
    one (source (i - 1 - int n * shift)) (source (i - int n * shift))"
proof -
  have l: "a + 2 * int n \<le> i - 1" "i - 1 < b" using bounds by linarith+
  have r: "a + 2 * int n \<le> i" using bounds by linarith
  show ?thesis using reflected_relative_interval[OF shift returns l]
    reflected_relative_interval[OF shift returns r bounds(2)] by simp
qed

theorem reflected_relative_two_checked_cell:
  assumes "2 \<le> i"
  shows "reflected_relative_two
      (\<lambda>left middle right.
        let q = 10 div multiplier;
            x = multiplier * (middle mod q) + left div q;
            y = multiplier * (right mod q) + middle div q
        in multiplier * (x mod q) + y div q)
      (\<lambda>j. source (nat j)) (int i) =
    reflected_H_digit multiplier source i"
  using assms reflected_H_two_tick_interior[of i multiplier source]
  by (simp add: reflected_relative_two_def Let_def nat_diff_distrib)

definition reflected_H_pair_parts :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<times> nat" where
  "reflected_H_pair_parts multiplier previous_low previous_high current_low current_high =
    (let q = 10 div multiplier;
         before = multiplier * (previous_high mod q) + previous_low div q;
         first = multiplier * (current_low mod q) + previous_high div q;
         second = multiplier * (current_high mod q) + current_low div q
     in (first div q + multiplier * (before mod q),
       second div q + multiplier * (first mod q)))"

definition reflected_H_pair :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "reflected_H_pair multiplier previous_low previous_high current_low current_high =
    (let parts = reflected_H_pair_parts multiplier previous_low previous_high current_low current_high
     in fst parts + 10 * snd parts)"

definition reflected_H_cell :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "reflected_H_cell multiplier previous current =
    reflected_H_pair multiplier (previous mod 10) (previous div 10)
      (current mod 10) (current div 10)"

lemma reflected_H_cell_decodes_pairs:
  assumes "previous_low < 10" "current_low < 10"
  shows "reflected_H_cell multiplier
      (previous_low + 10 * previous_high) (current_low + 10 * current_high) =
    reflected_H_pair multiplier previous_low previous_high current_low current_high"
  using assms by (simp add: reflected_H_cell_def add.commute)

lemma reflected_H_cell_predecessor_factor:
  fixes multiplier previous current :: nat
  defines "q \<equiv> 10 div multiplier"
  defines "carry \<equiv> (previous div 10) div q"
  defines "first \<equiv> multiplier * (current mod 10 mod q) + carry"
  shows "reflected_H_cell multiplier previous current =
    multiplier * ((multiplier * (previous div 10 mod q) + previous mod 10 div q) mod q) +
      (first div q + 10 * multiplier * (first mod q) +
        10 * ((multiplier * (current div 10 mod q) + current mod 10 div q) div q))"
  unfolding q_def carry_def first_def
  by (simp add: reflected_H_cell_def reflected_H_pair_def reflected_H_pair_parts_def
      Let_def algebra_simps)

theorem reflected_H_pair_digit_bridge:
  assumes "0 < cell"
  shows "reflected_H_digit multiplier source (2 * cell) +
      10 * reflected_H_digit multiplier source (2 * cell + 1) =
    reflected_H_pair multiplier (source (2 * (cell - 1)))
      (source (2 * (cell - 1) + 1)) (source (2 * cell))
      (source (2 * cell + 1))"
proof -
  obtain k where cell: "cell = Suc k" using assms by (cases cell) auto
  show ?thesis unfolding cell
    by (simp add: reflected_H_digit_def reflected_E_digit_def reflected_M_digit_def
        reflected_previous_def reflected_H_pair_def reflected_H_pair_parts_def
        Let_def algebra_simps)
qed

theorem reflected_H_pair_zero_bridge:
  "reflected_H_digit multiplier source 0 +
      10 * reflected_H_digit multiplier source 1 =
    reflected_H_pair multiplier 0 0 (source 0) (source 1)"
  by (simp add: reflected_H_digit_def reflected_E_digit_def reflected_M_digit_def
      reflected_previous_def reflected_H_pair_def reflected_H_pair_parts_def Let_def)

definition reflected_pair_at :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<times> nat" where
  "reflected_pair_at source cell = (source (2 * cell), source (2 * cell + 1))"

definition reflected_pair_action :: "nat \<Rightarrow> (nat \<times> nat) \<Rightarrow> (nat \<times> nat) \<Rightarrow> nat \<times> nat" where
  "reflected_pair_action multiplier current previous =
    reflected_H_pair_parts multiplier (fst previous) (snd previous)
      (fst current) (snd current)"

theorem reflected_H_pair_parts_bridge:
  assumes "0 < cell"
  shows "(reflected_H_digit multiplier source (2 * cell),
      reflected_H_digit multiplier source (2 * cell + 1)) =
    reflected_pair_action multiplier (reflected_pair_at source cell)
      (reflected_pair_at source (cell - 1))"
proof -
  obtain k where cell: "cell = Suc k" using assms by (cases cell) auto
  show ?thesis unfolding cell
    by (simp add: reflected_H_digit_def reflected_E_digit_def reflected_M_digit_def
        reflected_previous_def reflected_pair_action_def reflected_pair_at_def
        reflected_H_pair_parts_def Let_def algebra_simps)
qed

theorem reflected_H_pair_parts_zero:
  "(reflected_H_digit multiplier source 0, reflected_H_digit multiplier source 1) =
    reflected_pair_action multiplier (reflected_pair_at source 0) (0, 0)"
  by (simp add: reflected_H_digit_def reflected_E_digit_def reflected_M_digit_def
      reflected_previous_def reflected_pair_action_def reflected_pair_at_def
      reflected_H_pair_parts_def Let_def)

theorem reflected_H_pair_overlap_one_step:
  assumes "0 < cell"
  shows "overlap_run (reflected_pair_action multiplier) 1
      (\<lambda>i. reflected_pair_at source (cell - i)) 0 =
    (reflected_H_digit multiplier source (2 * cell),
      reflected_H_digit multiplier source (2 * cell + 1))"
  using reflected_H_pair_parts_bridge[OF assms, of multiplier source]
  by simp

theorem reflected_H_pair_overlap_dyadic:
  "overlap_recursive order (reflected_pair_action multiplier) source i =
    overlap_run (reflected_pair_action multiplier) (2 ^ order) source i"
  by (rule overlap_recursive_exact)

fun reflected_H_digit_iter ::
  "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat" where
  "reflected_H_digit_iter multiplier 0 source = source"
| "reflected_H_digit_iter multiplier (Suc steps) source =
    reflected_H_digit multiplier (reflected_H_digit_iter multiplier steps source)"

fun reflected_single_run ::
  "(nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow>
    (int \<Rightarrow> 'a) \<Rightarrow> int \<Rightarrow> 'a" where
  "reflected_single_run gate 0 source = source"
| "reflected_single_run gate (Suc n) source =
    (\<lambda>i. gate n (reflected_single_run gate n source (i - 1))
      (reflected_single_run gate n source i))"

theorem reflected_single_run_locality:
  assumes same: "\<And>j. i - int n \<le> j \<Longrightarrow> j \<le> i \<Longrightarrow>
      source j = other j"
  shows "reflected_single_run gate n source i = reflected_single_run gate n other i"
  using same
proof (induction n arbitrary: i)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have left: "reflected_single_run gate n source (i - 1) =
      reflected_single_run gate n other (i - 1)"
    by (rule Suc.IH) (use Suc.prems in \<open>auto; linarith\<close>)
  have right: "reflected_single_run gate n source i =
      reflected_single_run gate n other i"
    by (rule Suc.IH) (use Suc.prems in \<open>auto; linarith\<close>)
  show ?case by (simp only: reflected_single_run.simps left right)
qed

definition reflected_clip :: "int \<Rightarrow> int \<Rightarrow> (int \<Rightarrow> nat) \<Rightarrow> int \<Rightarrow> nat" where
  "reflected_clip a b source j = (if a \<le> j \<and> j < b then source j else 0)"

theorem reflected_single_run_clip:
  assumes "a \<le> i - int n" "i < b"
  shows "reflected_single_run gate n source i =
    reflected_single_run gate n (reflected_clip a b source) i"
  by (rule reflected_single_run_locality)
     (use assms in \<open>auto simp: reflected_clip_def; linarith\<close>)

theorem reflected_prefix_fringe:
  fixes a i :: int
  assumes zero: "\<And>j. j < 0 \<Longrightarrow> source j = 0"
    and bound: "i < a + int n"
  shows "reflected_single_run gate n source i =
    reflected_single_run gate n (reflected_clip 0 (a + int n) source) i"
  by (rule reflected_single_run_locality)
     (use zero bound in \<open>auto simp: reflected_clip_def; linarith\<close>)

theorem reflected_suffix_fringe:
  fixes b i limit :: int
  assumes "b \<le> i" "i < limit"
  shows "reflected_single_run gate n source i =
    reflected_single_run gate n (reflected_clip (b - int n) limit source) i"
  by (rule reflected_single_run_clip) (use assms in \<open>linarith\<close>)+

definition reflected_source_two_gate :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "reflected_source_two_gate m l d r =
    (let q = 10 div m; x = m * (d mod q) + l div q;
         y = m * (r mod q) + d div q
     in m * (x mod q) + y div q)"

definition reflected_alternating_gate :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "reflected_alternating_gate m t l r =
    (if even t then m * (r mod (10 div m)) + l div (10 div m)
     else r div (10 div m) + m * (l mod (10 div m)))"

lemma reflected_single_two_gates:
  "reflected_single_run (reflected_alternating_gate m) 2 source i =
    reflected_relative_two (reflected_source_two_gate m) source i"
  by (simp add: numeral_2_eq_2 reflected_alternating_gate_def reflected_relative_two_def
      reflected_source_two_gate_def Let_def add.commute diff_diff_add)

theorem reflected_single_run_even:
  "reflected_single_run (reflected_alternating_gate m) (2 * n) source =
    (reflected_relative_two (reflected_source_two_gate m) ^^ n) source"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have clock: "2 * Suc n = Suc (Suc (2 * n))" by simp
  show ?case unfolding clock
    using Suc.IH
    by (simp add: reflected_alternating_gate_def reflected_relative_two_def
        reflected_source_two_gate_def funpow_Suc_right Let_def add.commute diff_diff_add)
qed

theorem reflected_single_run_odd_relative:
  fixes a b shift i :: int
  assumes shift: "0 \<le> shift" "shift \<le> 2"
    and returns: "\<And>j. a + 2 \<le> j \<Longrightarrow> j < b \<Longrightarrow>
      reflected_relative_two (reflected_source_two_gate m) source j = source (j - shift)"
    and bounds: "a + 2 * int n + 1 \<le> i" "i < b"
  shows "reflected_single_run (reflected_alternating_gate m) (Suc (2 * n)) source i =
    m * (source (i - int n * shift) mod (10 div m)) +
      source (i - 1 - int n * shift) div (10 div m)"
proof -
  have response:
    "reflected_alternating_gate m (2 * n)
      (((reflected_relative_two (reflected_source_two_gate m) ^^ n) source) (i - 1))
      (((reflected_relative_two (reflected_source_two_gate m) ^^ n) source) i) =
    reflected_alternating_gate m (2 * n)
      (source (i - 1 - int n * shift)) (source (i - int n * shift))"
    by (rule reflected_relative_interval_odd[OF shift returns bounds])
  show ?thesis using response
    by (simp add: reflected_single_run_even reflected_alternating_gate_def)
qed

lemma reflected_relative_two_H_iter:
  assumes "2 * int n \<le> i"
  shows "((reflected_relative_two (reflected_source_two_gate m) ^^ n)
      (\<lambda>j. source (nat j))) i = reflected_H_digit_iter m n source (nat i)"
  using assms
proof (induction n arbitrary: i)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have b: "2 * int n \<le> i - 2" "2 * int n \<le> i - 1" "2 * int n \<le> i"
    using Suc.prems by (simp; linarith)+
  have nonneg: "0 \<le> int n" by simp
  have i2: "(2::int) \<le> i" using Suc.prems nonneg by (simp; linarith)
  have pos: "2 \<le> nat i" using i2 by (simp add: le_nat_iff)
  have j1: "nat (i - 1) = nat i - 1" using i2 by (simp add: nat_diff_distrib)
  have j2: "nat (i - 2) = nat i - 2" using i2 by (simp add: nat_diff_distrib)
  show ?case using Suc.IH[OF b(1)] Suc.IH[OF b(2)] Suc.IH[OF b(3)]
    reflected_H_two_tick_interior[OF pos, of m "reflected_H_digit_iter m n source"]
    by (simp add: funpow_Suc_right reflected_relative_two_def reflected_source_two_gate_def
        Let_def j1 j2 algebra_simps)
qed

theorem reflected_source_relative_H_interior:
  fixes a b shift i :: int
  assumes "0 \<le> a" "0 \<le> shift" "shift \<le> 2"
    and returns: "\<And>j. a + 2 \<le> j \<Longrightarrow> j < b \<Longrightarrow>
      reflected_relative_two (reflected_source_two_gate m) (\<lambda>k. source (nat k)) j =
        source (nat (j - shift))"
    and bounds: "a + 2 * int n \<le> i" "i < b"
  shows "reflected_H_digit_iter m n source (nat i) = source (nat (i - int n * shift))"
proof -
  have interior: "2 * int n \<le> i" using assms by linarith
  show ?thesis using reflected_relative_interval[OF assms(2,3) returns bounds]
    reflected_relative_two_H_iter[OF interior, of m source] by simp
qed

theorem reflected_H_overlap_physical_window:
  assumes "i + steps < cell"
  shows "overlap_run (reflected_pair_action multiplier) steps
      (\<lambda>j. reflected_pair_at source (cell - j)) i =
    (reflected_H_digit_iter multiplier steps source (2 * (cell - i)),
     reflected_H_digit_iter multiplier steps source (2 * (cell - i) + 1))"
  using assms
proof (induction steps arbitrary: i)
  case 0
  then show ?case by (simp add: reflected_pair_at_def)
next
  case (Suc steps)
  have first: "i + steps < cell" using Suc.prems by arith
  have second: "Suc i + steps < cell" using Suc.prems by arith
  have positive: "0 < cell - i" using Suc.prems by arith
  have index: "cell - Suc i = cell - i - 1" using Suc.prems by arith
  have one: "overlap_run (reflected_pair_action multiplier) steps
        (\<lambda>j. reflected_pair_at source (cell - j)) i =
      reflected_pair_at (reflected_H_digit_iter multiplier steps source) (cell - i)"
    using Suc.IH[OF first] by (simp only: reflected_pair_at_def)
  have two: "overlap_run (reflected_pair_action multiplier) steps
        (\<lambda>j. reflected_pair_at source (cell - j)) (Suc i) =
      reflected_pair_at (reflected_H_digit_iter multiplier steps source) (cell - i - 1)"
    using Suc.IH[OF second] by (simp only: reflected_pair_at_def index)
  have step: "(reflected_H_digit multiplier (reflected_H_digit_iter multiplier steps source)
        (2 * (cell - i)),
      reflected_H_digit multiplier (reflected_H_digit_iter multiplier steps source)
        (2 * (cell - i) + 1)) =
    reflected_pair_action multiplier
      (reflected_pair_at (reflected_H_digit_iter multiplier steps source) (cell - i))
      (reflected_pair_at (reflected_H_digit_iter multiplier steps source) (cell - i - 1))"
    by (rule reflected_H_pair_parts_bridge[OF positive])
  show ?case by (simp only: overlap_run.simps reflected_H_digit_iter.simps one two step)
qed

corollary reflected_H_dyadic_physical_window:
  assumes "i + 2 ^ order < cell"
  shows "overlap_recursive order (reflected_pair_action multiplier)
      (\<lambda>j. reflected_pair_at source (cell - j)) i =
    (reflected_H_digit_iter multiplier (2 ^ order) source (2 * (cell - i)),
     reflected_H_digit_iter multiplier (2 ^ order) source (2 * (cell - i) + 1))"
  unfolding overlap_recursive_exact
  by (rule reflected_H_overlap_physical_window[OF assms])

definition reflected_padded_source :: "nat list \<Rightarrow> nat \<Rightarrow> nat" where
  "reflected_padded_source word i = (if i < length word then word ! i else 0)"

corollary reflected_H_dyadic_source_window:
  assumes "i + 2 ^ order < cell"
  shows "overlap_recursive order (reflected_pair_action multiplier)
      (\<lambda>j. reflected_pair_at (reflected_padded_source word) (cell - j)) i =
    (reflected_H_digit_iter multiplier (2 ^ order) (reflected_padded_source word)
       (2 * (cell - i)),
     reflected_H_digit_iter multiplier (2 ^ order) (reflected_padded_source word)
       (2 * (cell - i) + 1))"
  by (rule reflected_H_dyadic_physical_window[OF assms])

ML \<open>
  val checked = @{thms reflected_H_two_tick_interior reflected_H_two_tick_zero_boundary
    reflected_relative_interval reflected_relative_interval_odd reflected_relative_two_checked_cell
    reflected_relative_two_H_iter reflected_source_relative_H_interior
    reflected_single_run_locality reflected_single_run_clip reflected_prefix_fringe
    reflected_suffix_fringe reflected_single_two_gates reflected_single_run_even
    reflected_single_run_odd_relative
    reflected_H_cell_decodes_pairs reflected_H_cell_predecessor_factor
    reflected_H_pair_digit_bridge reflected_H_pair_zero_bridge
    reflected_H_pair_parts_bridge reflected_H_pair_parts_zero
    reflected_H_pair_overlap_one_step reflected_H_dyadic_physical_window
    reflected_H_dyadic_source_window};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Reflected H cell proof depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked
    then error "Skipped reflected H cell proof" else ();
\<close>

end
