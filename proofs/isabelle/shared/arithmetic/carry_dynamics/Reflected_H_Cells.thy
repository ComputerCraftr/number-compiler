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
  val checked = @{thms reflected_H_cell_decodes_pairs reflected_H_cell_predecessor_factor
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
