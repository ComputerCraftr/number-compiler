theory Comma_Fast_Arithmetic
  imports Comma_Entry_Arithmetic.Comma_Entry_Arithmetic
begin

text \<open>The finite arithmetic projections carry explicit checked tables.
The residual search below consumes at most one decimal phase cycle.\<close>

definition comma_cycle_length_fast :: "nat \<Rightarrow> nat" where
  "comma_cycle_length_fast f = [10,5,10,5,2,5,10,5,10] ! (f-1)"

definition comma_finite_period_fast :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_finite_period_fast f d =
    [[460, 460, 460, 460, 460, 460, 460, 460, 460, 460], [210, 260, 210, 260, 210, 260, 210, 260, 210, 260], [480, 480, 480, 480, 480, 480, 480, 480, 480, 480], [220, 270, 220, 270, 220, 270, 220, 270, 220, 270], [60, 80, 100, 120, 140, 60, 80, 100, 120, 140], [230, 280, 230, 280, 230, 280, 230, 280, 230, 280], [520, 520, 520, 520, 520, 520, 520, 520, 520, 520], [240, 290, 240, 290, 240, 290, 240, 290, 240, 290], [540, 540, 540, 540, 540, 540, 540, 540, 540, 540]] ! (f-1) ! d"

lemma comma_cycle_length_fast_checked:
  "list_all (\<lambda>f. comma_cycle_length_fast f = comma_cycle_length f) [1..<10]"
  by (tactic \<open>simp_tac
    (Comma_Entry_Arithmetic.natural_context @{context} |> Simplifier.add_simps
      @{thms comma_cycle_length_fast_def comma_compiled_cycle_length_facts
        list_all_Nil_iff list_all_Cons_iff upt_rec nth_Cons'}) 1\<close>)

lemma comma_cycle_length_fast_correct:
  assumes "1\<le>f" "f\<le>9"
  shows "comma_cycle_length_fast f = comma_cycle_length f"
  using comma_cycle_length_fast_checked assms
  by (auto simp: list_all_iff)

lemma comma_finite_period_fast_checked:
  "list_all (\<lambda>f. list_all (\<lambda>d.
    comma_finite_period_fast f d = comma_finite_period f d) [0..<10]) [1..<10]"
  by (tactic \<open>simp_tac
    (Comma_Entry_Arithmetic.natural_context @{context} |> Simplifier.add_simps
      @{thms comma_finite_period_fast_def comma_compiled_period_facts
        list_all_Nil_iff list_all_Cons_iff upt_rec nth_Cons'}) 1\<close>)

lemma comma_finite_period_fast_correct:
  assumes "1\<le>f" "f\<le>9" "d<10"
  shows "comma_finite_period_fast f d = comma_finite_period f d"
  using comma_finite_period_fast_checked assms
  by (auto simp: list_all_iff)


text \<open>Every table entry is checked against an existing closed modular-power
lemma. Execution uses the table and a short phase remainder only.\<close>

definition comma_power_table :: "nat \<Rightarrow> nat list" where
  "comma_power_table P =
    (if P = 60 then [40]
     else if P = 80 then [0]
     else if P = 100 then [0]
     else if P = 120 then [40]
     else if P = 140 then [40, 120, 80, 100, 20, 60]
     else if P = 210 then [40, 190, 10, 100, 160, 130]
     else if P = 220 then [120, 100]
     else if P = 230 then [180, 190, 60, 140, 20, 200, 160, 220, 130, 150, 120, 50, 40, 170, 90, 210, 30, 70, 10, 100, 80, 110]
     else if P = 240 then [160]
     else if P = 260 then [160, 40, 140, 100, 220, 120]
     else if P = 270 then [100, 190, 10]
     else if P = 280 then [40, 120, 80, 240, 160, 200]
     else if P = 290 then [240, 80, 220, 170, 250, 180, 60, 20, 200, 260, 280, 190, 160, 150, 50, 210, 70, 120, 40, 110, 230, 270, 90, 30, 10, 100, 130, 140]
     else if P = 460 then [180, 420, 60, 140, 20, 200, 160, 220, 360, 380, 120, 280, 40, 400, 320, 440, 260, 300, 240, 100, 80, 340]
     else if P = 480 then [160]
     else if P = 520 then [160, 40, 400, 360, 480, 120]
     else if P = 540 then [100, 460, 280]
     else [])"

lemma comma_power_table_checked:
  "list_all (\<lambda>P. list_all (\<lambda>j.
    comma_power_table P ! j = mod_exp (10::nat) (5+j) P)
    [0..<comma_short_period P])
    [60,80,100,120,140,210,220,230,240,260,270,280,290,460,480,520,540]"
  by (tactic \<open>simp_tac
    (Comma_Entry_Arithmetic.natural_context @{context} |> Simplifier.add_simps
      @{thms comma_power_table_def comma_compiled_short_period_facts
        comma_compiled_power_facts
        list_all_Nil_iff list_all_Cons_iff upt_rec nth_Cons'}) 1\<close>)

lemma comma_power_table_correct:
  assumes "P\<in>comma_cycle_displacements" "j<comma_short_period P"
  shows "comma_power_table P ! j = mod_exp (10::nat) (5+j) P"
  using comma_power_table_checked assms
  by (auto simp: list_all_iff comma_cycle_displacements_def)

definition comma_power_residue_fast :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_power_residue_fast P r =
    comma_power_table P ! ((r+919) mod comma_short_period P)"

lemma comma_power_residue_fast_correct:
  assumes "P\<in>comma_cycle_displacements"
  shows "comma_power_residue_fast P r = comma_power_residue P r"
proof -
  have positive: "0<comma_short_period P"
    using comma_short_period_catalog[OF assms] by blast
  have bound: "(r+919) mod comma_short_period P < comma_short_period P"
    using positive by simp
  show ?thesis
    using comma_power_table_correct[OF assms bound]
    by (simp only: comma_power_residue_fast_def comma_power_residue_rotated)
qed

definition comma_finite_headroom_fast ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_finite_headroom_fast f residue delta offset =
    (let P=comma_finite_period_fast f (offset mod 10);
         e=if f<9 then 1 else 0;
         power=comma_power_residue_fast P ((residue+delta) mod 924)
     in 1+e+nat ((int power-int offset-int (1+e)) mod int P))"

lemma comma_finite_headroom_fast_correct:
  assumes "1\<le>f" "f\<le>9"
  shows "comma_finite_headroom_fast f residue delta offset =
    comma_finite_headroom f residue delta offset"
proof -
  have period: "comma_finite_period_fast f (offset mod 10) =
    comma_finite_period f (offset mod 10)"
    by (rule comma_finite_period_fast_correct[OF assms]) simp
  have catalog: "comma_finite_period f (offset mod 10) \<in> comma_cycle_displacements"
    using comma_finite_period_in_catalog[rule_format, of f "offset mod 10"] assms by auto
  show ?thesis
    by (simp only: comma_finite_headroom_fast_def comma_finite_headroom_def
      period comma_finite_guard_extra_def
      comma_power_residue_fast_correct[OF catalog] Let_def)
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_power_table_checked comma_power_residue_fast_correct
      comma_finite_headroom_fast_correct}) then ()
    else error "Fast arithmetic depends on an oracle";
\<close>
end
