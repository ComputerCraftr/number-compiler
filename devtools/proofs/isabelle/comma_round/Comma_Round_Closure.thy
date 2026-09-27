theory Comma_Round_Closure
  imports Comma_Chart_Bridge.Comma_Chart_Refinement
begin

text \<open>A round follows the canonical finite chart action.  It ends at the
first terminal event or at the first 9-to-1 decimal crossing; this derived
control does not decide which fork child survives.\<close>

fun comma_round_measure :: "comma_finite_position \<Rightarrow> nat" where
  "comma_round_measure (Comma_Entry f delta offset) =
    (9 - f) * 1024 + 600"
| "comma_round_measure (Comma_Near f delta headroom) =
    (9 - f) * 1024 + headroom"

definition comma_round_crossing ::
  "comma_finite_position \<Rightarrow> comma_finite_position \<Rightarrow> bool" where
  "comma_round_crossing source target =
    (case (source,target) of
      (Comma_Near f delta headroom, Comma_Entry g next_delta offset)
        \<Rightarrow> f = 9 \<and> g = 1 \<and> next_delta = Suc delta
    | _ \<Rightarrow> False)"

lemma comma_round_entry_headroom_bound:
  assumes lower: "1 \<le> f" and upper: "f \<le> 9"
    and offset: "offset \<le> 98"
  shows "comma_finite_headroom f (residue mod 924) delta offset \<le> 540"
proof -
  have exponent: "5 \<le> 924 + residue" by simp
  have bound: "comma_finite_headroom f ((924 + residue) mod 924)
      delta offset \<le> 540"
    using comma_finite_entry_headroom_admitted(2)
      [OF lower upper exponent offset, of delta] .
  show ?thesis using bound by simp
qed

lemma comma_round_crossing_offset_bound:
  assumes move: "comma_finite_step (residue mod 924) source = Comma_Next target"
    and crossing: "comma_round_crossing source target"
  shows "\<exists>delta headroom offset.
    source = Comma_Near 9 delta headroom \<and>
    target = Comma_Entry 1 (Suc delta) offset \<and> offset \<le> 90"
proof -
  obtain delta headroom offset where source:
      "source = Comma_Near 9 delta headroom"
    and target: "target = Comma_Entry 1 (Suc delta) offset"
    using crossing
    by (cases source; cases target)
      (auto simp: comma_round_crossing_def split: if_splits)
  let ?d = "(10 - headroom mod 10) mod 10"
  have headroom: "1 \<le> headroom" and upper: "headroom \<le> 540"
    and offset: "offset = 10 * ?d + 1 - headroom"
    using move
    by (auto simp: source target comma_finite_step_def
      comma_weighted_step_def Let_def split: if_splits)
  have digit: "?d \<le> 9" by simp
  have "offset \<le> 90" using headroom offset digit by arith
  then show ?thesis using source target by blast
qed

lemma comma_round_next_decreases:
  assumes move: "comma_finite_step (residue mod 924) source = Comma_Next target"
    and within: "\<not> comma_round_crossing source target"
  shows "comma_round_measure target < comma_round_measure source"
proof (cases source)
  case (Comma_Entry f delta offset)
  let ?h = "comma_finite_headroom f (residue mod 924) delta offset"
  have admitted: "1 \<le> f" "f \<le> 9" "offset \<le> 98"
    using move by (auto simp: Comma_Entry comma_finite_step_def
      comma_weighted_step_def Let_def split: if_splits)
  have period: "comma_finite_period f (offset mod 10) \<noteq> 0"
    using move admitted by (auto simp: Comma_Entry comma_finite_step_def
      comma_weighted_step_def Let_def split: if_splits)
  have target: "target = Comma_Near f delta ?h"
    using move admitted period
    by (simp add: Comma_Entry comma_finite_step_def
      comma_weighted_step_def Let_def)
  have headroom: "?h \<le> 540"
    using comma_round_entry_headroom_bound[OF admitted] .
  show ?thesis using target headroom
    by (simp add: Comma_Entry)
next
  case (Comma_Near f delta headroom)
  let ?d = "(10 - headroom mod 10) mod 10"
  have admitted: "1 \<le> f" "f \<le> 9" "1 \<le> headroom"
      "headroom \<le> 540"
    using move by (auto simp: Comma_Near comma_finite_step_def
      comma_weighted_step_def Let_def split: if_splits)
  show ?thesis
  proof (cases "f < 9")
    case True
    let ?low = "10 * ?d + f"
    have positive: "0 < ?low" using admitted by simp
    show ?thesis
    proof (cases "headroom > ?low + 1")
      case True
      have target: "target = Comma_Near f delta (headroom - ?low)"
        using move True \<open>f < 9\<close> admitted
        by (simp add: Comma_Near comma_finite_step_def
          comma_weighted_step_def Let_def)
      show ?thesis using target positive True by (simp add: Comma_Near)
    next
      case False
      have not_equal: "headroom \<noteq> ?low + 1"
        using move False \<open>f < 9\<close> admitted
        by (auto simp: Comma_Near comma_finite_step_def
          comma_weighted_step_def Let_def)
      have target: "target = Comma_Entry (f + 1) delta
          (?low + 1 - headroom)"
        using move False not_equal \<open>f < 9\<close> admitted
        by (simp add: Comma_Near comma_finite_step_def
          comma_weighted_step_def Let_def)
      show ?thesis using target admitted \<open>f < 9\<close>
        by (simp add: Comma_Near; arith)
    qed
  next
    case False
    have nine: "f = 9" using admitted False by arith
    let ?same = "10 * ?d + 9"
    let ?cross = "10 * ?d + 1"
    have target: "target = Comma_Near 9 delta (headroom - ?same)"
    proof (rule ccontr)
      assume different: "target \<noteq> Comma_Near 9 delta (headroom - ?same)"
      have crossed: "target = Comma_Entry 1 (Suc delta)
          (?cross - headroom)"
        using move different admitted nine
        by (auto simp: Comma_Near comma_finite_step_def
          comma_weighted_step_def Let_def split: if_splits)
      have "comma_round_crossing source target"
        using crossed nine
        by (simp add: Comma_Near comma_round_crossing_def)
      then show False using within by contradiction
    qed
    have positive: "0 < ?same" by simp
    have decrease: "?same \<le> headroom"
      using move target admitted nine
      by (auto simp: Comma_Near comma_finite_step_def
        comma_weighted_step_def Let_def split: if_splits)
    show ?thesis using target positive decrease nine
      by (simp add: Comma_Near)
  qed
qed

datatype comma_round_result =
    Comma_Round_Fork nat nat
  | Comma_Round_Landmine nat
  | Comma_Round_Cross comma_finite_position
  | Comma_Round_Invalid

function comma_round_close ::
  "nat \<Rightarrow> comma_finite_position \<Rightarrow>
    nat \<times> comma_finite_position \<times> comma_round_result" where
  "comma_round_close residue position =
    (case comma_finite_step (residue mod 924) position of
      Comma_Next target \<Rightarrow>
        if comma_round_crossing position target then
          (0,position,Comma_Round_Cross target)
        else (let (steps,terminal,result) = comma_round_close residue target
          in (Suc steps,terminal,result))
    | Comma_Fork a delta \<Rightarrow>
        (0,position,Comma_Round_Fork a delta)
    | Comma_Landmine delta \<Rightarrow>
        (0,position,Comma_Round_Landmine delta)
    | Comma_Invalid \<Rightarrow> (0,position,Comma_Round_Invalid))"
  by pat_completeness auto
termination
  by (relation "measure (comma_round_measure \<circ> snd)")
    (auto intro: comma_round_next_decreases)

fun comma_round_prefix_steps ::
  "nat \<Rightarrow> nat \<Rightarrow> comma_finite_position \<Rightarrow>
    comma_finite_position \<Rightarrow> bool" where
  "comma_round_prefix_steps 0 residue source terminal =
    (source = terminal)"
| "comma_round_prefix_steps (Suc steps) residue source terminal =
    (\<exists>successor. comma_finite_step (residue mod 924) source =
      Comma_Next successor \<and>
      comma_round_prefix_steps steps residue successor terminal)"

lemma comma_round_close_refines_trace:
  assumes close: "comma_round_close residue position = (steps,terminal,result)"
  shows "comma_round_prefix_steps steps residue position terminal \<and>
    (case result of
      Comma_Round_Fork a delta \<Rightarrow>
        comma_finite_step (residue mod 924) terminal = Comma_Fork a delta
    | Comma_Round_Landmine delta \<Rightarrow>
        comma_finite_step (residue mod 924) terminal = Comma_Landmine delta
    | Comma_Round_Cross target \<Rightarrow>
        comma_finite_step (residue mod 924) terminal = Comma_Next target
          \<and> comma_round_crossing terminal target
    | Comma_Round_Invalid \<Rightarrow>
        comma_finite_step (residue mod 924) terminal = Comma_Invalid)"
  using close
proof (induction residue position arbitrary: steps terminal result
    rule: comma_round_close.induct)
  case (1 residue position)
  show ?case
    using 1
    by (cases "comma_finite_step (residue mod 924) position")
      (auto simp: comma_round_close.simps split: if_splits prod.splits
        comma_round_result.splits)
qed

lemma comma_round_prefix_finite_run:
  assumes path: "comma_round_prefix_steps steps residue source terminal"
  shows "comma_finite_run (steps + fuel) (residue mod 924) source =
    comma_finite_run fuel (residue mod 924) terminal"
  using path
proof (induction steps arbitrary: source)
  case 0
  then show ?case by simp
next
  case (Suc steps)
  then obtain successor where step:
      "comma_finite_step (residue mod 924) source = Comma_Next successor"
    and suffix: "comma_round_prefix_steps steps residue successor terminal"
    by auto
  show ?case using Suc.IH[OF suffix] step by simp
qed

lemma comma_round_close_fork_finite_run:
  assumes close: "comma_round_close residue source =
    (steps,terminal,Comma_Round_Fork a delta)"
  shows "comma_finite_run (Suc steps) (residue mod 924) source =
    Some (Comma_Fork_At a delta)"
  using comma_round_close_refines_trace[OF close]
    comma_round_prefix_finite_run[of steps residue source terminal 1]
  by simp

lemma comma_round_close_landmine_finite_run:
  assumes close: "comma_round_close residue source =
    (steps,terminal,Comma_Round_Landmine delta)"
  shows "comma_finite_run (Suc steps) (residue mod 924) source =
    Some (Comma_Landmine_At delta)"
  using comma_round_close_refines_trace[OF close]
    comma_round_prefix_finite_run[of steps residue source terminal 1]
  by simp

lemma comma_round_prefix_append_one:
  assumes path: "comma_round_prefix_steps steps residue source terminal"
    and step: "comma_finite_step (residue mod 924) terminal =
      Comma_Next target"
  shows "comma_round_prefix_steps (Suc steps) residue source target"
  using path
proof (induction steps arbitrary: source)
  case 0
  then show ?case using step by simp
next
  case (Suc steps)
  then obtain successor where first:
      "comma_finite_step (residue mod 924) source = Comma_Next successor"
    and rest: "comma_round_prefix_steps steps residue successor terminal"
    by auto
  show ?case using Suc.IH[OF rest] first by simp
qed

lemma comma_round_close_cross_prefix:
  assumes close: "comma_round_close residue source =
    (steps,terminal,Comma_Round_Cross target)"
  shows "comma_round_prefix_steps (Suc steps) residue source target"
  using comma_round_close_refines_trace[OF close]
    comma_round_prefix_append_one by auto

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_round_entry_headroom_bound
      comma_round_crossing_offset_bound comma_round_next_decreases
      comma_round_close_refines_trace
      comma_round_prefix_finite_run comma_round_close_fork_finite_run
      comma_round_close_landmine_finite_run
      comma_round_prefix_append_one
      comma_round_close_cross_prefix})
    then () else error "Comma round closure depends on an oracle";
\<close>

end
