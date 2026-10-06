theory Comma_Round_Weights
  imports Comma_Decade_Totality.Comma_Decade_Control
begin

text \<open>Literal weight is an observation of canonical weighted Next edges.
The control round never evaluates these weights. At a concrete admitted
exponent the chart refinement supplies their literal interpretation.\<close>

fun comma_weighted_prefix_using ::
  "(nat \<Rightarrow> comma_finite_position \<Rightarrow> comma_weighted_move) \<Rightarrow>
    nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> comma_finite_position \<Rightarrow>
    comma_finite_position \<Rightarrow> nat \<Rightarrow> bool" where
  "comma_weighted_prefix_using step p r 0 source terminal weight =
    (source = terminal \<and> weight = 0)"
| "comma_weighted_prefix_using step p r (Suc n) source terminal weight =
    (\<exists>successor local_weight rest.
      step (r mod 924) source = Comma_WNext successor local_weight \<and>
      comma_weighted_prefix_using step p r n successor terminal rest \<and>
      weight = comma_chart_weight_value p local_weight + rest)"

definition comma_round_weighted_prefix ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> comma_finite_position \<Rightarrow>
    comma_finite_position \<Rightarrow> nat \<Rightarrow> bool" where
  "comma_round_weighted_prefix p r n source terminal weight =
    comma_weighted_prefix_using comma_weighted_step p r n source terminal weight"

lemma comma_round_weighted_prefix_zero [simp]:
  "comma_round_weighted_prefix p r 0 source terminal weight =
    (source = terminal \<and> weight = 0)"
  by (simp add: comma_round_weighted_prefix_def)

lemma comma_round_weighted_prefix_suc [simp]:
  "comma_round_weighted_prefix p r (Suc n) source terminal weight =
    (\<exists>successor local_weight rest.
      comma_weighted_step (r mod 924) source = Comma_WNext successor local_weight \<and>
      comma_round_weighted_prefix p r n successor terminal rest \<and>
      weight = comma_chart_weight_value p local_weight + rest)"
  by (simp add: comma_round_weighted_prefix_def)

lemmas comma_round_weighted_prefix_simps =
  comma_round_weighted_prefix_zero comma_round_weighted_prefix_suc

lemma comma_round_weighted_prefix_erasure:
  "comma_round_prefix_steps n r source terminal =
    (\<exists>weight. comma_round_weighted_prefix p r n source terminal weight)"
proof (induction n arbitrary: source)
  case 0
  then show ?case by simp
next
  case (Suc n)
  show ?case
    using Suc.IH
    by (cases "comma_weighted_step (r mod 924) source")
      (auto simp: comma_finite_step_def simp del: comma_weighted_step_def)
qed

lemma comma_round_close_has_weighted_prefix:
  assumes "comma_round_close r source = (n,terminal,result)"
  shows "\<exists>weight. comma_round_weighted_prefix p r n source terminal weight"
  using comma_round_close_refines_trace[OF assms]
    comma_round_weighted_prefix_erasure[of n r source terminal p]
  by simp

lemma comma_round_weighted_prefix_append:
  assumes path: "comma_round_weighted_prefix p r n source terminal weight"
    and step: "comma_weighted_step (r mod 924) terminal = Comma_WNext target local_weight"
  shows "comma_round_weighted_prefix p r (Suc n) source target
    (weight + comma_chart_weight_value p local_weight)"
  using path
proof (induction n arbitrary: source weight)
  case 0
  then show ?case using step by auto
next
  case (Suc n)
  then obtain successor w rest where move:
    "comma_weighted_step (r mod 924) source = Comma_WNext successor w"
    and tail: "comma_round_weighted_prefix p r n successor terminal rest"
    and weight: "weight = comma_chart_weight_value p w + rest" by auto
  show ?case
    using Suc.IH[OF tail] move weight
    by (auto simp: add.assoc simp del: comma_weighted_step_def)
qed

lemma comma_round_weighted_prefix_concat:
  assumes first: "comma_round_weighted_prefix p r n source middle left_weight"
    and second: "comma_round_weighted_prefix p r m middle target right_weight"
  shows "comma_round_weighted_prefix p r (n+m) source target
    (left_weight+right_weight)"
  using first
proof (induction n arbitrary: source left_weight)
  case 0
  then show ?case using second by simp
next
  case (Suc n)
  then obtain successor w rest where move:
    "comma_weighted_step (r mod 924) source = Comma_WNext successor w"
    and tail: "comma_round_weighted_prefix p r n successor middle rest"
    and weight: "left_weight = comma_chart_weight_value p w + rest" by auto
  show ?case
    using Suc.IH[OF tail] move weight
    by (auto simp: add.assoc simp del: comma_weighted_step_def)
qed

lemma comma_round_crossing_weight_unit:
  assumes move: "comma_finite_step (r mod 924) terminal = Comma_Next target"
    and cross: "comma_round_crossing terminal target"
  shows "comma_weighted_step (r mod 924) terminal =
    Comma_WNext target (Comma_Chart_Weight 0 0 1 1)"
  using move cross
  by (cases terminal; cases target)
    (auto simp: comma_round_crossing_def comma_finite_step_def
      comma_weighted_step_def Let_def split: if_splits)

lemma comma_round_crossing_adds_one_literal:
  assumes close: "comma_round_close r source = (n,terminal,Comma_Round_Cross target)"
  shows "\<exists>weight. comma_round_weighted_prefix p r n source terminal weight \<and>
    comma_round_weighted_prefix p r (Suc n) source target (weight + 1)"
proof -
  obtain weight where path:
    "comma_round_weighted_prefix p r n source terminal weight"
    using comma_round_close_has_weighted_prefix[OF close] by blast
  have move: "comma_finite_step (r mod 924) terminal = Comma_Next target"
    and cross: "comma_round_crossing terminal target"
    using comma_round_close_refines_trace[OF close] by simp_all
  have step: "comma_weighted_step (r mod 924) terminal =
    Comma_WNext target (Comma_Chart_Weight 0 0 1 1)"
    by (rule comma_round_crossing_weight_unit[OF move cross])
  have extended: "comma_round_weighted_prefix p r (Suc n) source target (weight + 1)"
    using comma_round_weighted_prefix_append[OF path step]
    by (simp only: comma_chart_weight_unit)
  show ?thesis by (rule exI[of _ weight], rule conjI[OF path extended])
qed

lemma comma_round_fork_inspection_zero_literal:
  assumes close: "comma_round_close (p mod 924) source =
    (n,terminal,Comma_Round_Fork a d)"
  shows "comma_finite_weighted_run 1 p terminal =
    Some (Comma_Fork_At a d,0,terminal)"
proof -
  have event: "comma_finite_step (p mod 924) terminal = Comma_Fork a d"
    using comma_round_close_refines_trace[OF close] by simp
  obtain t where step: "comma_weighted_step (p mod 924) terminal = Comma_WFork t a d"
    using event by (cases "comma_weighted_step (p mod 924) terminal")
      (auto simp: comma_finite_step_def simp del: comma_weighted_step_def)
  have "t = terminal" using comma_weighted_terminal_is_source step by blast
  then show ?thesis using step by (simp del: comma_weighted_step_def)
qed

lemma comma_round_landmine_inspection_zero_literal:
  assumes close: "comma_round_close (p mod 924) source =
    (n,terminal,Comma_Round_Landmine d)"
  shows "comma_finite_weighted_run 1 p terminal =
    Some (Comma_Landmine_At d,0,terminal)"
proof -
  have event: "comma_finite_step (p mod 924) terminal = Comma_Landmine d"
    using comma_round_close_refines_trace[OF close] by simp
  obtain t where step: "comma_weighted_step (p mod 924) terminal = Comma_WLandmine t d"
    using event by (cases "comma_weighted_step (p mod 924) terminal")
      (auto simp: comma_finite_step_def simp del: comma_weighted_step_def)
  have "t = terminal" using comma_weighted_terminal_is_source step by blast
  then show ?thesis using step by (simp del: comma_weighted_step_def)
qed


text \<open>The abstract weight observation above allows arbitrary p and r.
Literal interpretation requires their phases to agree, an admitted chart,
and the exponent bound used by the Entry and Near refinement theorems.\<close>

lemma comma_round_weighted_step_literal:
  assumes exponent: "5 \<le> p"
    and valid: "comma_round_admitted source"
    and move: "comma_weighted_step (p mod 924) source = Comma_WNext target weight"
  shows "comma_literal_path (comma_chart_weight_value p weight)
    (comma_chart_value p source) (comma_chart_value p target)"
proof -
  have finite: "comma_finite_step (p mod 924) source = Comma_Next target"
    by (simp only: comma_finite_step_def move comma_erase_weight.simps)
  have emitted: "comma_finite_next_weight p source = comma_chart_weight_value p weight"
    by (simp only: comma_finite_next_weight_def move comma_weighted_move.case)
  show ?thesis
  proof (cases source)
    case (Comma_Entry f delta offset)
    have f: "1 \<le> f" "f \<le> 9" and offset: "offset \<le> 98"
      using valid by (simp_all add: Comma_Entry)
    note entry = comma_entry_chart_exact_literal_path(1,2,4)
      [OF f exponent offset, of delta]
    have target: "target = Comma_Near f delta
        (comma_finite_headroom f (p mod 924) delta offset)"
      using finite entry(1) by (metis Comma_Entry comma_finite_move.inject)
    show ?thesis using entry(2,3) emitted target by (metis Comma_Entry)
  next
    case (Comma_Near f delta headroom)
    have f: "1 \<le> f" "f \<le> 9"
      and headroom: "1 \<le> headroom" "headroom \<le> 540"
      using valid by (simp_all add: Comma_Near)
    have next_move: "comma_finite_step (p mod 924) (Comma_Near f delta headroom) =
      Comma_Next target" using finite by (simp only: Comma_Near)
    note near = comma_near_chart_next_literal(1,2)[OF f exponent headroom next_move]
    show ?thesis using near emitted by (metis Comma_Near)
  qed
qed

theorem comma_round_weighted_prefix_literal:
  assumes path: "comma_round_weighted_prefix p r n source terminal weight"
    and phase: "r mod 924 = p mod 924"
    and exponent: "5 \<le> p"
    and valid: "comma_round_admitted source"
  shows "comma_literal_path weight
    (comma_chart_value p source) (comma_chart_value p terminal)"
  using path valid
proof (induction n arbitrary: source weight)
  case 0
  then show ?case by (auto intro: comma_literal_path.zero)
next
  case (Suc n)
  obtain successor local_weight rest where move:
    "comma_weighted_step (r mod 924) source = Comma_WNext successor local_weight"
    and tail: "comma_round_weighted_prefix p r n successor terminal rest"
    and weight: "weight = comma_chart_weight_value p local_weight + rest"
    using Suc.prems(1) by (simp only: comma_round_weighted_prefix_simps; blast)
  have finite: "comma_finite_step (r mod 924) source = Comma_Next successor"
    by (simp only: comma_finite_step_def move comma_erase_weight.simps)
  have next_valid: "comma_round_admitted successor"
    by (rule comma_round_next_admitted[OF Suc.prems(2) finite])
  have first: "comma_literal_path (comma_chart_weight_value p local_weight)
    (comma_chart_value p source) (comma_chart_value p successor)"
    by (rule comma_round_weighted_step_literal[OF exponent Suc.prems(2)])
      (use move in \<open>simp only: phase\<close>)
  have rest: "comma_literal_path rest
    (comma_chart_value p successor) (comma_chart_value p terminal)"
    by (rule Suc.IH[OF tail next_valid])
  show ?case using comma_literal_path_append[OF first rest]
    by (simp only: weight)
qed

corollary comma_round_close_literal_prefix:
  assumes close: "comma_round_close r source = (n,terminal,result)"
    and phase: "r mod 924 = p mod 924"
    and exponent: "5 \<le> p"
    and valid: "comma_round_admitted source"
  shows "\<exists>weight. comma_round_weighted_prefix p r n source terminal weight \<and>
    comma_literal_path weight (comma_chart_value p source) (comma_chart_value p terminal)"
  using comma_round_close_has_weighted_prefix[OF close, of p]
    comma_round_weighted_prefix_literal[OF _ phase exponent valid]
  by blast

corollary comma_round_crossing_literal_prefix:
  assumes close: "comma_round_close r source = (n,terminal,Comma_Round_Cross target)"
    and phase: "r mod 924 = p mod 924"
    and exponent: "5 \<le> p"
    and valid: "comma_round_admitted source"
  shows "\<exists>weight. comma_literal_path weight
      (comma_chart_value p source) (comma_chart_value p terminal) \<and>
    comma_literal_path (weight + 1)
      (comma_chart_value p source) (comma_chart_value p target)"
  using comma_round_crossing_adds_one_literal[OF close, of p]
    comma_round_weighted_prefix_literal[OF _ phase exponent valid]
  by blast

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_round_weighted_prefix_concat comma_round_weighted_prefix_erasure comma_round_close_has_weighted_prefix
      comma_round_crossing_adds_one_literal comma_round_fork_inspection_zero_literal
      comma_round_landmine_inspection_zero_literal
      comma_round_weighted_step_literal comma_round_weighted_prefix_literal
      comma_round_close_literal_prefix comma_round_crossing_literal_prefix})
    then () else error "Comma round weights depend on an oracle";
\<close>
end
