theory Source_Chart_Selector_Fusion
  imports "Temporal_Clock_Jumps.Decimal_Publisher_Constructor"
    Reverse_Residuals.Reverse_Contextual_Fixed_Point
begin

text \<open>This is an optional downstream consumer/fusion theory.  It is
not a prerequisite for a closed full skew-cylinder return representation and
does not require that representation to use a selector graph or a minimizer.
For implementations using such charts it is deliberately cross-chart: source
states and quotient-chart states have different types, and source emissions
may be translated to chart emissions.  This differs from
stable-contextual-all-continuations, which proves equality of two
traces inside one state universe from a stable contextual signature.

Nothing below constructs a 196 normalizer.  The transition maps, chart map,
admitted set, selectors, and emission translation are supplied parameters.
Consequently the existence result obtained from
factor-through-iff is a mathematical factorization and is not
an executable choice of quotient table or a work bound.\<close>

fun selector_run ::
    "('s \<Rightarrow> 'j \<Rightarrow> 's) \<Rightarrow> 'j list \<Rightarrow> 's \<Rightarrow> 's" where
  "selector_run delta [] s = s"
| "selector_run delta (j # js) s = selector_run delta js (delta s j)"

fun selector_emissions ::
    "('s \<Rightarrow> 'j \<Rightarrow> 's) \<Rightarrow> ('s \<Rightarrow> 'j \<Rightarrow> 'o) \<Rightarrow>
      'j list \<Rightarrow> 's \<Rightarrow> 'o list" where
  "selector_emissions delta source_observe [] s = []"
| "selector_emissions delta source_observe (j # js) s =
    source_observe s j #
      selector_emissions delta source_observe js (delta s j)"

definition selector_trace ::
    "('s \<Rightarrow> 'j \<Rightarrow> 's) \<Rightarrow> ('s \<Rightarrow> 'j \<Rightarrow> 'o) \<Rightarrow>
      'j list \<Rightarrow> 's \<Rightarrow> 'o list \<times> 's" where
  "selector_trace delta source_observe js s =
    (selector_emissions delta source_observe js s, selector_run delta js s)"

definition map_selector_trace ::
    "('o \<Rightarrow> 'p) \<Rightarrow> ('s \<Rightarrow> 'c) \<Rightarrow>
      ('o list \<times> 's) \<Rightarrow> ('p list \<times> 'c)" where
  "map_selector_trace f q tr = (map f (fst tr), q (snd tr))"

lemma selector_run_closed:
  assumes closed: "\<And>s j. s \<in> A \<Longrightarrow> delta s j \<in> A"
      and admitted: "s \<in> A"
  shows "selector_run delta js s \<in> A"
  using admitted
  by (induction js arbitrary: s) (auto intro: closed)

lemma selector_run_cross_chart:
  assumes closed: "\<And>s j. s \<in> A \<Longrightarrow> delta s j \<in> A"
      and commute: "\<And>s j. s \<in> A \<Longrightarrow>
        q (delta s j) = delta_q (q s) j"
      and admitted: "s \<in> A"
  shows "q (selector_run delta js s) =
    selector_run delta_q js (q s)"
  using admitted
proof (induction js arbitrary: s)
  case Nil
  then show ?case by simp
next
  case (Cons j js)
  have next_admitted: "delta s j \<in> A"
    by (rule closed[OF Cons.prems])
  have tail: "q (selector_run delta js (delta s j)) =
      selector_run delta_q js (q (delta s j))"
    by (rule Cons.IH[OF next_admitted])
  show ?case using tail commute[OF Cons.prems, of j] by simp
qed

lemma selector_emissions_cross_chart:
  assumes closed: "\<And>s j. s \<in> A \<Longrightarrow> delta s j \<in> A"
      and commute: "\<And>s j. s \<in> A \<Longrightarrow>
        q (delta s j) = delta_q (q s) j"
      and observe: "\<And>s j. s \<in> A \<Longrightarrow>
        chart_observe (q s) j = f (source_observe s j)"
      and admitted: "s \<in> A"
  shows "selector_emissions delta_q chart_observe js (q s) =
    map f (selector_emissions delta source_observe js s)"
  using admitted
proof (induction js arbitrary: s)
  case Nil
  then show ?case by simp
next
  case (Cons j js)
  have next_admitted: "delta s j \<in> A"
    by (rule closed[OF Cons.prems])
  have tail: "selector_emissions delta_q chart_observe js (q (delta s j)) =
      map f (selector_emissions delta source_observe js (delta s j))"
    by (rule Cons.IH[OF next_admitted])
  show ?case using commute[OF Cons.prems, of j]
      observe[OF Cons.prems, of j] tail by simp
qed

theorem selector_word_interpreter_fusion:
  assumes closed: "\<And>s j. s \<in> A \<Longrightarrow> delta s j \<in> A"
      and commute: "\<And>s j. s \<in> A \<Longrightarrow>
        q (delta s j) = delta_q (q s) j"
      and observe: "\<And>s j. s \<in> A \<Longrightarrow>
        chart_observe (q s) j = f (source_observe s j)"
      and admitted: "s \<in> A"
  shows "selector_trace delta_q chart_observe js (q s) =
    map_selector_trace f q (selector_trace delta source_observe js s)"
  using selector_run_cross_chart[
      where A=A and delta=delta and q=q and delta_q=delta_q
        and s=s and js=js, OF closed commute admitted]
    selector_emissions_cross_chart[
      where A=A and delta=delta and q=q and delta_q=delta_q
        and source_observe=source_observe and chart_observe=chart_observe
        and f=f and s=s and js=js, OF closed commute observe admitted]
  by (simp add: selector_trace_def map_selector_trace_def)

section \<open>Rows of the supplied source-side selector graph\<close>

definition source_selector_row where
  "source_selector_row delta source_observe q s j =
    (source_observe s j, q (delta s j))"

definition chart_selector_row where
  "chart_selector_row delta_q chart_observe c j =
    (chart_observe c j, delta_q c j)"

lemma selector_graph_row_natural:
  assumes commute: "q (delta s j) = delta_q (q s) j"
      and observe: "chart_observe (q s) j = f (source_observe s j)"
  shows "chart_selector_row delta_q chart_observe (q s) j =
    map_prod f id (source_selector_row delta source_observe q s j)"
  using assms
  by (simp add: source_selector_row_def chart_selector_row_def)

definition selector_word_row where
  "selector_word_row delta source_observe q js s =
    (selector_emissions delta source_observe js s,
      q (selector_run delta js s))"

corollary selector_word_row_natural:
  assumes closed: "\<And>s j. s \<in> A \<Longrightarrow> delta s j \<in> A"
      and commute: "\<And>s j. s \<in> A \<Longrightarrow>
        q (delta s j) = delta_q (q s) j"
      and observe: "\<And>s j. s \<in> A \<Longrightarrow>
        chart_observe (q s) j = f (source_observe s j)"
      and admitted: "s \<in> A"
  shows "selector_word_row delta_q chart_observe id js (q s) =
    map_prod (map f) id
      (selector_word_row delta source_observe q js s)"
  using selector_word_interpreter_fusion[
      where A=A and delta=delta and q=q and delta_q=delta_q
        and source_observe=source_observe and chart_observe=chart_observe
        and f=f and s=s and js=js, OF closed commute observe admitted]
  by (simp add: selector_word_row_def selector_trace_def
      map_selector_trace_def)

section \<open>Exact factor-through boundary for temporal transport\<close>

theorem temporal_chart_factor_through_iff:
  "(\<exists>advance. \<forall>s\<in>A.
      advance (q_before s) = q_after (T s)) \<longleftrightarrow>
   (\<forall>s\<in>A. \<forall>t\<in>A. q_before s = q_before t \<longrightarrow>
      q_after (T s) = q_after (T t))"
  by (rule factor_through_iff[
        where A=A and q=q_before and r="\<lambda>s. q_after (T s)"])

corollary equal_chart_has_equal_next_chart_iff:
  "(\<forall>s\<in>A. \<forall>t\<in>A. q_before s = q_before t \<longrightarrow>
      q_after (T s) = q_after (T t)) \<longleftrightarrow>
   (\<exists>advance. \<forall>s\<in>A. advance (q_before s) = q_after (T s))"
proof
  assume congruence:
    "\<forall>s\<in>A. \<forall>t\<in>A. q_before s = q_before t \<longrightarrow>
      q_after (T s) = q_after (T t)"
  show "\<exists>advance. \<forall>s\<in>A.
      advance (q_before s) = q_after (T s)"
    by (rule temporal_chart_factor_through_iff[
          where A=A and q_before=q_before and q_after=q_after and T=T,
          THEN iffD2, OF congruence])
next
  assume factor:
    "\<exists>advance. \<forall>s\<in>A.
      advance (q_before s) = q_after (T s)"
  show "\<forall>s\<in>A. \<forall>t\<in>A. q_before s = q_before t \<longrightarrow>
      q_after (T s) = q_after (T t)"
    by (rule temporal_chart_factor_through_iff[
          where A=A and q_before=q_before and q_after=q_after and T=T,
          THEN iffD1, OF factor])
qed

lemma transition_run_closed:
  assumes closed: "\<And>s. s \<in> A \<Longrightarrow> T s \<in> A"
      and admitted: "s \<in> A"
  shows "run T n s \<in> A"
  using admitted
  by (induction n arbitrary: s) (auto intro: closed)

theorem supplied_cross_chart_future_word_preservation:
  assumes temporal_closed: "\<And>s. s \<in> A \<Longrightarrow> T s \<in> A"
      and temporal_commute: "\<And>s. s \<in> A \<Longrightarrow>
        q (T s) = U (q s)"
      and selector_closed: "\<And>s j. s \<in> A \<Longrightarrow> delta s j \<in> A"
      and selector_commute: "\<And>s j. s \<in> A \<Longrightarrow>
        q (delta s j) = delta_q (q s) j"
      and observe: "\<And>s j. s \<in> A \<Longrightarrow>
        chart_observe (q s) j = f (source_observe s j)"
      and admitted: "s \<in> A"
  shows "selector_trace delta_q chart_observe js (run U n (q s)) =
    map_selector_trace f q
      (selector_trace delta source_observe js (run T n s))"
proof -
  have source_admitted: "run T n s \<in> A"
    by (rule transition_run_closed[
          where A=A and T=T and s=s and n=n,
          OF temporal_closed admitted])
  have temporal_fusion: "q (run T n s) = run U n (q s)"
    by (rule iterate_commutes[
          where A=A and T=T and q=q and u=U and s=s and n=n,
          OF temporal_closed temporal_commute admitted])
  have selector_fusion:
      "selector_trace delta_q chart_observe js (q (run T n s)) =
       map_selector_trace f q
        (selector_trace delta source_observe js (run T n s))"
    by (rule selector_word_interpreter_fusion[
          where A=A and delta=delta and q=q and delta_q=delta_q
            and source_observe=source_observe
            and chart_observe=chart_observe and f=f
            and s="run T n s" and js=js,
          OF selector_closed selector_commute observe source_admitted])
  show ?thesis using selector_fusion temporal_fusion by simp
qed

section \<open>A finite non-faithful countermodel\<close>

datatype selector_counter_state = CounterLeft | CounterRight | CounterMarked

fun counter_chart where
  "counter_chart CounterLeft = False"
| "counter_chart CounterRight = False"
| "counter_chart CounterMarked = True"

definition counter_selector_step where
  "counter_selector_step s j = (s::selector_counter_state)"

definition counter_selector_emit where
  "counter_selector_emit s j = False"

fun counter_temporal_step where
  "counter_temporal_step CounterLeft = CounterLeft"
| "counter_temporal_step CounterRight = CounterMarked"
| "counter_temporal_step CounterMarked = CounterMarked"

lemma counter_selectors_are_stable:
  "map_selector_trace id counter_chart
      (selector_trace counter_selector_step counter_selector_emit js CounterLeft) =
   map_selector_trace id counter_chart
      (selector_trace counter_selector_step counter_selector_emit js CounterRight)"
  by (induction js)
    (simp_all add: selector_trace_def map_selector_trace_def
      counter_selector_step_def counter_selector_emit_def)

lemma counter_temporal_successor_is_not_stable:
  "counter_chart CounterLeft = counter_chart CounterRight \<and>
   counter_chart (counter_temporal_step CounterLeft) \<noteq>
    counter_chart (counter_temporal_step CounterRight)"
  by simp

text \<open>The finite countermodel says only that a selector-stable chart
which omits a source distinction need not be stable under an unrelated
temporal transition.  Its row is intentionally not faithful to the complete
admitted source result.  It is not a counterexample to reverse/add, to the 196
source chart, or to a complete exact emitted occurrence.\<close>

section \<open>Conditional sufficiency of a complete row semantics\<close>

theorem complete_row_semantics_factors_result:
  assumes chart_determines_row:
      "\<And>s t. s \<in> A \<Longrightarrow> t \<in> A \<Longrightarrow>
        q s = q t \<Longrightarrow> row s = row t"
      and row_determines_result:
      "\<And>s t. s \<in> A \<Longrightarrow> t \<in> A \<Longrightarrow>
        row s = row t \<Longrightarrow> result s = result t"
  shows "\<exists>publish. \<forall>s\<in>A. publish (q s) = result s"
proof -
  have congruence:
      "\<forall>s\<in>A. \<forall>t\<in>A. q s = q t \<longrightarrow> result s = result t"
  proof (intro ballI impI)
    fix s t
    assume s_admitted: "s \<in> A" and t_admitted: "t \<in> A"
      and same_chart: "q s = q t"
    have "row s = row t"
      by (rule chart_determines_row[OF s_admitted t_admitted same_chart])
    then show "result s = result t"
      by (rule row_determines_result[OF s_admitted t_admitted])
  qed
  show ?thesis
    by (rule factor_through_iff[
          where A=A and q=q and r=result, THEN iffD2, OF congruence])
qed

corollary complete_row_semantics_equal_result:
  assumes chart_determines_row:
      "\<And>s t. s \<in> A \<Longrightarrow> t \<in> A \<Longrightarrow>
        q s = q t \<Longrightarrow> row s = row t"
      and row_determines_result:
      "\<And>s t. s \<in> A \<Longrightarrow> t \<in> A \<Longrightarrow>
        row s = row t \<Longrightarrow> result s = result t"
      and admitted: "s \<in> A" "t \<in> A"
      and equal_chart: "q s = q t"
  shows "result s = result t"
proof -
  have same_row: "row s = row t"
    by (rule chart_determines_row[OF admitted equal_chart])
  show ?thesis
    by (rule row_determines_result[OF admitted same_row])
qed

corollary complete_row_semantics_equal_consumer:
  assumes chart_determines_row:
      "\<And>s t. s \<in> A \<Longrightarrow> t \<in> A \<Longrightarrow>
        q s = q t \<Longrightarrow> row s = row t"
      and row_determines_result:
      "\<And>s t. s \<in> A \<Longrightarrow> t \<in> A \<Longrightarrow>
        row s = row t \<Longrightarrow> result s = result t"
      and admitted: "s \<in> A" "t \<in> A"
      and equal_chart: "q s = q t"
  shows "consumer (result s) = consumer (result t)"
proof -
  have same_row: "row s = row t"
    by (rule chart_determines_row[OF admitted equal_chart])
  have same_result: "result s = result t"
    by (rule row_determines_result[OF admitted same_row])
  show ?thesis by (rule arg_cong[OF same_result])
qed

text \<open>Production still has to instantiate the supplied maps with the
authenticated 196 source chart, prove closure and the local selector and
emission equations for every admitted selector, show that the retained row is
complete for the exact recursive result, and implement canonical reachable-row
construction before publication.  These theorems provide no algorithm for
Myhill--Nerode minimization, no bound on reachable-row discovery, and no claim
that the current CLI avoids causal reconstruction.\<close>

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms selector_run_closed selector_run_cross_chart
      selector_emissions_cross_chart selector_word_interpreter_fusion
      selector_graph_row_natural selector_word_row_natural
      temporal_chart_factor_through_iff equal_chart_has_equal_next_chart_iff
      transition_run_closed supplied_cross_chart_future_word_preservation
      counter_selectors_are_stable counter_temporal_successor_is_not_stable
      complete_row_semantics_factors_result
      complete_row_semantics_equal_result
      complete_row_semantics_equal_consumer})
    then () else error "Source-chart selector fusion proof depends on an oracle";
\<close>

end
