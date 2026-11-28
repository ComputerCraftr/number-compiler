theory Comma_Symbolic_First_Sector_Writer
  imports Comma_Symbolic_Writer Comma_Symbolic_Near_Cut
begin

text \<open>The source-bound Entry and strict Near prefix form one physical writer
action. Its point operation selects a chronological cut directly from the
period quotient or the bounded Near displacement. The state records whether
this one action has completed; it carries no occurrence history.\<close>

definition comma_first_sector_writer_point ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_first_sector_writer_point f p delta offset j =
    (let h = comma_finite_headroom f (p mod 924) delta offset;
         steps = ((10 ^ (p + delta) - offset - h) div
           comma_finite_period f (offset mod 10)) * comma_cycle_length f
     in if j \<le> steps then comma_symbolic_entry_cut f p delta offset j
        else comma_chart_value p (Comma_Near f delta
          (comma_symbolic_near_cut f h (j - steps))))"

definition comma_first_sector_writer_value ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> nat" where
  "comma_first_sector_writer_value f p delta offset t completed =
    (if completed then comma_chart_value p (Comma_Near f delta t)
     else comma_chart_value p (Comma_Entry f delta offset))"

definition comma_first_sector_writer ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat
    \<Rightarrow> bool comma_symbolic_writer_action" where
  "comma_first_sector_writer f p delta offset elapsed t =
    \<lparr>comma_writer_advance = (\<lambda>_. True),
     comma_writer_duration = (\<lambda>completed. if completed then 0 else elapsed),
     comma_writer_point = (\<lambda>completed j.
       if completed then comma_chart_value p (Comma_Near f delta t)
       else comma_first_sector_writer_point f p delta offset j)\<rparr>"

theorem comma_first_sector_writer_cut_exact:
  fixes f p delta offset elapsed t j h steps n :: nat
    and event :: comma_finite_move
  assumes sector: "1 \<le> f" "f \<le> 9"
    and exponent: "5 \<le> p" and offset: "offset \<le> 98"
    and packet: "comma_c1_first_sector f p delta offset = (elapsed,t,event)"
    and bound: "j \<le> elapsed"
  defines "h \<equiv> comma_finite_headroom f (p mod 924) delta offset"
    and "steps \<equiv> ((10 ^ (p + delta) - offset - h) div
      comma_finite_period f (offset mod 10)) * comma_cycle_length f"
    and "n \<equiv> fst (comma_near_closed_germ f h)"
  shows "comma_literal_path j (comma_chart_value p (Comma_Entry f delta offset))
      (comma_first_sector_writer_point f p delta offset j)"
    and "comma_literal_path (elapsed-j)
      (comma_first_sector_writer_point f p delta offset j)
      (comma_chart_value p (Comma_Near f delta t))"
proof -
  have h: "1 \<le> h" "h \<le> 540"
    using comma_finite_entry_headroom_admitted[OF sector exponent offset, of delta]
    by (simp_all add: h_def)
  have elapsed: "elapsed = steps + n"
    and prefix: "comma_near_prefix n f h t"
    using comma_c1_first_sector_source[OF sector exponent offset packet]
    by (simp_all add: h_def steps_def n_def)
  have both: "comma_literal_path j (comma_chart_value p (Comma_Entry f delta offset))
      (comma_first_sector_writer_point f p delta offset j) \<and>
    comma_literal_path (elapsed-j)
      (comma_first_sector_writer_point f p delta offset j)
      (comma_chart_value p (Comma_Near f delta t))"
  proof (cases "j \<le> steps")
    case True
    have cuts:
      "comma_literal_path j (comma_chart_value p (Comma_Entry f delta offset))
        (comma_symbolic_entry_cut f p delta offset j)"
      "comma_literal_path (steps-j) (comma_symbolic_entry_cut f p delta offset j)
        (comma_chart_value p (Comma_Near f delta h))"
      using comma_symbolic_entry_cut_exact[OF sector exponent offset, where delta=delta and j=j]
        True by (simp_all add: h_def steps_def)
    have near: "comma_literal_path n (comma_chart_value p (Comma_Near f delta h))
        (comma_chart_value p (Comma_Near f delta t))"
      by (rule comma_c1_near_chart_prefix_refinement(3)[OF sector exponent h prefix])
    have tail: "comma_literal_path ((steps-j)+n)
        (comma_symbolic_entry_cut f p delta offset j)
        (comma_chart_value p (Comma_Near f delta t))"
      by (rule comma_literal_path_append[OF cuts(2) near])
    have time: "(steps-j)+n = elapsed-j" using True elapsed by arith
    have point: "comma_first_sector_writer_point f p delta offset j =
        comma_symbolic_entry_cut f p delta offset j"
      using True by (simp add: comma_first_sector_writer_point_def Let_def h_def steps_def)
    have left: "comma_literal_path j (comma_chart_value p (Comma_Entry f delta offset))
        (comma_first_sector_writer_point f p delta offset j)"
      using cuts(1) by (simp only: point)
    have right: "comma_literal_path (elapsed-j)
        (comma_first_sector_writer_point f p delta offset j)
        (comma_chart_value p (Comma_Near f delta t))"
      using tail by (simp only: point time)
    show ?thesis using left right by simp
  next
    case False
    have near_bound: "j-steps \<le> n" using bound elapsed by arith
    have near_bound_source:
      "j-steps \<le> fst (comma_near_closed_germ f
        (comma_finite_headroom f (p mod 924) delta offset))"
      using near_bound by (simp only: n_def h_def)
    have cuts:
      "comma_literal_path (steps+(j-steps)) (comma_chart_value p (Comma_Entry f delta offset))
        (comma_chart_value p (Comma_Near f delta (comma_symbolic_near_cut f h (j-steps))))"
      "comma_literal_path (elapsed-(steps+(j-steps)))
        (comma_chart_value p (Comma_Near f delta (comma_symbolic_near_cut f h (j-steps))))
        (comma_chart_value p (Comma_Near f delta t))"
      using comma_symbolic_first_sector_near_cut[
        where j="j-steps", OF sector exponent offset packet near_bound_source]
      by (simp_all add: h_def steps_def)
    have index: "steps+(j-steps) = j" using False by arith
    have point: "comma_first_sector_writer_point f p delta offset j =
        comma_chart_value p (Comma_Near f delta (comma_symbolic_near_cut f h (j-steps)))"
      using False by (simp add: comma_first_sector_writer_point_def Let_def h_def steps_def)
    have left: "comma_literal_path j (comma_chart_value p (Comma_Entry f delta offset))
        (comma_first_sector_writer_point f p delta offset j)"
      using cuts(1) by (simp only: point index)
    have right: "comma_literal_path (elapsed-j)
        (comma_first_sector_writer_point f p delta offset j)
        (comma_chart_value p (Comma_Near f delta t))"
      using cuts(2) by (simp only: point index)
    show ?thesis using left right by simp
  qed
  show "comma_literal_path j (comma_chart_value p (Comma_Entry f delta offset))
      (comma_first_sector_writer_point f p delta offset j)"
    and "comma_literal_path (elapsed-j)
      (comma_first_sector_writer_point f p delta offset j)
      (comma_chart_value p (Comma_Near f delta t))"
    using both by blast+
qed

theorem comma_first_sector_writer_source:
  assumes sector: "1 \<le> f" "f \<le> 9"
    and exponent: "5 \<le> p" and offset: "offset \<le> 98"
    and packet: "comma_c1_first_sector f p delta offset = (elapsed,t,event)"
  shows "comma_symbolic_writer_action_sound
      (comma_first_sector_writer_value f p delta offset t) (\<lambda>_. True)
      (comma_first_sector_writer f p delta offset elapsed t)"
proof -
  have cuts:
    "\<And>j. j \<le> elapsed \<Longrightarrow>
      comma_literal_path j (comma_chart_value p (Comma_Entry f delta offset))
        (comma_first_sector_writer_point f p delta offset j)"
    "\<And>j. j \<le> elapsed \<Longrightarrow>
      comma_literal_path (elapsed-j) (comma_first_sector_writer_point f p delta offset j)
        (comma_chart_value p (Comma_Near f delta t))"
    using comma_first_sector_writer_cut_exact[OF sector exponent offset packet] by blast+
  have start: "comma_first_sector_writer_point f p delta offset 0 =
      comma_chart_value p (Comma_Entry f delta offset)"
    using cuts(1)[of 0] by (auto elim: comma_literal_path.cases)
  have finish: "comma_first_sector_writer_point f p delta offset elapsed =
      comma_chart_value p (Comma_Near f delta t)"
    using cuts(2)[of elapsed] by (auto elim: comma_literal_path.cases)
  show ?thesis
    using cuts start finish
    by (auto simp: comma_symbolic_writer_action_sound_def
      comma_first_sector_writer_def comma_first_sector_writer_value_def
      intro: comma_literal_path.zero)
qed

theorem comma_first_sector_writer_selected_cut:
  assumes sector: "1 \<le> f" "f \<le> 9"
    and exponent: "5 \<le> p" and offset: "offset \<le> 98"
    and packet: "comma_c1_first_sector f p delta offset = (elapsed,t,event)"
    and bound: "j \<le> elapsed"
  shows "comma_literal_path j (comma_chart_value p (Comma_Entry f delta offset))
      (comma_writer_point (comma_first_sector_writer f p delta offset elapsed t) False j)"
    and "comma_literal_path (elapsed-j)
      (comma_writer_point (comma_first_sector_writer f p delta offset elapsed t) False j)
      (comma_chart_value p (Comma_Near f delta t))"
  using comma_symbolic_writer_checked_cut[
      OF comma_first_sector_writer_source[OF sector exponent offset packet],
      where s=False and i=j] bound
  by (simp_all add: comma_first_sector_writer_def comma_first_sector_writer_value_def)



theorem comma_first_sector_writer_continue:
  assumes sector: "1 \<le> f" "f \<le> 9"
    and exponent: "5 \<le> p" and offset: "offset \<le> 98"
    and packet: "comma_c1_first_sector f p delta offset =
      (elapsed,t,Comma_Next target)"
  defines "writer \<equiv> comma_first_sector_writer f p delta offset elapsed t"
  shows "comma_literal_path (Suc (comma_writer_duration writer False))
      (comma_first_sector_writer_value f p delta offset t False)
      (comma_chart_value p target)"
    and "comma_large_children f (p+delta) (comma_writer_point writer False elapsed) =
      [comma_chart_value p target]"
proof -
  have sound: "comma_symbolic_writer_action_sound
      (comma_first_sector_writer_value f p delta offset t) (\<lambda>_. True) writer"
    using comma_first_sector_writer_source[OF sector exponent offset packet]
    by (simp add: writer_def)
  note selected = spec[OF sound[unfolded comma_symbolic_writer_action_sound_def], of False]
  have endpoint: "comma_writer_point writer False elapsed =
      comma_chart_value p (Comma_Near f delta t)"
    using selected by (auto simp: writer_def comma_first_sector_writer_def
      comma_first_sector_writer_value_def)
  show "comma_literal_path (Suc (comma_writer_duration writer False))
      (comma_first_sector_writer_value f p delta offset t False)
      (comma_chart_value p target)"
    using comma_c1_first_sector_next(1)[OF sector exponent offset packet]
    by (simp add: writer_def comma_first_sector_writer_def
      comma_first_sector_writer_value_def)
  show "comma_large_children f (p+delta) (comma_writer_point writer False elapsed) =
      [comma_chart_value p target]"
    using comma_c1_first_sector_next(2)[OF sector exponent offset packet]
    by (simp only: endpoint)
qed

theorem comma_first_sector_writer_fork:
  assumes sector: "1 \<le> f" "f \<le> 9"
    and exponent: "5 \<le> p" and offset: "offset \<le> 98"
    and packet: "comma_c1_first_sector f p delta offset =
      (elapsed,t,Comma_Fork a delta)"
  defines "writer \<equiv> comma_first_sector_writer f p delta offset elapsed t"
  shows "comma_writer_duration writer False = elapsed"
    and "comma_writer_point writer False elapsed =
      comma_chart_value p (Comma_Near f delta t)"
    and "comma_large_children f (p+delta) (comma_writer_point writer False elapsed) =
      [comma_near_boundary a (p+delta), comma_zero_boundary a (p+delta)]"
proof -
  have sound: "comma_symbolic_writer_action_sound
      (comma_first_sector_writer_value f p delta offset t) (\<lambda>_. True) writer"
    using comma_first_sector_writer_source[OF sector exponent offset packet]
    by (simp add: writer_def)
  note selected = spec[OF sound[unfolded comma_symbolic_writer_action_sound_def], of False]
  have endpoint: "comma_writer_point writer False elapsed =
      comma_chart_value p (Comma_Near f delta t)"
    using selected by (auto simp: writer_def comma_first_sector_writer_def
      comma_first_sector_writer_value_def)
  show "comma_writer_duration writer False = elapsed"
    by (simp add: writer_def comma_first_sector_writer_def)
  show "comma_writer_point writer False elapsed =
      comma_chart_value p (Comma_Near f delta t)" by (rule endpoint)
  show "comma_large_children f (p+delta) (comma_writer_point writer False elapsed) =
      [comma_near_boundary a (p+delta), comma_zero_boundary a (p+delta)]"
    using comma_c1_first_sector_fork(3)[OF sector exponent offset packet]
    by (simp only: endpoint)
qed

theorem comma_first_sector_writer_landmine:
  assumes sector: "1 \<le> f" "f \<le> 9"
    and exponent: "5 \<le> p" and offset: "offset \<le> 98"
    and packet: "comma_c1_first_sector f p delta offset =
      (elapsed,t,Comma_Landmine delta)"
  defines "writer \<equiv> comma_first_sector_writer f p delta offset elapsed t"
  shows "comma_writer_duration writer False = elapsed"
    and "\<nexists>target. comma_child (comma_writer_point writer False elapsed) target"
proof -
  have sound: "comma_symbolic_writer_action_sound
      (comma_first_sector_writer_value f p delta offset t) (\<lambda>_. True) writer"
    using comma_first_sector_writer_source[OF sector exponent offset packet]
    by (simp add: writer_def)
  note selected = spec[OF sound[unfolded comma_symbolic_writer_action_sound_def], of False]
  have endpoint: "comma_writer_point writer False elapsed =
      comma_chart_value p (Comma_Near f delta t)"
    using selected by (auto simp: writer_def comma_first_sector_writer_def
      comma_first_sector_writer_value_def)
  show "comma_writer_duration writer False = elapsed"
    by (simp add: writer_def comma_first_sector_writer_def)
  show "\<nexists>target. comma_child (comma_writer_point writer False elapsed) target"
    by (subst endpoint) (rule comma_c1_first_sector_landmine(2)[OF sector exponent offset packet])
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles @{thms
    comma_first_sector_writer_cut_exact comma_first_sector_writer_source
    comma_first_sector_writer_selected_cut comma_first_sector_writer_continue
    comma_first_sector_writer_fork
    comma_first_sector_writer_landmine}) then ()
    else error "First-sector symbolic writer used an oracle";
  val _ = if Thm_Deps.has_skip_proof @{thms
    comma_first_sector_writer_cut_exact comma_first_sector_writer_source
    comma_first_sector_writer_selected_cut comma_first_sector_writer_continue
    comma_first_sector_writer_fork
    comma_first_sector_writer_landmine}
    then error "First-sector symbolic writer used a skipped proof" else ();
\<close>

end
