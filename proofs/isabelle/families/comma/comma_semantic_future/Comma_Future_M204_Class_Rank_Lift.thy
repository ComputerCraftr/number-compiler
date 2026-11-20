theory Comma_Future_M204_Class_Rank_Lift
  imports Comma_Future_M204_Class_Bridge
begin

lemma comma_future_m204_source_output_digit_bound:
  assumes bellman: "comma_frontier_m204_bellman D"
    and valid: "comma_boundary_valid q"
    and source_result: "comma_future_m204_source_output D q = Some (J,delta)"
  shows "J<9"
proof -
  obtain J' delta' where exact: "comma_future_m204_source_output D q = Some (J',delta')"
    and bounded: "J'<9"
    by (rule comma_future_m204_source_output_exact[OF bellman valid])
  have "J=J'" using source_result exact by (simp only: option.inject prod.inject)
  with bounded show ?thesis by simp
qed

lemma comma_future_m204_boundary_cases:
  fixes P :: "comma_boundary_state \<Rightarrow> bool"
  assumes valid: "comma_boundary_valid q"
    and n2: "\<And>r. r<924 \<Longrightarrow> P (Comma_N,2,r)"
    and n3: "\<And>r. r<924 \<Longrightarrow> P (Comma_N,3,r)"
    and n4: "\<And>r. r<924 \<Longrightarrow> P (Comma_N,4,r)"
    and n5: "\<And>r. r<924 \<Longrightarrow> P (Comma_N,5,r)"
    and n6: "\<And>r. r<924 \<Longrightarrow> P (Comma_N,6,r)"
    and n7: "\<And>r. r<924 \<Longrightarrow> P (Comma_N,7,r)"
    and n8: "\<And>r. r<924 \<Longrightarrow> P (Comma_N,8,r)"
    and n9: "\<And>r. r<924 \<Longrightarrow> P (Comma_N,9,r)"
    and z2: "\<And>r. r<924 \<Longrightarrow> P (Comma_Z,2,r)"
    and z3: "\<And>r. r<924 \<Longrightarrow> P (Comma_Z,3,r)"
    and z4: "\<And>r. r<924 \<Longrightarrow> P (Comma_Z,4,r)"
    and z5: "\<And>r. r<924 \<Longrightarrow> P (Comma_Z,5,r)"
    and z6: "\<And>r. r<924 \<Longrightarrow> P (Comma_Z,6,r)"
    and z7: "\<And>r. r<924 \<Longrightarrow> P (Comma_Z,7,r)"
    and z8: "\<And>r. r<924 \<Longrightarrow> P (Comma_Z,8,r)"
    and z9: "\<And>r. r<924 \<Longrightarrow> P (Comma_Z,9,r)"
  shows "P q"
proof -
  obtain kind a r where q: "q=(kind,a,r)" by (cases q) auto
  have r: "r<924" and a: "2\<le>a" "a\<le>9"
    using valid q by (auto simp: comma_boundary_valid_def)
  have alternatives: "a=2 \<or> a=3 \<or> a=4 \<or> a=5 \<or> a=6 \<or> a=7 \<or> a=8 \<or> a=9"
    using a by arith
  show ?thesis using alternatives r n2 n3 n4 n5 n6 n7 n8 n9 z2 z3 z4 z5 z6 z7 z8 z9 q
    by (cases kind) blast+
qed

theorem comma_future_m204_source_rank_lift:
  fixes class_of :: "comma_boundary_state \<Rightarrow> nat"
  assumes bellman: "comma_frontier_m204_bellman D"
    and rows: "list_all (comma_future_m204_row_checked classes) [0..<length classes]"
    and bound: "\<And>q. comma_boundary_valid q \<Longrightarrow> class_of q < length classes"
    and joins: "\<And>q J delta. comma_boundary_valid q \<Longrightarrow>
      comma_future_m204_source_output D q = Some (J,delta) \<Longrightarrow>
      comma_future_m204_graph_control classes (class_of q) = Suc J \<and>
      comma_future_m204_graph_child classes (class_of q) 0 =
        (if J=8 then 0 else Suc (class_of (Comma_N,J+2,(snd (snd q)+delta) mod 924))) \<and>
      comma_future_m204_graph_child classes (class_of q) 1 =
        (if J=8 then 0 else Suc (class_of (Comma_Z,J+2,(snd (snd q)+delta) mod 924)))"
  shows "comma_semantic_rank_check comma_boundary_valid
    (comma_future_m204_rank classes \<circ> class_of)
    (comma_semantic_boundary_children comma_semantic_decade_summary)
    (comma_semantic_boundary_control_step comma_semantic_decade_summary)"
proof -
  have class_rank: "comma_semantic_rank_check (comma_future_m204_valid classes)
    (comma_future_m204_rank classes) (comma_future_m204_children classes)
    (comma_future_m204_step classes)"
    by (rule comma_future_m204_checked_rank[OF rows])
  have source_row: "comma_future_m204_row_checked classes (class_of q)"
    if valid: "comma_boundary_valid q" for q
    using rows bound[OF valid] by (simp add: list_all_iff)
  have step: "comma_semantic_boundary_control_step comma_semantic_decade_summary q =
      comma_future_m204_step classes (class_of q)"
    if valid: "comma_boundary_valid q" for q
    by (rule comma_future_m204_checked_source_class(1)[where class_of=class_of and rows=classes, OF bellman valid source_row[OF valid]])
       (use joins[OF valid] in blast)
  have children: "map class_of
      (comma_semantic_boundary_children comma_semantic_decade_summary q control) =
      comma_future_m204_children classes (class_of q) control"
    if valid: "comma_boundary_valid q" for q control
    by (rule comma_future_m204_checked_source_class(2)[where class_of=class_of and rows=classes, OF bellman valid source_row[OF valid]])
       (use joins[OF valid] in blast)
  show ?thesis
    by (rule comma_semantic_rank_check_lifts_through_class_map[OF class_rank])
       (use bound step children in \<open>auto simp: comma_future_m204_valid_def\<close>)+
qed

lemma comma_future_m204_shifted_children_valid:
  assumes digit: "J < 9" and non_landmine: "J \<noteq> 8"
  shows "comma_boundary_valid (Comma_N,J+2,(phase+delta) mod 924)"
    "comma_boundary_valid (Comma_Z,J+2,(phase+delta) mod 924)"
proof -
  have lower: "2 \<le> J+2" by simp
  have upper: "J+2 \<le> 9" using digit non_landmine by arith
  have phase: "(phase+delta) mod 924 < 924" by simp
  show "comma_boundary_valid (Comma_N,J+2,(phase+delta) mod 924)"
    using lower upper phase by (simp only: comma_boundary_valid_def prod.case HOL.simp_thms)
  show "comma_boundary_valid (Comma_Z,J+2,(phase+delta) mod 924)"
    using lower upper phase by (simp only: comma_boundary_valid_def prod.case HOL.simp_thms)
qed

theorem comma_future_m204_morphism_transport:
  fixes source_class target_class :: "comma_boundary_state \<Rightarrow> nat"
  assumes bellman: "comma_frontier_m204_bellman D"
    and same: "\<And>q. comma_boundary_valid q \<Longrightarrow> source_class q = target_class q"
    and work: "\<And>q J delta. comma_boundary_valid q \<Longrightarrow>
      comma_future_m204_source_output D q = Some (J,delta) \<Longrightarrow>
      comma_future_m204_graph_control rows (source_class q) = Suc J \<and>
      comma_future_m204_graph_child rows (source_class q) 0 =
        (if J=8 then 0 else Suc (source_class (Comma_N,J+2,(snd (snd q)+delta) mod 924))) \<and>
      comma_future_m204_graph_child rows (source_class q) 1 =
        (if J=8 then 0 else Suc (source_class (Comma_Z,J+2,(snd (snd q)+delta) mod 924)))"
  shows "\<forall>q J delta. comma_boundary_valid q \<longrightarrow>
    comma_future_m204_source_output D q = Some (J,delta) \<longrightarrow>
    comma_future_m204_graph_control rows (target_class q) = Suc J \<and>
    comma_future_m204_graph_child rows (target_class q) 0 =
      (if J=8 then 0 else Suc (target_class (Comma_N,J+2,(snd (snd q)+delta) mod 924))) \<and>
    comma_future_m204_graph_child rows (target_class q) 1 =
      (if J=8 then 0 else Suc (target_class (Comma_Z,J+2,(snd (snd q)+delta) mod 924)))"
proof (intro allI impI)
  fix q J delta
  assume valid: "comma_boundary_valid q"
    and source_result: "comma_future_m204_source_output D q = Some (J,delta)"
  have digit: "J < 9" by (rule comma_future_m204_source_output_digit_bound[OF bellman valid source_result])
  have source_equal: "source_class q = target_class q" by (rule same[OF valid])
  have checked: "comma_future_m204_graph_control rows (source_class q) = Suc J \<and>
    comma_future_m204_graph_child rows (source_class q) 0 =
      (if J=8 then 0 else Suc (source_class (Comma_N,J+2,(snd (snd q)+delta) mod 924))) \<and>
    comma_future_m204_graph_child rows (source_class q) 1 =
      (if J=8 then 0 else Suc (source_class (Comma_Z,J+2,(snd (snd q)+delta) mod 924)))"
    by (rule work[OF valid source_result])
  show "comma_future_m204_graph_control rows (target_class q) = Suc J \<and>
    comma_future_m204_graph_child rows (target_class q) 0 =
      (if J=8 then 0 else Suc (target_class (Comma_N,J+2,(snd (snd q)+delta) mod 924))) \<and>
    comma_future_m204_graph_child rows (target_class q) 1 =
      (if J=8 then 0 else Suc (target_class (Comma_Z,J+2,(snd (snd q)+delta) mod 924)))"
  proof (cases "J=8")
    case True
    show ?thesis using checked True
      by (simp only: source_equal if_True HOL.simp_thms)
  next
    case False
    note child_valid = comma_future_m204_shifted_children_valid[OF digit False,
      where phase="snd (snd q)" and delta=delta]
    have north: "source_class (Comma_N,J+2,(snd (snd q)+delta) mod 924) =
        target_class (Comma_N,J+2,(snd (snd q)+delta) mod 924)"
      by (rule same[OF child_valid(1)])
    have south: "source_class (Comma_Z,J+2,(snd (snd q)+delta) mod 924) =
        target_class (Comma_Z,J+2,(snd (snd q)+delta) mod 924)"
      by (rule same[OF child_valid(2)])
    show ?thesis using checked False
      by (simp only: source_equal north south if_False HOL.simp_thms)
  qed
qed
theorem comma_future_m204_rank_transport:
  fixes source_class target_class :: "comma_boundary_state \<Rightarrow> nat"
    and class_rank :: "nat \<Rightarrow> nat option"
  assumes bellman: "comma_frontier_m204_bellman D"
    and same: "\<And>q. comma_boundary_valid q \<Longrightarrow> source_class q = target_class q"
    and checked: "comma_semantic_rank_check comma_boundary_valid
      (class_rank \<circ> source_class)
      (comma_semantic_boundary_children comma_semantic_decade_summary)
      (comma_semantic_boundary_control_step comma_semantic_decade_summary)"
  shows "comma_semantic_rank_check comma_boundary_valid
    (class_rank \<circ> target_class)
    (comma_semantic_boundary_children comma_semantic_decade_summary)
    (comma_semantic_boundary_control_step comma_semantic_decade_summary)"
  unfolding comma_semantic_rank_check_def
proof (intro allI impI)
  fix q
  assume valid: "comma_boundary_valid q"
  obtain J delta where source_result: "comma_future_m204_source_output D q = Some (J,delta)"
    and digit: "J < 9"
    and step: "comma_semantic_boundary_control_step comma_semantic_decade_summary q =
      Some (comma_future_m204_control J)"
    and children: "comma_semantic_boundary_children comma_semantic_decade_summary q
      (comma_future_m204_control J) =
      (if J=8 then [] else
        [(Comma_N,J+2,(snd (snd q)+delta) mod 924),
         (Comma_Z,J+2,(snd (snd q)+delta) mod 924)])"
    by (rule comma_future_m204_source_output_exact[OF bellman valid])
  have source_equal: "source_class q = target_class q" by (rule same[OF valid])
  have old: "comma_semantic_rank_row_checked (class_rank \<circ> source_class)
      (comma_semantic_boundary_children comma_semantic_decade_summary)
      (comma_semantic_boundary_control_step comma_semantic_decade_summary) q"
    by (rule comma_semantic_rank_check_row[OF checked valid])
  show "comma_semantic_rank_row_checked (class_rank \<circ> target_class)
      (comma_semantic_boundary_children comma_semantic_decade_summary)
      (comma_semantic_boundary_control_step comma_semantic_decade_summary) q"
  proof (cases "J = 8")
    case True
    have step_landmine: "comma_semantic_boundary_control_step comma_semantic_decade_summary q =
        Some Comma_Future_Landmine"
      using step True by (simp only: comma_future_m204_control.simps if_True HOL.simp_thms)
    have children_landmine: "comma_semantic_boundary_children comma_semantic_decade_summary q
        Comma_Future_Landmine = []"
      using children True by (simp only: comma_future_m204_control.simps if_True HOL.simp_thms)
    show ?thesis using old
      by (simp only: comma_semantic_rank_row_checked_def step_landmine
          children_landmine option.case comma_future_control.case comp_apply
          source_equal HOL.simp_thms)
  next
    case False
    note child_valid = comma_future_m204_shifted_children_valid[OF digit False,
      where phase="snd (snd q)" and delta=delta]
    have left: "source_class (Comma_N,J+2,(snd (snd q)+delta) mod 924) =
        target_class (Comma_N,J+2,(snd (snd q)+delta) mod 924)"
      by (rule same[OF child_valid(1)])
    have right: "source_class (Comma_Z,J+2,(snd (snd q)+delta) mod 924) =
        target_class (Comma_Z,J+2,(snd (snd q)+delta) mod 924)"
      by (rule same[OF child_valid(2)])
    have step_fork: "comma_semantic_boundary_control_step comma_semantic_decade_summary q =
        Some (Comma_Future_Fork (J+2))"
      using step False by (simp only: comma_future_m204_control.simps if_False HOL.simp_thms)
    have children_fork: "comma_semantic_boundary_children comma_semantic_decade_summary q
        (Comma_Future_Fork (J+2)) =
        [(Comma_N,J+2,(snd (snd q)+delta) mod 924),
         (Comma_Z,J+2,(snd (snd q)+delta) mod 924)]"
      using children False by (simp only: comma_future_m204_control.simps if_False HOL.simp_thms)
    show ?thesis using old
      by (simp only: comma_semantic_rank_row_checked_def step_fork children_fork
          option.case comma_future_control.case comp_apply list_all_Cons_iff
          list_all_Nil_iff filter.simps source_equal left right HOL.simp_thms)
  qed
qed

end
