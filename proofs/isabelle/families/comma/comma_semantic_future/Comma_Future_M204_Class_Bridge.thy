theory Comma_Future_M204_Class_Bridge
  imports Comma_Future_M204_Class_Rank Comma_Future_M204_Source_Bridge
begin

definition comma_future_m204_graph_control :: "comma_future_m204_row list \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_future_m204_graph_control rows c =
    (case fst (rows ! c) of None \<Rightarrow> 9 | Some digit \<Rightarrow> digit - 1)"

definition comma_future_m204_graph_child :: "comma_future_m204_row list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_future_m204_graph_child rows c side =
    (let children = fst (snd (rows ! c)) in
      if side < length children then Suc (children ! side) else 0)"

lemma comma_future_m204_class_row_decode:
  assumes row: "comma_future_m204_row_checked rows cid"
    and digit: "J < 9"
    and control: "comma_future_m204_graph_control rows cid = Suc J"
    and left: "comma_future_m204_graph_child rows cid 0 =
      (if J=8 then 0 else Suc n)"
    and right: "comma_future_m204_graph_child rows cid 1 =
      (if J=8 then 0 else Suc z)"
  shows "comma_future_m204_step rows cid = Some (comma_future_m204_control J)"
    "comma_future_m204_children rows cid (comma_future_m204_control J) =
      (if J=8 then [] else [n,z])"
proof -
  obtain c children rank where selected: "rows ! cid = (c,children,rank)"
    by (cases "rows ! cid") (auto split: prod.splits)
  have bound: "cid < length rows" using row
    unfolding comma_future_m204_row_checked_def by blast
  have shape: "(case c of None \<Rightarrow> children=[]
      | Some digit \<Rightarrow> 2\<le>digit \<and> digit\<le>9 \<and> length children=2)"
    using row selected
    by (auto simp only: comma_future_m204_row_checked_def prod.case fst_conv snd_conv)
  consider (landmine) "c=None" | (fork) d where "c=Some d" by (cases c) auto
  then have decoded: "comma_future_m204_step rows cid = Some (comma_future_m204_control J) \<and>
    comma_future_m204_children rows cid (comma_future_m204_control J) =
      (if J=8 then [] else [n,z])"
  proof cases
    case landmine
    have j: "J=8" using control landmine selected
      by (simp only: comma_future_m204_graph_control_def selected fst_conv landmine option.simps HOL.simp_thms; arith)
    have empty: "children=[]" using shape landmine by simp
    have step: "comma_future_m204_step rows cid = Some (comma_future_m204_control J)"
      using selected bound landmine j
      by (simp only: comma_future_m204_step_def comma_future_m204_control.simps selected
        bound landmine fst_conv option.simps if_True HOL.simp_thms)
    have kids: "comma_future_m204_children rows cid (comma_future_m204_control J) =
      (if J=8 then [] else [n,z])"
      using selected empty j step
      by (simp only: comma_future_m204_children_def selected fst_conv snd_conv empty
        j if_True HOL.simp_thms)
    show ?thesis using step kids by blast
  next
    case (fork d)
    have d: "d=J+2" using control fork selected
      by (simp only: comma_future_m204_graph_control_def selected fst_conv fork option.simps HOL.simp_thms; arith)
    have j: "J\<noteq>8" using shape fork d by (auto simp only: option.simps; arith)
    have len: "length children=2" using shape fork by simp
    obtain x y where children: "children=[x,y]"
      using len by (auto simp: numeral_2_eq_2 length_Suc_conv)
    have step: "comma_future_m204_step rows cid = Some (comma_future_m204_control J)"
      using selected bound fork d j
      by (simp only: comma_future_m204_step_def comma_future_m204_control.simps selected
        bound fork fst_conv option.simps j if_True if_False d HOL.simp_thms)
    have fields: "x=n" "y=z" using left right selected children j
      by (simp_all add: comma_future_m204_graph_child_def selected children j numeral_2_eq_2)
    have kids: "comma_future_m204_children rows cid (comma_future_m204_control J) =
      (if J=8 then [] else [n,z])"
      using selected bound fork d j children fields
      by (simp only: comma_future_m204_children_def comma_future_m204_step_def
        comma_future_m204_control.simps selected bound fork fst_conv snd_conv option.simps
        j if_True if_False d children fields HOL.simp_thms)
    show ?thesis using step kids by blast
  qed
  show "comma_future_m204_step rows cid = Some (comma_future_m204_control J)"
    using decoded by blast
  show "comma_future_m204_children rows cid (comma_future_m204_control J) =
      (if J=8 then [] else [n,z])" using decoded by blast
qed

lemma comma_future_m204_checked_source_class:
  fixes class_of :: "comma_boundary_state \<Rightarrow> nat"
  assumes bellman: "comma_frontier_m204_bellman D"
    and valid: "comma_boundary_valid q"
    and row: "comma_future_m204_row_checked rows (class_of q)"
    and joins: "\<And>J delta. comma_future_m204_source_output D q = Some (J,delta) \<Longrightarrow>
      comma_future_m204_graph_control rows (class_of q) = Suc J \<and>
      comma_future_m204_graph_child rows (class_of q) 0 =
        (if J=8 then 0 else Suc (class_of (Comma_N,J+2,(snd (snd q)+delta) mod 924))) \<and>
      comma_future_m204_graph_child rows (class_of q) 1 =
        (if J=8 then 0 else Suc (class_of (Comma_Z,J+2,(snd (snd q)+delta) mod 924)))"
  shows "comma_semantic_boundary_control_step comma_semantic_decade_summary q =
      comma_future_m204_step rows (class_of q)"
    "\<And>control. map class_of
      (comma_semantic_boundary_children comma_semantic_decade_summary q control) =
      comma_future_m204_children rows (class_of q) control"
proof -
  obtain J delta where source_result: "comma_future_m204_source_output D q = Some (J,delta)"
    and bound: "J<9"
    and control: "comma_semantic_boundary_control_step comma_semantic_decade_summary q =
      Some (comma_future_m204_control J)"
    and children: "comma_semantic_boundary_children comma_semantic_decade_summary q
      (comma_future_m204_control J) =
      (if J=8 then [] else
        [(Comma_N,J+2,(snd (snd q)+delta) mod 924),
         (Comma_Z,J+2,(snd (snd q)+delta) mod 924)])"
    by (rule comma_future_m204_source_output_exact[OF bellman valid])
  note graph = comma_future_m204_class_row_decode[OF row bound]
  have graph_step: "comma_future_m204_step rows (class_of q) = Some (comma_future_m204_control J)"
    and graph_children: "comma_future_m204_children rows (class_of q) (comma_future_m204_control J) =
      (if J=8 then [] else
        [class_of (Comma_N,J+2,(snd (snd q)+delta) mod 924),
         class_of (Comma_Z,J+2,(snd (snd q)+delta) mod 924)])"
    using graph joins[OF source_result] by blast+
  show "comma_semantic_boundary_control_step comma_semantic_decade_summary q =
      comma_future_m204_step rows (class_of q)" using control graph_step by simp
  fix requested
  show "map class_of (comma_semantic_boundary_children comma_semantic_decade_summary q requested) =
      comma_future_m204_children rows (class_of q) requested"
    using control children graph_step graph_children
    by (cases "requested = comma_future_m204_control J")
       (auto simp: comma_future_m204_children_def comma_semantic_boundary_children_def
         comma_semantic_boundary_control_step_def split: option.splits)
qed

end
