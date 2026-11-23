theory Comma_Future_M204_Class_Bridge
  imports Comma_Future_M204_Class_Rank Comma_Future_M204_Source_Bridge
begin

text \<open>An injective, bound-independent ordered tuple code.  This avoids
  treating equal-rank children or bounded modular residues as interchangeable.
  It is independent of the number of graph classes, so class bounds remain a
  separate certified predicate.\<close>

definition comma_future_m204_pair :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_future_m204_pair a b = (a+b)*(a+b+1)+2*b"

lemma comma_future_m204_pair_injective:
  assumes same: "comma_future_m204_pair a b = comma_future_m204_pair c d"
  shows "a=c \<and> b=d"
proof -
  let ?s = "a+b"
  let ?t = "c+d"
  have low_s: "?s*(?s+1) \<le> comma_future_m204_pair a b"
    by (simp add: comma_future_m204_pair_def)
  have b_bound: "b \<le> ?s"
    by (simp add: add.commute)
  have upper_s: "(?s+1)*(?s+2) = ?s*(?s+1)+2*?s+2"
    by (simp add: algebra_simps)
  have pair_s: "comma_future_m204_pair a b = ?s*(?s+1)+2*b"
    by (simp add: comma_future_m204_pair_def)
  have high_s: "comma_future_m204_pair a b < (?s+1)*(?s+2)"
    using b_bound pair_s upper_s by arith
  have low_t: "?t*(?t+1) \<le> comma_future_m204_pair c d"
    by (simp add: comma_future_m204_pair_def)
  have d_bound: "d \<le> ?t"
    by (simp add: add.commute)
  have upper_t: "(?t+1)*(?t+2) = ?t*(?t+1)+2*?t+2"
    by (simp add: algebra_simps)
  have pair_t: "comma_future_m204_pair c d = ?t*(?t+1)+2*d"
    by (simp add: comma_future_m204_pair_def)
  have high_t: "comma_future_m204_pair c d < (?t+1)*(?t+2)"
    using d_bound pair_t upper_t by arith
  have sum: "?s=?t"
  proof (rule ccontr)
    assume "?s \<noteq> ?t"
    then consider "?s < ?t" | "?t < ?s" by linarith
    then show False
    proof cases
      case 1
      have "(?s+1)*(?s+2) \<le> ?t*(?t+1)"
        using 1 by (intro mult_le_mono) auto
      with same high_s low_t show False by linarith
    next
      case 2
      have "(?t+1)*(?t+2) \<le> ?s*(?s+1)"
        using 2 by (intro mult_le_mono) auto
      with same high_t low_s show False by linarith
    qed
  qed
  have pair_equal: "?s*(?s+1)+2*b = ?s*(?s+1)+2*d"
  proof -
    have "?s*(?s+1)+2*b = comma_future_m204_pair a b"
      using pair_s by simp
    also have "... = comma_future_m204_pair c d"
      using same by simp
    also have "... = ?t*(?t+1)+2*d"
      using pair_t by simp
    also have "... = ?s*(?s+1)+2*d"
      using sum by simp
    finally show ?thesis .
  qed
  have "b=d" using pair_equal by arith
  with sum show ?thesis by linarith
qed

lemma comma_future_m204_pair_eq_iff [simp]:
  "comma_future_m204_pair a b = comma_future_m204_pair c d \<longleftrightarrow>
    a=c \<and> b=d"
  using comma_future_m204_pair_injective by blast

lemma comma_future_m204_ordered_tuple_eq_iff [simp]:
  "comma_future_m204_pair (comma_future_m204_pair a b) c =
    comma_future_m204_pair (comma_future_m204_pair x y) z \<longleftrightarrow>
    a=x \<and> b=y \<and> c=z"
  by simp

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

text \<open>A source-issued typed crossing can authenticate its ordered row
without a global Bellman action. The two child-class joins remain explicit;
equality of terminal labels alone does not establish them.\<close>

lemma comma_future_typed_crossing_source_class:
  fixes class_of :: "comma_boundary_state \<Rightarrow> nat"
    and provider :: "comma_decade_state \<Rightarrow> comma_decade_residual option"
  assumes valid: "comma_boundary_valid q"
    and close: "comma_round_close (snd (snd q)) (comma_finite_initial q) =
      (steps,final,Comma_Round_Cross (Comma_Entry 1 1 x))"
    and selected: "provider (Comma_Decade ((snd (snd q)+1) mod 924) x) = Some (h,tau)"
    and summary: "comma_decade_exact_summary
      (Comma_Decade ((snd (snd q)+1) mod 924) x) h tau"
    and row: "comma_future_m204_row_checked rows (class_of q)"
    and joins: "comma_future_m204_graph_control rows (class_of q) =
        Suc (comma_terminal_weight_digit tau)"
      "comma_future_m204_graph_child rows (class_of q) 0 =
        (if comma_terminal_weight_digit tau=8 then 0 else
          Suc (class_of (Comma_N,comma_terminal_weight_digit tau+2,
            (snd (snd q)+1+h) mod 924)))"
      "comma_future_m204_graph_child rows (class_of q) 1 =
        (if comma_terminal_weight_digit tau=8 then 0 else
          Suc (class_of (Comma_Z,comma_terminal_weight_digit tau+2,
            (snd (snd q)+1+h) mod 924)))"
  shows "comma_semantic_boundary_control_step provider q =
      comma_future_m204_step rows (class_of q)"
    and "\<And>control. map class_of (comma_semantic_boundary_children provider q control) =
      comma_future_m204_children rows (class_of q) control"
proof -
  let ?J = "comma_terminal_weight_digit tau"
  let ?control = "comma_future_m204_control ?J"
  have terminal: "comma_terminal_weight_admitted tau"
    by (rule comma_decade_exact_summary_terminal_admitted[OF summary])
  have bound: "?J < 9" by (rule comma_terminal_weight_digit_bound[OF terminal])
  note source = comma_future_typed_crossing_ordered_children
    [where provider=provider and q=q and steps=steps and final=final and x=x and h=h
      and tau=tau, OF valid close selected]
  have control_tau: "?control = comma_semantic_boundary_control_of (comma_summary_outcome (h+1) tau)"
  proof (cases tau)
    case Comma_Terminal_Landmine
    then show ?thesis by simp
  next
    case (Comma_Terminal_Fork a)
    then show ?thesis using terminal
      by (auto simp: comma_terminal_weight_admitted_def; arith)
  qed
  have source_control: "comma_semantic_boundary_control_step provider q = Some ?control"
    using source(1) control_tau by simp
  have source_children: "comma_semantic_boundary_children provider q ?control =
      (if ?J=8 then [] else
        [(Comma_N,?J+2,(snd (snd q)+1+h) mod 924),
         (Comma_Z,?J+2,(snd (snd q)+1+h) mod 924)])"
  proof (cases tau)
    case Comma_Terminal_Landmine
    then show ?thesis using source(2) control_tau by simp
  next
    case (Comma_Terminal_Fork a)
    then show ?thesis using source(2) control_tau terminal
      by (auto simp: comma_terminal_weight_admitted_def; arith)
  qed
  have graph_step: "comma_future_m204_step rows (class_of q) = Some ?control"
    and graph_children: "comma_future_m204_children rows (class_of q) ?control =
      (if ?J=8 then [] else
        [class_of (Comma_N,?J+2,(snd (snd q)+1+h) mod 924),
         class_of (Comma_Z,?J+2,(snd (snd q)+1+h) mod 924)])"
    using comma_future_m204_class_row_decode[OF row bound joins] by blast+
  show "comma_semantic_boundary_control_step provider q =
      comma_future_m204_step rows (class_of q)" using source_control graph_step by simp
  fix requested
  show "map class_of (comma_semantic_boundary_children provider q requested) =
      comma_future_m204_children rows (class_of q) requested"
    using source_control source_children graph_step graph_children
    by (cases "requested = ?control")
      (auto simp: comma_future_m204_children_def comma_semantic_boundary_children_def
        comma_semantic_boundary_control_step_def split: option.splits)
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

ML \<open>
  val _ = Comma_Proof_Dependency_Audit.require_paths @{context}
    "Typed crossing source-to-class row"
    ["comma_frontier_m204_bellman", "comma_future_m204_summary_lookup",
     "comma_future_m204_checked_source_class"]
    @{thms comma_future_typed_crossing_source_class};
\<close>

end
