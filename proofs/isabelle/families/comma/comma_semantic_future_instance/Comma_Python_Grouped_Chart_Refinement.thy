theory Comma_Python_Grouped_Chart_Refinement
  imports Comma_Python_Grouped_Near_Refinement
begin

text \<open>
The Python grouped iterator replaces a strict-interior Near run by the
classifier's first decisive Near endpoint.  This theory relates that actual
move record to a finite scalar chart walk: the grouped move consumes exactly
the scalar Near prefix, after which execution continues at the decisive
endpoint (which may still cross to an Entry chart).
\<close>

definition comma_python_grouped_near_interior ::
  "comma_finite_position \<Rightarrow> bool" where
  "comma_python_grouped_near_interior position \<longleftrightarrow>
    (case position of
       Comma_Entry f delta offset \<Rightarrow> False
     | Comma_Near f delta h \<Rightarrow>
         10 * ((10 - h mod 10) mod 10) + f +
           (if f < 9 then 1 else 0) < h)"

definition comma_python_grouped_chart_step ::
  "nat \<Rightarrow> comma_finite_position \<Rightarrow>
    comma_python_chart_move option" where
  "comma_python_grouped_chart_step residue position =
    (if comma_python_grouped_near_interior position then
       (case position of
          Comma_Entry f delta offset \<Rightarrow>
            comma_python_scalar_chart_step residue position
        | Comma_Near f delta h \<Rightarrow>
            (let result = comma_python_classify_near_port_summary f h;
                 n = comma_python_near_port_steps result;
                 t = comma_python_near_port_terminal result
             in Some \<lparr>
               comma_python_chart_next = Some (Comma_Near f delta t),
               comma_python_chart_weight = Comma_Chart_Weight 0 0 (int n) 1,
               comma_python_chart_fork_a = None,
               comma_python_chart_cycle = None,
               comma_python_chart_terminal = None,
               comma_python_chart_literal_increment = h - t\<rparr>))
     else comma_python_scalar_chart_step residue position)"

lemma comma_python_grouped_chart_step_scalar:
  assumes outside: "\<not> comma_python_grouped_near_interior position"
  shows "comma_python_grouped_chart_step residue position =
    comma_python_scalar_chart_step residue position"
  using outside
  by (simp add: comma_python_grouped_chart_step_def)

lemma comma_python_grouped_chart_step_interior:
  fixes residue f delta h p :: nat
  assumes residue: "residue < 924"
    and leading: "1 \<le> f" "f \<le> 9"
    and headroom: "h \<le> 540"
    and interior:
      "10 * ((10 - h mod 10) mod 10) + f +
        (if f < 9 then 1 else 0) < h"
  defines "result \<equiv> comma_python_classify_near_port_summary f h"
  shows "\<exists>move. comma_python_grouped_chart_step residue
      (Comma_Near f delta h) = Some move \<and>
    comma_python_chart_next move = Some
      (Comma_Near f delta (comma_python_near_port_terminal result)) \<and>
    comma_python_chart_weight move = Comma_Chart_Weight 0 0
      (int (comma_python_near_port_steps result)) 1 \<and>
    comma_python_chart_fork_a move = None \<and>
    comma_python_chart_cycle move = None \<and>
    comma_python_chart_terminal move = None \<and>
    comma_python_chart_literal_increment move = h -
      comma_python_near_port_terminal result \<and>
    comma_round_weighted_prefix p residue
      (comma_python_near_port_steps result)
      (Comma_Near f delta h)
      (Comma_Near f delta (comma_python_near_port_terminal result))
      (comma_python_near_port_steps result) \<and>
    comma_python_chart_position_admitted
      (Comma_Near f delta (comma_python_near_port_terminal result))"
proof -
  let ?move = "\<lparr>
    comma_python_chart_next = Some
      (Comma_Near f delta (comma_python_near_port_terminal result)),
    comma_python_chart_weight = Comma_Chart_Weight 0 0
      (int (comma_python_near_port_steps result)) 1,
    comma_python_chart_fork_a = None,
    comma_python_chart_cycle = None,
    comma_python_chart_terminal = None,
    comma_python_chart_literal_increment = h -
      comma_python_near_port_terminal result\<rparr>"
  note classifier = comma_python_grouped_near_classifier_prefix
    [of f h delta p residue, OF leading interior headroom,
      folded result_def]
  note chart_contract = comma_python_grouped_near_chart_contract
    [of f h delta p residue, OF leading interior headroom,
      folded result_def]
  have terminal_bound:
    "comma_python_near_port_terminal result \<le> 540"
    using classifier(3) headroom by arith
  have guard:
    "comma_python_grouped_near_interior (Comma_Near f delta h)"
    using interior by (simp add: comma_python_grouped_near_interior_def)
  have step:
    "comma_python_grouped_chart_step residue (Comma_Near f delta h) =
      Some ?move"
    using guard by (simp add: comma_python_grouped_chart_step_def result_def)
  have target_admitted:
    "comma_python_chart_position_admitted
      (Comma_Near f delta (comma_python_near_port_terminal result))"
    using leading classifier(7) terminal_bound
    by (cases "f < 9")
      (simp_all add: comma_python_chart_position_admitted_def; arith)
  show ?thesis
    using step chart_contract(4) target_admitted
    by (intro exI[of _ ?move]) (simp add: ?move_def)
qed

lemma comma_near_prefix_step_weighted:
  assumes edge:
    "comma_finite_step 0 (Comma_Near f 0 h) =
      Comma_Next (Comma_Near f 0 j)"
  shows "comma_weighted_step (p mod 924) (Comma_Near f delta h) =
    Comma_WNext (Comma_Near f delta j) (Comma_Chart_Weight 0 0 1 1)"
  using edge
  by (auto simp: comma_finite_step_def comma_erase_weight.simps
      comma_weighted_step_def comma_chart_weight_unit Let_def
      split: if_splits)

lemma comma_python_scalar_chart_walk_cut_near_prefix:
  assumes walk:
    "comma_python_scalar_chart_walk p (Comma_Near f delta h)
      moves outcome terminal"
    and prefix: "comma_near_prefix n f h t"
  shows "\<exists>prefix_moves suffix_moves.
    moves = prefix_moves @ suffix_moves \<and>
    length prefix_moves = n \<and>
    comma_python_scalar_chart_walk p (Comma_Near f delta t)
      suffix_moves outcome terminal"
  using walk prefix
proof (induction n arbitrary: h delta moves outcome terminal)
  case 0
  then show ?case by (intro exI[of _ "[]"] exI[of _ moves]) simp
next
  case (Suc n)
  then obtain j where edge:
      "comma_finite_step 0 (Comma_Near f 0 h) =
        Comma_Next (Comma_Near f 0 j)"
    and tail_prefix: "comma_near_prefix n f j t"
    by (cases n; auto)
  have weighted_edge:
      "comma_weighted_step (p mod 924) (Comma_Near f delta h) =
        Comma_WNext (Comma_Near f delta j)
          (Comma_Chart_Weight 0 0 1 1)"
    by (rule comma_near_prefix_step_weighted[OF edge])
  from Suc.prems(1) show ?case
  proof cases
    case (fork p0 source0 a0 delta0 move0)
    then show ?thesis using weighted_edge by simp
  next
    case (landmine p0 source0 delta0 move0)
    then show ?thesis using weighted_edge by simp
  next
    case (advance p0 source0 successor weight move rest_moves
        outcome0 terminal0)
    have successor:
      "successor = Comma_Near f delta j"
      and weight:
      "weight = Comma_Chart_Weight 0 0 1 1"
      using advance.hyps(1) weighted_edge by simp_all
    obtain prefix_moves suffix_moves where split:
        "rest_moves = prefix_moves @ suffix_moves"
      and prefix_length: "length prefix_moves = n"
      and tail_walk:
        "comma_python_scalar_chart_walk p (Comma_Near f delta t)
          suffix_moves outcome terminal"
      using Suc.IH[of j delta rest_moves outcome terminal]
        advance.hyps(5) tail_prefix by blast
    show ?thesis
      using advance.hyps(2-4) successor split prefix_length tail_walk
      by (intro exI[of _ "move # prefix_moves"]
          exI[of _ suffix_moves]) auto
  qed
qed

lemma comma_python_near_prefix_has_first_edge:
  assumes prefix: "comma_near_prefix (Suc n) f h t"
  obtains j where
    "comma_finite_step 0 (Comma_Near f 0 h) =
      Comma_Next (Comma_Near f 0 j)"
proof using prefix by auto

lemma comma_python_near_prefix_positive_has_first_edge:
  assumes positive: "0 < n"
    and prefix: "comma_near_prefix n f h t"
  obtains j where
    "comma_finite_step 0 (Comma_Near f 0 h) =
      Comma_Next (Comma_Near f 0 j)"
proof -
  obtain k where n: "n = Suc k" using positive by (cases n) auto
  show thesis
    using comma_python_near_prefix_has_first_edge[of k f h t] prefix n
    by (intro that) simp
qed

lemma comma_python_scalar_chart_walk_nonempty:
  assumes walk:
    "comma_python_scalar_chart_walk p source moves outcome terminal"
  shows "moves \<noteq> []"
  using walk
  by (cases rule: comma_python_scalar_chart_walk.cases) auto

lemma comma_python_scalar_terminal_near_not_interior:
  assumes sector: "1 \<le> f" "f \<le> 9"
    and headroom: "1 \<le> h" "h \<le> 540"
    and walk:
      "comma_python_scalar_chart_walk p (Comma_Near f delta h)
        [move] outcome (Comma_Near f delta h)"
  shows "\<not> comma_python_grouped_near_interior
    (Comma_Near f delta h)"
proof
  assume interior:
    "comma_python_grouped_near_interior (Comma_Near f delta h)"
  then have guard:
    "10 * ((10 - h mod 10) mod 10) + f +
      (if f < 9 then 1 else 0) < h"
    by (simp add: comma_python_grouped_near_interior_def)
  have contract: "0 < comma_python_near_port_steps
      (comma_python_classify_near_port_summary f h)"
      "comma_near_prefix
        (comma_python_near_port_steps
          (comma_python_classify_near_port_summary f h)) f h
        (comma_python_near_port_terminal
          (comma_python_classify_near_port_summary f h))"
    using comma_python_grouped_near_chart_contract
      [of f h delta p p] sector guard headroom by blast+
  have positive_prefix:
    "0 < comma_python_near_port_steps
      (comma_python_classify_near_port_summary f h)"
    using contract(1) .
  from comma_python_near_prefix_positive_has_first_edge
      [OF positive_prefix contract(2)]
  obtain j where edge:
    "comma_finite_step 0 (Comma_Near f 0 h) =
      Comma_Next (Comma_Near f 0 j)" .
  have weighted:
    "comma_weighted_step (p mod 924) (Comma_Near f delta h) =
      Comma_WNext (Comma_Near f delta j) (Comma_Chart_Weight 0 0 1 1)"
    by (rule comma_near_prefix_step_weighted[OF edge])
  from walk show False
  proof cases
    case (fork p0 source0 a0 delta0 move0)
    then show ?thesis using weighted by simp
  next
    case (landmine p0 source0 delta0 move0)
    then show ?thesis using weighted by simp
  next
    case (advance p0 source0 successor weight move0 tail_moves
        outcome0 terminal0)
    have tail_nonempty:
      "tail_moves \<noteq> []"
      by (rule comma_python_scalar_chart_walk_nonempty[OF advance.hyps(5)])
    then show ?thesis using advance by simp
  qed
qed

inductive comma_python_grouped_chart_walk ::
  "nat \<Rightarrow> comma_finite_position \<Rightarrow>
    comma_python_chart_move list \<Rightarrow> comma_finite_outcome \<Rightarrow>
    comma_finite_position \<Rightarrow> bool" where
  fork:
    "comma_weighted_step (p mod 924) source =
        Comma_WFork source a delta \<Longrightarrow>
     comma_python_grouped_chart_step (p mod 924) source = Some move \<Longrightarrow>
     comma_python_chart_move_erasure source move =
        comma_finite_step (p mod 924) source \<Longrightarrow>
     comma_python_chart_move_matches_weighted source move
        (Comma_WFork source a delta) \<Longrightarrow>
     comma_python_grouped_chart_walk p source [move]
       (Comma_Fork_At a delta) source"
| landmine:
    "comma_weighted_step (p mod 924) source =
        Comma_WLandmine source delta \<Longrightarrow>
     comma_python_grouped_chart_step (p mod 924) source = Some move \<Longrightarrow>
     comma_python_chart_move_erasure source move =
        comma_finite_step (p mod 924) source \<Longrightarrow>
     comma_python_chart_move_matches_weighted source move
        (Comma_WLandmine source delta) \<Longrightarrow>
     comma_python_grouped_chart_walk p source [move]
       (Comma_Landmine_At delta) source"
| advance:
    "comma_weighted_step (p mod 924) source =
        Comma_WNext successor weight \<Longrightarrow>
     comma_python_grouped_chart_step (p mod 924) source = Some move \<Longrightarrow>
     comma_python_chart_next move = Some successor \<Longrightarrow>
     comma_python_chart_move_erasure source move =
        comma_finite_step (p mod 924) source \<Longrightarrow>
     comma_python_chart_move_matches_weighted source move
        (Comma_WNext successor weight) \<Longrightarrow>
     comma_python_grouped_chart_walk p successor moves outcome terminal \<Longrightarrow>
     comma_python_grouped_chart_walk p source (move # moves) outcome terminal"
| grouped_near:
    "source = Comma_Near f delta h \<Longrightarrow>
     comma_python_grouped_near_interior source \<Longrightarrow>
     result = comma_python_classify_near_port_summary f h \<Longrightarrow>
     comma_python_grouped_chart_step (p mod 924) source = Some move \<Longrightarrow>
     comma_python_chart_next move = Some
       (Comma_Near f delta (comma_python_near_port_terminal result)) \<Longrightarrow>
     comma_python_chart_weight move = Comma_Chart_Weight 0 0
       (int (comma_python_near_port_steps result)) 1 \<Longrightarrow>
     comma_python_chart_fork_a move = None \<Longrightarrow>
     comma_python_chart_cycle move = None \<Longrightarrow>
     comma_python_chart_terminal move = None \<Longrightarrow>
     comma_python_chart_literal_increment move = h -
       comma_python_near_port_terminal result \<Longrightarrow>
     comma_round_weighted_prefix p (p mod 924)
       (comma_python_near_port_steps result) source
       (Comma_Near f delta (comma_python_near_port_terminal result))
       (comma_python_near_port_steps result) \<Longrightarrow>
     comma_python_grouped_chart_walk p
       (Comma_Near f delta (comma_python_near_port_terminal result))
       moves outcome terminal \<Longrightarrow>
     comma_python_grouped_chart_walk p source (move # moves)
       outcome terminal"

lemma comma_python_grouped_chart_walk_of_scalar:
  assumes scalar:
    "comma_python_scalar_chart_walk p source scalar_moves outcome terminal"
    and exponent: "5 \<le> p"
    and admitted: "comma_python_chart_position_admitted source"
  shows "\<exists>moves. comma_python_grouped_chart_walk p source moves
    outcome terminal"
  using scalar exponent admitted
proof (induction "length scalar_moves"
    arbitrary: source scalar_moves outcome terminal rule: less_induct)
  case less
  note walk = less.prems(1)
  note exponent = less.prems(2)
  note admitted = less.prems(3)
  show ?case
  using walk
  proof cases
    case (fork p0 source0 a delta move)
    have outside: "\<not> comma_python_grouped_near_interior source"
    proof (cases source)
      case (Comma_Entry f d x)
      then show ?thesis by (simp add: comma_python_grouped_near_interior_def)
    next
      case (Comma_Near f d h)
      have fields: "1 \<le> f" "f \<le> 9" "1 \<le> h" "h \<le> 540"
        using admitted Comma_Near
        by (simp_all add: comma_python_chart_position_admitted_def)
      have terminal_walk:
        "comma_python_scalar_chart_walk p (Comma_Near f d h) [move]
          (Comma_Fork_At a delta) (Comma_Near f d h)"
        using fork Comma_Near by simp
      show ?thesis
        using comma_python_scalar_terminal_near_not_interior
          [OF fields terminal_walk] Comma_Near by simp
    qed
    have step:
      "comma_python_grouped_chart_step (p mod 924) source =
        comma_python_scalar_chart_step (p mod 924) source"
      by (rule comma_python_grouped_chart_step_scalar[OF outside])
    show ?thesis
      using fork step
      by (intro exI[of _ "[move]"] comma_python_grouped_chart_walk.fork)
        (auto simp: comma_python_chart_move_erasure_def)
  next
    case (landmine p0 source0 delta move)
    have outside: "\<not> comma_python_grouped_near_interior source"
    proof (cases source)
      case (Comma_Entry f d x)
      then show ?thesis by (simp add: comma_python_grouped_near_interior_def)
    next
      case (Comma_Near f d h)
      have fields: "1 \<le> f" "f \<le> 9" "1 \<le> h" "h \<le> 540"
        using admitted Comma_Near
        by (simp_all add: comma_python_chart_position_admitted_def)
      have terminal_walk:
        "comma_python_scalar_chart_walk p (Comma_Near f d h) [move]
          (Comma_Landmine_At delta) (Comma_Near f d h)"
        using landmine Comma_Near by simp
      show ?thesis
        using comma_python_scalar_terminal_near_not_interior
          [OF fields terminal_walk] Comma_Near by simp
    qed
    have step:
      "comma_python_grouped_chart_step (p mod 924) source =
        comma_python_scalar_chart_step (p mod 924) source"
      by (rule comma_python_grouped_chart_step_scalar[OF outside])
    show ?thesis
      using landmine step
      by (intro exI[of _ "[move]"] comma_python_grouped_chart_walk.landmine)
        (auto simp: comma_python_chart_move_erasure_def)
  next
    case (advance p0 source0 successor weight move tail_moves
        outcome0 terminal0)
    show ?thesis
    proof (cases "comma_python_grouped_near_interior source")
      case False
      have step:
        "comma_python_grouped_chart_step (p mod 924) source =
          comma_python_scalar_chart_step (p mod 924) source"
        by (rule comma_python_grouped_chart_step_scalar[OF False])
      have next:
        "comma_python_chart_next move = Some successor"
        using advance.hyps(4) advance.hyps(1)
        by (simp add: comma_python_chart_move_matches_weighted_def)
      have successor_admitted:
        "comma_python_chart_position_admitted successor"
        by (rule comma_python_scalar_chart_step_preserves_admission
            [OF exponent admitted advance.hyps(2) next])
      have shorter: "length tail_moves < length scalar_moves"
        using advance.hyps(2) by simp
      obtain grouped_tail where grouped_tail:
        "comma_python_grouped_chart_walk p successor grouped_tail
          outcome terminal"
        using less.hyps[of "length tail_moves" successor tail_moves
            outcome terminal]
          shorter advance.hyps(5) exponent successor_admitted
        by blast
      show ?thesis
        using advance step grouped_tail
        by (intro exI[of _ "move # grouped_tail"]
            comma_python_grouped_chart_walk.advance)
          (auto simp: comma_python_chart_move_erasure_def)
    next
      case True
      obtain f delta h where source:
        "source = Comma_Near f delta h"
        using True by (cases source)
          (auto simp: comma_python_grouped_near_interior_def)
      have leading: "1 \<le> f" "f \<le> 9"
        and headroom: "1 \<le> h" "h \<le> 540"
        using admitted source
        by (simp_all add: comma_python_chart_position_admitted_def)
      have interior:
        "10 * ((10 - h mod 10) mod 10) + f +
          (if f < 9 then 1 else 0) < h"
        using True source by (simp add: comma_python_grouped_near_interior_def)
      let ?result = "comma_python_classify_near_port_summary f h"
      let ?n = "comma_python_near_port_steps ?result"
      let ?t = "comma_python_near_port_terminal ?result"
      have result_def: "?result = comma_python_classify_near_port_summary f h"
        by simp
      have classifier:
        "0 < ?n"
        "comma_near_prefix ?n f h ?t"
        "(if f < 9 then 1 else 0) < ?t"
        "?t \<le> 10 * comma_python_near_port_active ?result + f +
          (if f < 9 then 1 else 0)"
        "comma_python_near_port_active ?result \<le> 9"
        using comma_python_grouped_near_classifier_prefix
          [of f h delta p "p mod 924", OF leading interior headroom(2),
            folded result_def]
        by blast+
      have target_admitted:
        "comma_python_chart_position_admitted (Comma_Near f delta ?t)"
        using leading classifier(3-5)
        by (cases "f < 9")
          (auto simp: comma_python_chart_position_admitted_def; arith)
      obtain prefix_moves suffix_moves where cut:
          "scalar_moves = prefix_moves @ suffix_moves"
        and prefix_length: "length prefix_moves = ?n"
        and suffix_walk:
          "comma_python_scalar_chart_walk p (Comma_Near f delta ?t)
            suffix_moves outcome terminal"
        using comma_python_scalar_chart_walk_cut_near_prefix
          [OF walk(1) classifier(2)] by blast
      have shorter: "length suffix_moves < length scalar_moves"
        using prefix_length cut classifier(1) by (simp; arith)
      obtain grouped_tail where grouped_tail:
        "comma_python_grouped_chart_walk p (Comma_Near f delta ?t)
          grouped_tail outcome terminal"
        using less.hyps[of "length suffix_moves" "Comma_Near f delta ?t"
            suffix_moves outcome terminal]
          shorter suffix_walk exponent target_admitted
        by blast
      have residue_bound: "p mod 924 < 924" by simp
      obtain macro where macro_step:
        "comma_python_grouped_chart_step (p mod 924) source = Some macro"
        and macro_target:
        "comma_python_chart_next macro = Some (Comma_Near f delta ?t)"
        and macro_weight:
        "comma_python_chart_weight macro = Comma_Chart_Weight 0 0 (int ?n) 1"
        and macro_fork: "comma_python_chart_fork_a macro = None"
        and macro_cycle: "comma_python_chart_cycle macro = None"
        and macro_terminal: "comma_python_chart_terminal macro = None"
        and macro_increment:
        "comma_python_chart_literal_increment macro = h - ?t"
        and macro_prefix:
        "comma_round_weighted_prefix p (p mod 924) ?n
          source (Comma_Near f delta ?t) ?n"
        using comma_python_grouped_chart_step_interior
          [of "p mod 924" f delta h p,
            OF residue_bound leading(1) leading(2) headroom(2) interior,
            folded source result_def]
        by blast
      have grouped:
        "comma_python_grouped_chart_walk p (Comma_Near f delta ?t)
          grouped_tail outcome terminal"
        using grouped_tail .
      show ?thesis
        using source True macro_step macro_target macro_weight macro_fork
          macro_cycle macro_terminal macro_increment macro_prefix grouped
        by (intro exI[of _ "macro # grouped_tail"]
            comma_python_grouped_chart_walk.grouped_near)
          (simp_all add: source True)
    qed
  qed
qed

lemmas comma_python_grouped_chart_refinement_oracle_audit_bundle =
  comma_python_grouped_chart_step_scalar
  comma_python_grouped_chart_step_interior
  comma_python_scalar_chart_walk_cut_near_prefix
  comma_python_scalar_terminal_near_not_interior
  comma_python_grouped_chart_walk_of_scalar

ML \<open>
val endpoints = @{thms comma_python_grouped_chart_refinement_oracle_audit_bundle}
val _ = Thm.consolidate endpoints
val _ = if null (Thm_Deps.all_oracles endpoints) then ()
  else error "Comma_Python_Grouped_Chart_Refinement local oracle audit failed"
\<close>

end
