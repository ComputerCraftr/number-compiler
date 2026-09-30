theory Comma_Entry_Port_Refinement
  imports Comma_Entry_Port_Anchor
begin

text \<open>One sector-indexed action is reused across its admitted seeds and
rows. The existing weighted trace owns its digit and dwell arithmetic;
funpow supplies iteration rather than a second primitive recursion. Source
key equality, row and absolute clock remain occurrence obligations. No
forest, losing-classification or all-future theorem is asserted here.\<close>

definition comma_port_action :: "nat \<Rightarrow> (nat\<times>nat) \<Rightarrow> nat\<times>nat" where
  "comma_port_action f state=(comma_port_next f (fst state),
    snd state+comma_port_dwell f (fst state))"

definition comma_port_action_power ::
  "nat \<Rightarrow> nat \<Rightarrow> (nat\<times>nat) \<Rightarrow> nat\<times>nat" where
  "comma_port_action_power f n state=(comma_port_action f ^^ n) state"

lemma comma_port_action_power_trace:
  "comma_port_action_power f n (d,0)=comma_port_weighted_trace f d n"
proof (induction n)
  case 0
  show ?case by (simp add: comma_port_action_power_def)
next
  case (Suc n)
  have successor: "comma_port_action_power f (Suc n) (d,0)=
    comma_port_action f (comma_port_action_power f n (d,0))"
    by (simp add: comma_port_action_power_def)
  show ?case by (simp only: successor Suc.IH comma_port_weighted_trace.simps;
    cases "comma_port_weighted_trace f d n"; simp add: comma_port_action_def)
qed

abbreviation comma_port_action_locator ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat option" where
  "comma_port_action_locator f d row \<equiv> comma_port_weighted_locator f d row"

lemma comma_port_action_locator_refines:
  "comma_port_action_locator f d row=List.find
    (\<lambda>k. row<snd (comma_port_action_power f (Suc k) (d,0)))
    [0..<comma_port_cycle_length f d]"
  by (simp only: comma_port_weighted_locator_def comma_port_action_power_trace)

text \<open>The selected terminal headroom is computed directly from the
active port and the residual row. It is not the source headroom awaiting
another Near scan. The lower bound below is proved before natural subtraction
is used to interpret the residual.\<close>

definition comma_entry_port_refined_locator ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat\<times>nat\<times>nat) option" where
  "comma_entry_port_refined_locator f d eta=
    (let seed=comma_entry_port_seed f d; row=comma_entry_port_row f d eta in
      map_option (\<lambda>k. let state=comma_port_action_power f k (seed,0);
        active=fst state; residual=row-snd state in
        (active,residual,
          10*active+f+(if f<9 then 1 else 0)-(comma_port_low f active+10*residual)))
      (comma_port_action_locator f seed row))"

lemma comma_entry_port_refined_locator_headroom:
  "map_option (\<lambda>(active,residual,h). h)
    (comma_entry_port_refined_locator f d eta)=comma_entry_weighted_headroom f d eta"
  by (simp add: comma_entry_port_refined_locator_def comma_entry_weighted_headroom_def
    comma_port_action_power_trace Let_def option.map_comp comp_def)

lemma comma_entry_port_refined_locator_exact:
  fixes eta seed row :: nat
  assumes sector: "1\<le>f" "f\<le>9" and digit: "d<10"
  defines "seed \<equiv> comma_entry_port_seed f d"
    and "row \<equiv> comma_entry_port_row f d eta"
  shows "\<exists>k<9. \<exists>active weight.
    comma_port_action_locator f seed row=Some k \<and>
    comma_port_action_power f k (seed,0)=(active,weight) \<and>
    1\<le>active \<and> active\<le>9 \<and> weight\<le>row \<and>
    row<weight+comma_port_dwell f active \<and>
    row-weight<comma_port_dwell f active \<and>
    comma_entry_port_refined_locator f d eta=Some
      (active,row-weight,
        10*active+f+(if f<9 then 1 else 0)-(comma_port_low f active+10*(row-weight)))"
proof -
  have law: "comma_entry_port_anchor_law f d"
    by (rule comma_entry_port_anchor_law[OF sector digit])
  have seed_bounds: "1\<le>seed" "seed\<le>9"
    using law by (auto simp: seed_def comma_entry_port_anchor_law_def)
  have row_bound: "row<comma_finite_period f seed div 10"
    using comma_entry_port_row_bound[OF sector digit, of eta]
    by (simp only: seed_def row_def)
  obtain k where k: "k<9"
    and selected: "comma_port_weighted_locator f seed row=Some k"
    and lower: "snd (comma_port_weighted_trace f seed k)\<le>row"
    and upper: "row<snd (comma_port_weighted_trace f seed (Suc k))"
    using comma_port_weighted_locator_coverage[OF sector seed_bounds row_bound] by blast
  obtain active weight where trace:
    "comma_port_weighted_trace f seed k=(active,weight)"
    by (cases "comma_port_weighted_trace f seed k") auto
  have active_bounds: "1\<le>active" "active\<le>9"
    using comma_port_trace_digit_admitted[OF sector seed_bounds, of k]
    by (simp_all add: trace)
  have successor: "snd (comma_port_weighted_trace f seed (Suc k))=
    weight+comma_port_dwell f active"
    by (simp only: comma_port_weighted_trace.simps trace Let_def prod.case snd_conv)
  have lower_weight: "weight\<le>row" using lower by (simp only: trace snd_conv)
  have upper_weight: "row<weight+comma_port_dwell f active"
    using upper by (simp only: successor)
  have residual: "row-weight<comma_port_dwell f active"
    using lower_weight upper_weight by arith
  have action_trace: "comma_port_action_power f k (seed,0)=(active,weight)"
    by (simp only: comma_port_action_power_trace trace)
  have refined: "comma_entry_port_refined_locator f d eta=Some
    (active,row-weight,
      10*active+f+(if f<9 then 1 else 0)-(comma_port_low f active+10*(row-weight)))"
    using selected action_trace
    by (simp add: comma_entry_port_refined_locator_def seed_def row_def Let_def)
  show ?thesis using k selected action_trace active_bounds lower_weight upper_weight
    residual refined by blast
qed

theorem comma_entry_nine_action_locator_refines_source:
  assumes sector: "1\<le>f" "f\<le>9" and offset: "x\<le>98"
    and key: "comma_entry_diagonal_key f r delta x=(d,eta)"
  shows "\<exists>active residual h.
    comma_entry_port_refined_locator f d eta=Some (active,residual,h) \<and>
    1\<le>active \<and> active\<le>9 \<and>
    residual<comma_port_dwell f active \<and>
    comma_fast_sector_target r (Comma_Entry f delta x)=Comma_Near f delta h"
proof -
  have actual_digit: "d=x mod 10" using key
    by (simp add: comma_entry_diagonal_key_def prod_eq_iff)
  have digit: "d<10" using actual_digit by simp
  obtain active residual h where refined:
    "comma_entry_port_refined_locator f d eta=Some (active,residual,h)"
    and active: "1\<le>active" "active\<le>9"
    and residual: "residual<comma_port_dwell f active"
    using comma_entry_port_refined_locator_exact[OF sector digit, of eta] by blast
  have headroom: "comma_entry_weighted_headroom f d eta=Some h"
    using comma_entry_port_refined_locator_headroom[of f d eta]
    by (simp only: refined option.map prod.case)
  have target: "comma_fast_sector_target r (Comma_Entry f delta x)=Comma_Near f delta h"
    using comma_entry_weighted_target(2)[OF sector offset key]
    by (simp only: headroom option.sel)
  show ?thesis using refined active residual target by blast
qed

corollary comma_entry_reduced_key_locator_refines_source:
  assumes sector: "1\<le>f" "f\<le>9" and offset: "x\<le>98"
    and reduced_key: "reduced_key=comma_entry_diagonal_key f r delta x"
  shows "\<exists>d eta active residual h.
    reduced_key=(d,eta) \<and>
    comma_entry_port_refined_locator f d eta=Some (active,residual,h) \<and>
    1\<le>active \<and> active\<le>9 \<and>
    residual<comma_port_dwell f active \<and>
    comma_fast_sector_target r (Comma_Entry f delta x)=Comma_Near f delta h"
proof -
  obtain d eta where pair: "reduced_key=(d,eta)" by (cases reduced_key) auto
  have key: "comma_entry_diagonal_key f r delta x=(d,eta)" using reduced_key pair by simp
  show ?thesis using comma_entry_nine_action_locator_refines_source[OF sector offset key]
    pair by blast
qed

text \<open>A search tree stores its finite split weights. The prefix function
is used only to certify those constants; lookup itself neither constructs a
weighted trace nor evaluates a prefix. Its interval certificate retains both
bounds, including the lower bound needed before natural subtraction.\<close>

datatype comma_prefix_search_tree =
    Comma_Prefix_Leaf nat nat nat nat
  | Comma_Prefix_Split nat nat comma_prefix_search_tree comma_prefix_search_tree

fun comma_prefix_tree_covers ::
  "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> comma_prefix_search_tree \<Rightarrow> bool" where
  "comma_prefix_tree_covers P lo hi (Comma_Prefix_Leaf k digit lower upper)=(lo=k \<and> hi=Suc k)"
| "comma_prefix_tree_covers P lo hi (Comma_Prefix_Split m threshold left right)=
    (lo<m \<and> m<hi \<and> threshold=P m \<and>
      comma_prefix_tree_covers P lo m left \<and>
      comma_prefix_tree_covers P m hi right)"

fun comma_prefix_tree_select :: "nat \<Rightarrow> comma_prefix_search_tree \<Rightarrow> nat" where
  "comma_prefix_tree_select row (Comma_Prefix_Leaf k digit lower upper)=k"
| "comma_prefix_tree_select row (Comma_Prefix_Split m threshold left right)=
    (if row<threshold then comma_prefix_tree_select row left
      else comma_prefix_tree_select row right)"

lemma comma_prefix_tree_select_interval:
  assumes cover: "comma_prefix_tree_covers P lo hi tree"
    and monotone: "mono P" and lower: "P lo\<le>row" and upper: "row<P hi"
  shows "lo\<le>comma_prefix_tree_select row tree \<and>
    comma_prefix_tree_select row tree<hi \<and>
    P (comma_prefix_tree_select row tree)\<le>row \<and>
    row<P (Suc (comma_prefix_tree_select row tree))"
  using assms
proof (induction tree arbitrary: lo hi)
  case (Comma_Prefix_Leaf k digit lower upper)
  then show ?case by simp
next
  case (Comma_Prefix_Split m threshold left right)
  have cuts: "lo<m" "m<hi" "threshold=P m"
    and left: "comma_prefix_tree_covers P lo m left"
    and right: "comma_prefix_tree_covers P m hi right"
    using Comma_Prefix_Split.prems(1) by simp_all
  show ?case
  proof (cases "row<threshold")
    case True
    have bound: "row<P m" using True cuts(3) by simp
    have selected: "lo\<le>comma_prefix_tree_select row left \<and>
      comma_prefix_tree_select row left<m \<and>
      P (comma_prefix_tree_select row left)\<le>row \<and>
      row<P (Suc (comma_prefix_tree_select row left))"
      by (rule Comma_Prefix_Split.IH(1)[OF left
        Comma_Prefix_Split.prems(2,3) bound])
    show ?thesis using selected cuts(2) by (simp add: True; arith)
  next
    case False
    have bound: "P m\<le>row" using False cuts(3) by simp
    have selected: "m\<le>comma_prefix_tree_select row right \<and>
      comma_prefix_tree_select row right<hi \<and>
      P (comma_prefix_tree_select row right)\<le>row \<and>
      row<P (Suc (comma_prefix_tree_select row right))"
      by (rule Comma_Prefix_Split.IH(2)[OF right
        Comma_Prefix_Split.prems(2) bound Comma_Prefix_Split.prems(4)])
    show ?thesis using selected cuts(1) by (simp add: False; arith)
  qed
qed

lemma comma_prefix_tree_select_refines_find:
  assumes cover: "comma_prefix_tree_covers P 0 N tree"
    and monotone: "mono P" and lower: "P 0\<le>row" and upper: "row<P N"
  shows "List.find (\<lambda>k. row<P (Suc k)) [0..<N]=
    Some (comma_prefix_tree_select row tree)"
proof -
  let ?k = "comma_prefix_tree_select row tree"
  have selected: "?k<N" "P ?k\<le>row" "row<P (Suc ?k)"
    using comma_prefix_tree_select_interval[OF assms] by blast+
  have earlier: "\<forall>j<?k. \<not>(row<P (Suc j))"
  proof (intro allI impI)
    fix j assume "j<?k"
    then have "Suc j\<le>?k" by simp
    then have "P (Suc j)\<le>P ?k" by (rule monoD[OF monotone])
    then show "\<not>(row<P (Suc j))" using selected(2) by arith
  qed
  show ?thesis using selected earlier
    by (auto simp only: find_Some_iff length_upt diff_zero nth_upt add_0_left)
qed

lemma comma_port_weighted_prefix_monotone:
  "mono (\<lambda>n. snd (comma_port_weighted_trace f d n))"
proof (simp only: mono_iff_le_Suc; intro allI)
  fix n
  show "snd (comma_port_weighted_trace f d n)\<le>
    snd (comma_port_weighted_trace f d (Suc n))"
    by (cases "comma_port_weighted_trace f d n") (simp add: Let_def)
qed

definition comma_port_tree_locator ::
  "nat \<Rightarrow> nat \<Rightarrow> comma_prefix_search_tree \<Rightarrow> nat \<Rightarrow> nat option" where
  "comma_port_tree_locator f d tree row=
    (if row<comma_finite_period f d div 10
      then Some (comma_prefix_tree_select row tree) else None)"

lemma comma_port_tree_locator_refines:
  assumes sector: "1\<le>f" "f\<le>9" and digit: "1\<le>d" "d\<le>9"
    and cover: "comma_prefix_tree_covers
      (\<lambda>n. snd (comma_port_weighted_trace f d n))
      0 (comma_port_cycle_length f d) tree"
  shows "comma_port_tree_locator f d tree row=comma_port_weighted_locator f d row"
proof -
  let ?P = "\<lambda>n. snd (comma_port_weighted_trace f d n)"
  let ?N = "comma_port_cycle_length f d"
  let ?W = "comma_finite_period f d div 10"
  have cycle: "?P ?N=?W"
    using comma_port_weighted_cycle[OF sector digit] by simp
  have monotone: "mono ?P" by (rule comma_port_weighted_prefix_monotone)
  show ?thesis
  proof (cases "row<?W")
    case True
    have bound: "row<?P ?N" using cycle True by simp
    have find: "List.find (\<lambda>k. row<?P (Suc k)) [0..<?N]=
      Some (comma_prefix_tree_select row tree)"
      by (rule comma_prefix_tree_select_refines_find[OF cover monotone _ bound]) simp
    show ?thesis by (simp only: comma_port_tree_locator_def True if_True
      comma_port_weighted_locator_def find)
  next
    case False
    have no_hit: "\<forall>k\<in>set [0..<?N]. \<not>(row<?P (Suc k))"
    proof (intro ballI)
      fix k assume "k\<in>set [0..<?N]"
      then have "Suc k\<le>?N" by simp
      then have "?P (Suc k)\<le>?P ?N" by (rule monoD[OF monotone])
      then show "\<not>(row<?P (Suc k))" using cycle False by arith
    qed
    have find: "List.find (\<lambda>k. row<?P (Suc k)) [0..<?N]=None"
      using no_hit by (simp only: find_None_iff; blast)
    show ?thesis by (simp only: comma_port_tree_locator_def False if_False
      comma_port_weighted_locator_def find)
  qed
qed

lemma comma_port_tree_locator_bounds:
  assumes sector: "1\<le>f" "f\<le>9" and digit: "1\<le>d" "d\<le>9"
    and cover: "comma_prefix_tree_covers
      (\<lambda>n. snd (comma_port_weighted_trace f d n))
      0 (comma_port_cycle_length f d) tree"
    and row: "row<comma_finite_period f d div 10"
  shows "\<exists>k<comma_port_cycle_length f d.
    comma_port_tree_locator f d tree row=Some k \<and>
    snd (comma_port_weighted_trace f d k)\<le>row \<and>
    row<snd (comma_port_weighted_trace f d (Suc k))"
proof -
  have cycle: "snd (comma_port_weighted_trace f d (comma_port_cycle_length f d))=
    comma_finite_period f d div 10"
    using comma_port_weighted_cycle[OF sector digit] by simp
  have bounds: "comma_prefix_tree_select row tree<comma_port_cycle_length f d \<and>
    snd (comma_port_weighted_trace f d (comma_prefix_tree_select row tree))\<le>row \<and>
    row<snd (comma_port_weighted_trace f d (Suc (comma_prefix_tree_select row tree)))"
    using comma_prefix_tree_select_interval[OF cover comma_port_weighted_prefix_monotone,
      of row] row cycle by simp
  show ?thesis using bounds row by (auto simp: comma_port_tree_locator_def)
qed

text \<open>The source theorem preserves the existing exact Entry anchor and
its physical headroom. A tree certificate changes finite comparison order;
it neither identifies weighted sectors nor creates successor authority.\<close>

definition comma_entry_tree_refined_locator ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> comma_prefix_search_tree \<Rightarrow>
    (nat\<times>nat\<times>nat) option" where
  "comma_entry_tree_refined_locator f d eta tree=
    (let seed=comma_entry_port_seed f d; row=comma_entry_port_row f d eta in
      map_option (\<lambda>k. let state=comma_port_action_power f k (seed,0);
        active=fst state; residual=row-snd state in
        (active,residual,
          10*active+f+(if f<9 then 1 else 0)-(comma_port_low f active+10*residual)))
      (comma_port_tree_locator f seed tree row))"

lemma comma_entry_tree_refined_locator_eq:
  assumes sector: "1\<le>f" "f\<le>9" and digit: "d<10"
    and cover: "comma_prefix_tree_covers
      (\<lambda>n. snd (comma_port_weighted_trace f (comma_entry_port_seed f d) n))
      0 (comma_port_cycle_length f (comma_entry_port_seed f d)) tree"
  shows "comma_entry_tree_refined_locator f d eta tree=
    comma_entry_port_refined_locator f d eta"
proof -
  have law: "comma_entry_port_anchor_law f d"
    by (rule comma_entry_port_anchor_law[OF sector digit])
  have seed: "1\<le>comma_entry_port_seed f d" "comma_entry_port_seed f d\<le>9"
    using law by (auto simp: comma_entry_port_anchor_law_def)
  have locator: "comma_port_tree_locator f (comma_entry_port_seed f d) tree
    (comma_entry_port_row f d eta)=comma_port_action_locator f
      (comma_entry_port_seed f d) (comma_entry_port_row f d eta)"
    by (rule comma_port_tree_locator_refines[OF sector seed cover])
  show ?thesis by (simp only: comma_entry_tree_refined_locator_def
    comma_entry_port_refined_locator_def Let_def locator)
qed

theorem comma_entry_tree_locator_refines_source:
  assumes sector: "1\<le>f" "f\<le>9" and offset: "x\<le>98"
    and key: "comma_entry_diagonal_key f r delta x=(d,eta)"
    and cover: "comma_prefix_tree_covers
      (\<lambda>n. snd (comma_port_weighted_trace f (comma_entry_port_seed f d) n))
      0 (comma_port_cycle_length f (comma_entry_port_seed f d)) tree"
  shows "\<exists>active residual h.
    comma_entry_tree_refined_locator f d eta tree=Some (active,residual,h) \<and>
    1\<le>active \<and> active\<le>9 \<and>
    residual<comma_port_dwell f active \<and>
    comma_fast_sector_target r (Comma_Entry f delta x)=Comma_Near f delta h"
proof -
  have actual_digit: "d=x mod 10" using key
    by (simp add: comma_entry_diagonal_key_def prod_eq_iff)
  have digit: "d<10" using actual_digit by simp
  have locator: "comma_entry_tree_refined_locator f d eta tree=
    comma_entry_port_refined_locator f d eta"
    by (rule comma_entry_tree_refined_locator_eq[OF sector digit cover])
  show ?thesis using comma_entry_nine_action_locator_refines_source[OF sector offset key]
    by (simp only: locator)
qed

text \<open>Stored leaves carry the literal active digit and both prefix
weights. This independent predicate checks every payload against the existing
weighted action; a correct search index alone does not certify leaf data.\<close>

fun comma_port_tree_payloads ::
  "nat \<Rightarrow> nat \<Rightarrow> comma_prefix_search_tree \<Rightarrow> bool" where
  "comma_port_tree_payloads f d (Comma_Prefix_Leaf k digit lower upper)=
    (digit=fst (comma_port_weighted_trace f d k) \<and>
      lower=snd (comma_port_weighted_trace f d k) \<and>
      upper=snd (comma_port_weighted_trace f d (Suc k)))"
| "comma_port_tree_payloads f d (Comma_Prefix_Split m threshold left right)=
    (comma_port_tree_payloads f d left \<and> comma_port_tree_payloads f d right)"

fun comma_prefix_tree_port_select ::
  "nat \<Rightarrow> comma_prefix_search_tree \<Rightarrow> nat\<times>nat\<times>nat" where
  "comma_prefix_tree_port_select row (Comma_Prefix_Leaf k digit lower upper)=
    (digit,lower,upper)"
| "comma_prefix_tree_port_select row (Comma_Prefix_Split m threshold left right)=
    (if row<threshold then comma_prefix_tree_port_select row left
      else comma_prefix_tree_port_select row right)"

lemma comma_port_tree_payload_refines:
  assumes labels: "comma_port_tree_payloads f d tree"
  shows "comma_prefix_tree_port_select row tree=
    (fst (comma_port_weighted_trace f d (comma_prefix_tree_select row tree)),
     snd (comma_port_weighted_trace f d (comma_prefix_tree_select row tree)),
     snd (comma_port_weighted_trace f d (Suc (comma_prefix_tree_select row tree))))"
  using labels by (induction tree) (auto split: if_splits)

text \<open>The following seventeen static trees are executable comparison
orders only. Their split constants are checked below against the existing
weighted trace definitions. The nine weighted actions remain distinct; orbit
selection is occurrence data, including the zero-bearing and top boundary.\<close>

definition comma_entry_prefix_tree ::
  "nat \<Rightarrow> nat \<Rightarrow> comma_prefix_search_tree" where
  "comma_entry_prefix_tree f orbit=(
    if f=1 \<and> orbit=0 then
      (Comma_Prefix_Split 2 18
        (Comma_Prefix_Split 1 9
        (Comma_Prefix_Leaf 0 9 0 9) (Comma_Prefix_Leaf 1 8 9 18)) (Comma_Prefix_Split 4 31
        (Comma_Prefix_Split 3 25
        (Comma_Prefix_Leaf 2 7 18 25) (Comma_Prefix_Leaf 3 6 25 31)) (Comma_Prefix_Split 6 40
        (Comma_Prefix_Split 5 36
        (Comma_Prefix_Leaf 4 5 31 36) (Comma_Prefix_Leaf 5 4 36 40)) (Comma_Prefix_Split 7 43
        (Comma_Prefix_Leaf 6 3 40 43) (Comma_Prefix_Split 8 45
        (Comma_Prefix_Leaf 7 2 43 45) (Comma_Prefix_Leaf 8 1 45 46)))))) else
    if f=2 \<and> orbit=0 then
      (Comma_Prefix_Split 1 9
        (Comma_Prefix_Leaf 0 8 0 9) (Comma_Prefix_Split 2 15
        (Comma_Prefix_Leaf 1 6 9 15) (Comma_Prefix_Split 3 19
        (Comma_Prefix_Leaf 2 4 15 19) (Comma_Prefix_Leaf 3 2 19 21)))) else
    if f=2 \<and> orbit=1 then
      (Comma_Prefix_Split 1 9
        (Comma_Prefix_Leaf 0 9 0 9) (Comma_Prefix_Split 2 17
        (Comma_Prefix_Leaf 1 7 9 17) (Comma_Prefix_Split 3 22
        (Comma_Prefix_Leaf 2 5 17 22) (Comma_Prefix_Split 4 25
        (Comma_Prefix_Leaf 3 3 22 25) (Comma_Prefix_Leaf 4 1 25 26))))) else
    if f=3 \<and> orbit=0 then
      (Comma_Prefix_Split 4 22
        (Comma_Prefix_Split 3 13
        (Comma_Prefix_Split 1 8
        (Comma_Prefix_Leaf 0 7 0 8) (Comma_Prefix_Split 2 12
        (Comma_Prefix_Leaf 1 4 8 12) (Comma_Prefix_Leaf 2 1 12 13))) (Comma_Prefix_Leaf 3 8 13 22)) (Comma_Prefix_Split 7 38
        (Comma_Prefix_Split 6 29
        (Comma_Prefix_Split 5 27
        (Comma_Prefix_Leaf 4 5 22 27) (Comma_Prefix_Leaf 5 2 27 29)) (Comma_Prefix_Leaf 6 9 29 38)) (Comma_Prefix_Split 8 45
        (Comma_Prefix_Leaf 7 6 38 45) (Comma_Prefix_Leaf 8 3 45 48)))) else
    if f=4 \<and> orbit=0 then
      (Comma_Prefix_Split 2 9
        (Comma_Prefix_Split 1 7
        (Comma_Prefix_Leaf 0 6 0 7) (Comma_Prefix_Leaf 1 2 7 9)) (Comma_Prefix_Split 3 18
        (Comma_Prefix_Leaf 2 8 9 18) (Comma_Prefix_Leaf 3 4 18 22))) else
    if f=4 \<and> orbit=1 then
      (Comma_Prefix_Split 2 11
        (Comma_Prefix_Split 1 8
        (Comma_Prefix_Leaf 0 7 0 8) (Comma_Prefix_Leaf 1 3 8 11)) (Comma_Prefix_Split 3 20
        (Comma_Prefix_Leaf 2 9 11 20) (Comma_Prefix_Split 4 26
        (Comma_Prefix_Leaf 3 5 20 26) (Comma_Prefix_Leaf 4 1 26 27)))) else
    if f=5 \<and> orbit=0 then
      (Comma_Prefix_Leaf 0 5 0 6) else
    if f=5 \<and> orbit=1 then
      (Comma_Prefix_Split 1 7
        (Comma_Prefix_Leaf 0 6 0 7) (Comma_Prefix_Leaf 1 1 7 8)) else
    if f=5 \<and> orbit=2 then
      (Comma_Prefix_Split 1 8
        (Comma_Prefix_Leaf 0 7 0 8) (Comma_Prefix_Leaf 1 2 8 10)) else
    if f=5 \<and> orbit=3 then
      (Comma_Prefix_Split 1 9
        (Comma_Prefix_Leaf 0 8 0 9) (Comma_Prefix_Leaf 1 3 9 12)) else
    if f=5 \<and> orbit=4 then
      (Comma_Prefix_Split 1 9
        (Comma_Prefix_Leaf 0 9 0 9) (Comma_Prefix_Leaf 1 4 9 14)) else
    if f=6 \<and> orbit=0 then
      (Comma_Prefix_Split 2 14
        (Comma_Prefix_Split 1 5
        (Comma_Prefix_Leaf 0 4 0 5) (Comma_Prefix_Leaf 1 8 5 14)) (Comma_Prefix_Split 3 16
        (Comma_Prefix_Leaf 2 2 14 16) (Comma_Prefix_Leaf 3 6 16 23))) else
    if f=6 \<and> orbit=1 then
      (Comma_Prefix_Split 2 15
        (Comma_Prefix_Split 1 6
        (Comma_Prefix_Leaf 0 5 0 6) (Comma_Prefix_Leaf 1 9 6 15)) (Comma_Prefix_Split 3 19
        (Comma_Prefix_Leaf 2 3 15 19) (Comma_Prefix_Split 4 27
        (Comma_Prefix_Leaf 3 7 19 27) (Comma_Prefix_Leaf 4 1 27 28)))) else
    if f=7 \<and> orbit=0 then
      (Comma_Prefix_Split 3 20
        (Comma_Prefix_Split 2 11
        (Comma_Prefix_Split 1 4
        (Comma_Prefix_Leaf 0 3 0 4) (Comma_Prefix_Leaf 1 6 4 11)) (Comma_Prefix_Leaf 2 9 11 20)) (Comma_Prefix_Split 6 38
        (Comma_Prefix_Split 5 29
        (Comma_Prefix_Split 4 23
        (Comma_Prefix_Leaf 3 2 20 23) (Comma_Prefix_Leaf 4 5 23 29)) (Comma_Prefix_Leaf 5 8 29 38)) (Comma_Prefix_Split 8 44
        (Comma_Prefix_Split 7 39
        (Comma_Prefix_Leaf 6 1 38 39) (Comma_Prefix_Leaf 7 4 39 44)) (Comma_Prefix_Leaf 8 7 44 52)))) else
    if f=8 \<and> orbit=0 then
      (Comma_Prefix_Split 3 15
        (Comma_Prefix_Split 2 8
        (Comma_Prefix_Split 1 3
        (Comma_Prefix_Leaf 0 2 0 3) (Comma_Prefix_Leaf 1 4 3 8)) (Comma_Prefix_Leaf 2 6 8 15)) (Comma_Prefix_Leaf 3 8 15 24)) else
    if f=8 \<and> orbit=1 then
      (Comma_Prefix_Split 3 18
        (Comma_Prefix_Split 2 10
        (Comma_Prefix_Split 1 4
        (Comma_Prefix_Leaf 0 3 0 4) (Comma_Prefix_Leaf 1 5 4 10)) (Comma_Prefix_Leaf 2 7 10 18)) (Comma_Prefix_Split 4 27
        (Comma_Prefix_Leaf 3 9 18 27) (Comma_Prefix_Leaf 4 1 27 29))) else
    if f=9 \<and> orbit=0 then
      (Comma_Prefix_Split 6 27
        (Comma_Prefix_Split 4 14
        (Comma_Prefix_Split 2 5
        (Comma_Prefix_Split 1 2
        (Comma_Prefix_Leaf 0 1 0 2) (Comma_Prefix_Leaf 1 2 2 5)) (Comma_Prefix_Split 3 9
        (Comma_Prefix_Leaf 2 3 5 9) (Comma_Prefix_Leaf 3 4 9 14))) (Comma_Prefix_Split 5 20
        (Comma_Prefix_Leaf 4 5 14 20) (Comma_Prefix_Leaf 5 6 20 27))) (Comma_Prefix_Split 8 44
        (Comma_Prefix_Split 7 35
        (Comma_Prefix_Leaf 6 7 27 35) (Comma_Prefix_Leaf 7 8 35 44)) (Comma_Prefix_Leaf 8 9 44 54))) else
    Comma_Prefix_Leaf 0 0 0 0)"

definition comma_entry_port_search_tree ::
  "nat \<Rightarrow> nat \<Rightarrow> comma_prefix_search_tree" where
  "comma_entry_port_search_tree f d=
    comma_entry_prefix_tree f (comma_entry_port_orbit f d)"

lemma comma_entry_port_search_trees_checked:
  "list_all (\<lambda>f. list_all (\<lambda>d.
    comma_prefix_tree_covers
      (\<lambda>n. snd (comma_port_weighted_trace f (comma_entry_port_seed f d) n))
      0 (comma_port_cycle_length f (comma_entry_port_seed f d))
      (comma_entry_port_search_tree f d) \<and>
    comma_port_tree_payloads f (comma_entry_port_seed f d)
      (comma_entry_port_search_tree f d)) [0..<10]) [1..<10]"
  by (tactic \<open>
    let
      val ctxt = @{context}
      val arithmetic = Comma_Entry_Arithmetic.natural_context ctxt
      val (certify, _) = Comma_Entry_Arithmetic.make_certifier ctxt
      fun number n = HOLogic.mk_number @{typ nat} n
      fun closed_value th = #2 (HOLogic.dest_number (Thm.term_of (Thm.rhs_of th)))
      val seed_context = arithmetic addsimps
        @{thms comma_entry_port_seed_def comma_entry_port_orbit_def
          comma_compiled_cycle_length_facts}
      fun seed f d = certify (Simplifier.rewrite seed_context
        (Thm.cterm_of ctxt (@{term comma_entry_port_seed} $ number f $ number d)))
      val seeds = maps (fn f => map (fn d => seed f d) (0 upto 9)) (1 upto 9)
      val ports = sort_distinct (prod_ord int_ord int_ord)
        (maps (fn f => map (fn d => (f, closed_value (seed f d))) (0 upto 9)) (1 upto 9))
      val _ = if length ports=17 then () else error "Entry tree lost its seventeen orbit seeds"
      val recurrence = map (Simplifier.simplify arithmetic)
        @{thms comma_port_weighted_trace.simps(2)[where n=0]
          comma_port_weighted_trace.simps(2)[where n=1]
          comma_port_weighted_trace.simps(2)[where n=2]
          comma_port_weighted_trace.simps(2)[where n=3]
          comma_port_weighted_trace.simps(2)[where n=4]
          comma_port_weighted_trace.simps(2)[where n=5]
          comma_port_weighted_trace.simps(2)[where n=6]
          comma_port_weighted_trace.simps(2)[where n=7]
          comma_port_weighted_trace.simps(2)[where n=8]}
      val step_context = arithmetic addsimps
        @{thms comma_port_next_def comma_port_previous_def comma_port_dwell_def}
      fun trace_term f d n =
        @{term comma_port_weighted_trace} $ number f $ number d $ number n
      fun check_pair th =
        let
          val (digit, weight) = HOLogic.dest_prod (Thm.term_of (Thm.rhs_of th))
          val _ = HOLogic.dest_number digit
          val _ = HOLogic.dest_number weight
        in certify th end
      fun traces (f,d) =
        let
          val zero = check_pair (Simplifier.rewrite
            (arithmetic addsimps @{thms comma_port_weighted_trace.simps(1)})
            (Thm.cterm_of ctxt (trace_term f d 0)))
          fun successor n previous = check_pair (Simplifier.rewrite
            (step_context addsimps [previous, nth recurrence (n-1)])
            (Thm.cterm_of ctxt (trace_term f d n)))
          val (_, backwards) = fold (fn n => fn (previous, facts) =>
            let val next=successor n previous in (next,next::facts) end)
            (1 upto 9) (zero,[zero])
        in rev backwards end
      val facts = maps traces ports
    in simp_tac (arithmetic addsimps seeds addsimps facts addsimps
      @{thms list_all_Nil_iff list_all_Cons_iff upt_rec
        comma_entry_prefix_tree_def comma_entry_port_search_tree_def
        comma_entry_port_orbit_def comma_port_cycle_length_def
        comma_prefix_tree_covers.simps comma_port_tree_payloads.simps
        comma_compiled_cycle_length_facts}) 1 end
    \<close>)

lemma comma_entry_port_search_tree_covers:
  assumes sector: "1\<le>f" "f\<le>9" and digit: "d<10"
  shows "comma_prefix_tree_covers
    (\<lambda>n. snd (comma_port_weighted_trace f (comma_entry_port_seed f d) n))
    0 (comma_port_cycle_length f (comma_entry_port_seed f d))
    (comma_entry_port_search_tree f d)"
  using comma_entry_port_search_trees_checked assms
  by (auto simp: list_all_iff)

lemma comma_entry_port_search_tree_payloads:
  assumes sector: "1\<le>f" "f\<le>9" and digit: "d<10"
  shows "comma_port_tree_payloads f (comma_entry_port_seed f d)
    (comma_entry_port_search_tree f d)"
  using comma_entry_port_search_trees_checked assms
  by (auto simp: list_all_iff)

lemma comma_entry_static_tree_locator_bounds:
  assumes sector: "1\<le>f" "f\<le>9" and digit: "d<10"
  shows "\<exists>k<comma_port_cycle_length f (comma_entry_port_seed f d).
    comma_port_tree_locator f (comma_entry_port_seed f d)
      (comma_entry_port_search_tree f d) (comma_entry_port_row f d eta)=Some k \<and>
    snd (comma_port_weighted_trace f (comma_entry_port_seed f d) k)\<le>
      comma_entry_port_row f d eta \<and>
    comma_entry_port_row f d eta<
      snd (comma_port_weighted_trace f (comma_entry_port_seed f d) (Suc k))"
proof -
  have law: "comma_entry_port_anchor_law f d"
    by (rule comma_entry_port_anchor_law[OF sector digit])
  have seed: "1\<le>comma_entry_port_seed f d" "comma_entry_port_seed f d\<le>9"
    using law by (auto simp: comma_entry_port_anchor_law_def)
  show ?thesis
    by (rule comma_port_tree_locator_bounds[OF sector seed
      comma_entry_port_search_tree_covers[OF sector digit]
      comma_entry_port_row_bound[OF sector digit]])
qed

theorem comma_entry_static_tree_locator_refines_source:
  assumes sector: "1\<le>f" "f\<le>9" and offset: "x\<le>98"
    and key: "comma_entry_diagonal_key f r delta x=(d,eta)"
  shows "\<exists>active residual h.
    comma_entry_tree_refined_locator f d eta (comma_entry_port_search_tree f d)=
      Some (active,residual,h) \<and>
    1\<le>active \<and> active\<le>9 \<and>
    residual<comma_port_dwell f active \<and>
    comma_fast_sector_target r (Comma_Entry f delta x)=Comma_Near f delta h"
proof -
  have actual_digit: "d=x mod 10" using key
    by (simp add: comma_entry_diagonal_key_def prod_eq_iff)
  have digit: "d<10" using actual_digit by simp
  show ?thesis
    by (rule comma_entry_tree_locator_refines_source[OF sector offset key
      comma_entry_port_search_tree_covers[OF sector digit]])
qed

text \<open>This executable consumer reads only the stored leaf payload.
The trace owner appears solely in the refinement proof, not its definition.\<close>

definition comma_entry_stored_tree_locator ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat\<times>nat\<times>nat) option" where
  "comma_entry_stored_tree_locator f d eta=
    (let seed=comma_entry_port_seed f d; row=comma_entry_port_row f d eta;
      tree=comma_entry_port_search_tree f d in
      if row<comma_finite_period f seed div 10 then
        (let (active,lower,upper)=comma_prefix_tree_port_select row tree;
          residual=row-lower in
          Some (active,residual,
            10*active+f+(if f<9 then 1 else 0)-
              (comma_port_low f active+10*residual)))
      else None)"

lemma comma_entry_stored_tree_locator_refines:
  assumes sector: "1\<le>f" "f\<le>9" and digit: "d<10"
  shows "comma_entry_stored_tree_locator f d eta=
    comma_entry_port_refined_locator f d eta"
proof -
  let ?seed = "comma_entry_port_seed f d"
  let ?row = "comma_entry_port_row f d eta"
  let ?tree = "comma_entry_port_search_tree f d"
  let ?k = "comma_prefix_tree_select ?row ?tree"
  have row: "?row<comma_finite_period f ?seed div 10"
    by (rule comma_entry_port_row_bound[OF sector digit])
  have labels: "comma_port_tree_payloads f ?seed ?tree"
    by (rule comma_entry_port_search_tree_payloads[OF sector digit])
  have payload: "comma_prefix_tree_port_select ?row ?tree=
    (fst (comma_port_weighted_trace f ?seed ?k),
     snd (comma_port_weighted_trace f ?seed ?k),
     snd (comma_port_weighted_trace f ?seed (Suc ?k)))"
    by (rule comma_port_tree_payload_refines[OF labels])
  have index: "comma_port_tree_locator f ?seed ?tree ?row=Some ?k"
    by (simp only: comma_port_tree_locator_def row if_True)
  have stored: "comma_entry_stored_tree_locator f d eta=
    comma_entry_tree_refined_locator f d eta ?tree"
    by (simp only: comma_entry_stored_tree_locator_def
      comma_entry_tree_refined_locator_def Let_def row if_True payload index
      comma_port_action_power_trace option.map;
      cases "comma_port_weighted_trace f ?seed ?k"; simp)
  show ?thesis using stored
    comma_entry_tree_refined_locator_eq[OF sector digit
      comma_entry_port_search_tree_covers[OF sector digit], of eta]
    by simp
qed

theorem comma_entry_stored_tree_locator_refines_source:
  assumes sector: "1\<le>f" "f\<le>9" and offset: "x\<le>98"
    and key: "comma_entry_diagonal_key f r delta x=(d,eta)"
  shows "\<exists>active residual h.
    comma_entry_stored_tree_locator f d eta=Some (active,residual,h) \<and>
    1\<le>active \<and> active\<le>9 \<and>
    residual<comma_port_dwell f active \<and>
    comma_fast_sector_target r (Comma_Entry f delta x)=Comma_Near f delta h"
proof -
  have actual_digit: "d=x mod 10" using key
    by (simp add: comma_entry_diagonal_key_def prod_eq_iff)
  have digit: "d<10" using actual_digit by simp
  show ?thesis using comma_entry_nine_action_locator_refines_source[OF sector offset key]
    by (simp only: comma_entry_stored_tree_locator_refines[OF sector digit])
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_port_action_power_trace comma_port_action_locator_refines
      comma_entry_port_refined_locator_headroom comma_entry_port_refined_locator_exact
      comma_entry_nine_action_locator_refines_source
      comma_entry_reduced_key_locator_refines_source
      comma_prefix_tree_select_interval comma_prefix_tree_select_refines_find
      comma_port_weighted_prefix_monotone comma_port_tree_locator_refines
      comma_port_tree_locator_bounds comma_entry_tree_refined_locator_eq
      comma_entry_tree_locator_refines_source
      comma_entry_port_search_trees_checked comma_entry_port_search_tree_covers
      comma_entry_static_tree_locator_bounds
      comma_entry_static_tree_locator_refines_source
      comma_port_tree_payload_refines comma_entry_port_search_tree_payloads
      comma_entry_stored_tree_locator_refines
      comma_entry_stored_tree_locator_refines_source}) then ()
    else error "Comma Entry action locator refinement depends on an oracle";
\<close>
end
