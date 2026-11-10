theory Comma_Entry_Port_Anchor
  imports Comma_Vieta_Root.Comma_Root_Pair_Port
begin

text \<open>The orbit potential below is signed. It transports the actual
Frobenius Entry diagonal to the canonical punctured orbit, without treating a
diagonal dwell as physical time. The selected weighted row is connected below
to the physical Near germ; neither rank nor fuel is an admission premise here.\<close>

definition comma_entry_port_orbit :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_entry_port_orbit f d=d mod (10 div comma_cycle_length f)"

definition comma_entry_port_seed :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_entry_port_seed f d=10-f+comma_entry_port_orbit f d"

definition comma_entry_port_position :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_entry_port_position f d=the (List.find
    (\<lambda>j. comma_phase_digit f (comma_entry_port_orbit f d) j=d)
    [0..<comma_cycle_length f])"

definition comma_entry_port_potential :: "nat \<Rightarrow> nat \<Rightarrow> int" where
  "comma_entry_port_potential f d=(
    int (comma_period_displacement f (comma_entry_port_orbit f d)
      (comma_entry_port_position f d)) -
    (int d-int (comma_entry_port_orbit f d))) div 10"

definition comma_entry_port_anchor_law :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "comma_entry_port_anchor_law f d=(
    2\<le>comma_cycle_length f \<and> comma_entry_port_orbit f d<10 \<and>
    comma_entry_port_position f d<comma_cycle_length f \<and>
    comma_phase_digit f (comma_entry_port_orbit f d)
      (comma_entry_port_position f d)=d \<and>
    1\<le>comma_entry_port_seed f d \<and> comma_entry_port_seed f d\<le>9 \<and>
    comma_finite_period f (comma_entry_port_seed f d)=comma_finite_period f d \<and>
    comma_finite_period f (comma_entry_port_orbit f d)=comma_finite_period f d \<and>
    comma_phase_digit f (comma_entry_port_orbit f d) (comma_cycle_length f-1)=
      comma_entry_port_seed f d \<and>
    comma_vieta_guard_root (if f<9 then 1 else 0) (comma_finite_period f d div 10)
      f (comma_entry_port_orbit f d) (comma_cycle_length f-1)+
      int (comma_port_low f (comma_entry_port_seed f d))=0 \<and>
    int (comma_period_displacement f (comma_entry_port_orbit f d)
      (comma_entry_port_position f d))=
      10*comma_entry_port_potential f d+int d-int (comma_entry_port_orbit f d))"

lemma comma_entry_port_displacement_zero:
  "comma_period_displacement f d 0=0"
  by (simp add: comma_period_displacement_def)

lemma comma_entry_port_anchor_laws_checked:
  "list_all (\<lambda>f. list_all (comma_entry_port_anchor_law f)
    [0..<10]) [1..<10]"
  by (tactic \<open>
    let
      val arithmetic = Comma_Entry_Arithmetic.natural_context @{context}
      val recurrence = map (Simplifier.simplify arithmetic)
        @{thms comma_period_displacement_succ[where j=0]
          comma_period_displacement_succ[where j=1]
          comma_period_displacement_succ[where j=2]
          comma_period_displacement_succ[where j=3]
          comma_period_displacement_succ[where j=4]
          comma_period_displacement_succ[where j=5]
          comma_period_displacement_succ[where j=6]
          comma_period_displacement_succ[where j=7]
          comma_period_displacement_succ[where j=8]}
    in simp_tac (arithmetic |> Simplifier.add_simps recurrence |> Simplifier.add_simps
      @{thms list_all_Nil_iff list_all_Cons_iff upt_rec
        comma_entry_port_anchor_law_def comma_entry_port_orbit_def
        comma_entry_port_seed_def comma_entry_port_position_def
        comma_entry_port_potential_def comma_phase_digit_def
        comma_entry_port_displacement_zero List.find.simps option.sel
        of_nat_numeral of_nat_0 of_nat_1
        comma_vieta_guard_root_def comma_vieta_root_def comma_port_low_def
        comma_compiled_cycle_length_facts comma_compiled_period_facts}) 1 end
    \<close>)

lemma comma_entry_port_anchor_law:
  assumes "1\<le>f" "f\<le>9" "d<10"
  shows "comma_entry_port_anchor_law f d"
  using comma_entry_port_anchor_laws_checked assms
  by (auto simp: list_all_iff)

definition comma_entry_port_row :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_entry_port_row f d eta=nat ((int eta-comma_entry_port_potential f d)
    mod int (comma_finite_period f d div 10))"

definition comma_port_conjugate_headroom ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_port_conjugate_headroom f P orbit row displacement=
    (let b=1+(if f<9 then 1 else 0)
     in b+nat ((-10*int row-(int orbit+int b)-int displacement) mod int P))"

lemma comma_entry_port_headroom_conjugacy:
  assumes sector: "1\<le>f" "f\<le>9" and digit: "d<10"
  shows "comma_diagonal_headroom f (comma_finite_period f d) d eta =
    comma_port_conjugate_headroom f (comma_finite_period f d)
      (comma_entry_port_orbit f d) (comma_entry_port_row f d eta)
      (comma_period_displacement f (comma_entry_port_orbit f d)
        (comma_entry_port_position f d))"
proof -
  let ?P = "comma_finite_period f d"
  let ?M = "?P div 10"
  let ?o = "comma_entry_port_orbit f d"
  let ?D = "comma_period_displacement f ?o (comma_entry_port_position f d)"
  let ?psi = "comma_entry_port_potential f d"
  let ?a = "int eta-?psi"
  let ?b = "1+(if f<9 then 1 else 0)"
  have law: "comma_entry_port_anchor_law f d"
    by (rule comma_entry_port_anchor_law[OF sector digit])
  have displacement: "int ?D=10*?psi+int d-int ?o"
    using law by (simp add: comma_entry_port_anchor_law_def)
  have catalog: "?P\<in>comma_cycle_displacements"
    using comma_finite_period_in_catalog[rule_format, of f d] sector digit by auto
  have positive: "0<?M" and decimal: "10 dvd ?P"
    using comma_entry_period_decimal[OF catalog] by blast+
  have period: "?P=10*?M" using decimal by (simp add: dvd_mult_div_cancel)
  have modulus: "int ?P=10*int ?M"
    using arg_cong[OF period, of int] by (simp only: of_nat_mult of_nat_numeral)
  have row: "int (comma_entry_port_row f d eta)=?a mod int ?M"
    using positive by (simp add: comma_entry_port_row_def)
  have equation: "-10*int eta-(int d+int ?b)=
    -10*?a-(int ?o+int ?b+int ?D)"
    using displacement by (simp add: algebra_simps; linarith)
  have normalized: "(-10*int eta-(int d+int ?b)) mod int ?P=
    (-10*int (comma_entry_port_row f d eta)-(int ?o+int ?b)-int ?D) mod int ?P"
    using comma_signed_diagonal_remainder[of ?a "int ?o+int ?D" "int ?b" "int ?M"]
    by (simp only: equation modulus row; simp add: algebra_simps)
  show ?thesis by (simp only: comma_diagonal_headroom_def
    comma_port_conjugate_headroom_def Let_def normalized)
qed

lemma comma_entry_port_row_bound:
  assumes sector: "1\<le>f" "f\<le>9" and digit: "d<10"
  shows "comma_entry_port_row f d eta<
    comma_finite_period f (comma_entry_port_seed f d) div 10"
proof -
  have catalog: "comma_finite_period f d\<in>comma_cycle_displacements"
    using comma_finite_period_in_catalog[rule_format, of f d] sector digit by auto
  have positive: "0<comma_finite_period f d div 10"
    using comma_entry_period_decimal[OF catalog] by blast
  have law: "comma_entry_port_anchor_law f d"
    by (rule comma_entry_port_anchor_law[OF sector digit])
  show ?thesis using law positive
    by (simp add: comma_entry_port_anchor_law_def comma_entry_port_row_def nat_less_iff)
qed

lemma comma_port_trace_digit_admitted:
  assumes sector: "1\<le>f" "f\<le>9" and digit: "1\<le>d" "d\<le>9"
  shows "1\<le>fst (comma_port_weighted_trace f d n) \<and>
    fst (comma_port_weighted_trace f d n)\<le>9"
proof (induction n)
  case 0 then show ?case using digit by simp
next
  case (Suc n)
  have law: "comma_port_local_law f (fst (comma_port_weighted_trace f d n))"
    using comma_port_local_law[OF sector] Suc.IH by blast
  obtain current weight where pair:
    "comma_port_weighted_trace f d n=(current,weight)" by (cases "comma_port_weighted_trace f d n") auto
  show ?case using law by (simp add: pair Let_def comma_port_local_law_def)
qed

lemma comma_entry_port_locator_admitted:
  fixes eta :: nat
  assumes sector: "1\<le>f" "f\<le>9" and digit: "d<10"
  defines "seed \<equiv> comma_entry_port_seed f d"
    and "row \<equiv> comma_entry_port_row f d eta"
  shows "\<exists>k<9. comma_port_weighted_locator f seed row=Some k \<and>
    1\<le>fst (comma_port_weighted_trace f seed k) \<and>
    fst (comma_port_weighted_trace f seed k)\<le>9 \<and>
    row-snd (comma_port_weighted_trace f seed k)<
      comma_port_dwell f (fst (comma_port_weighted_trace f seed k))"
proof -
  have law: "comma_entry_port_anchor_law f d"
    by (rule comma_entry_port_anchor_law[OF sector digit])
  have seed: "1\<le>seed" "seed\<le>9"
    using law by (auto simp: seed_def comma_entry_port_anchor_law_def)
  have bound: "row<comma_finite_period f seed div 10"
    using comma_entry_port_row_bound[OF sector digit, of eta]
    by (simp add: seed_def row_def)
  obtain k where locator: "k<9" "comma_port_weighted_locator f seed row=Some k"
    and lower: "snd (comma_port_weighted_trace f seed k)\<le>row"
    and upper: "row<snd (comma_port_weighted_trace f seed (Suc k))"
    using comma_port_weighted_locator_coverage[OF sector seed bound] by blast
  have trace_successor: "snd (comma_port_weighted_trace f seed (Suc k))=
    snd (comma_port_weighted_trace f seed k)+
      comma_port_dwell f (fst (comma_port_weighted_trace f seed k))"
    by (cases "comma_port_weighted_trace f seed k") (simp add: Let_def)
  have residual: "row-snd (comma_port_weighted_trace f seed k)<
    comma_port_dwell f (fst (comma_port_weighted_trace f seed k))"
    using lower upper trace_successor by arith
  show ?thesis using locator residual comma_port_trace_digit_admitted[OF sector seed, of k]
    by blast
qed

lemma comma_entry_phase_shift:
  assumes phase: "d=comma_phase_digit f orbit j"
  shows "comma_phase_digit f orbit (j+n)=comma_phase_digit f d n"
proof -
  have source: "d=(orbit+j*f) mod 10" using phase by (simp add: comma_phase_digit_def)
  have expanded: "orbit+(j+n)*f=(orbit+j*f)+n*f" by (simp add: algebra_simps)
  show ?thesis unfolding comma_phase_digit_def
    by (simp only: source expanded mod_add_left_eq)
qed

lemma comma_entry_displacement_shift:
  assumes phase: "d=comma_phase_digit f orbit j"
  shows "comma_period_displacement f orbit (j+n)=
    comma_period_displacement f orbit j+comma_period_displacement f d n"
proof (induction n)
  case 0 then show ?case by (simp add: comma_period_displacement_def)
next
  case (Suc n)
  have digit: "comma_phase_digit f orbit (j+n)=comma_phase_digit f d n"
    by (rule comma_entry_phase_shift[OF phase])
  show ?case using Suc.IH digit
    by (simp add: comma_period_displacement_succ add.assoc)
qed

lemma comma_entry_guard_root_periodic:
  assumes sector: "1\<le>f" "f\<le>9" and digit: "orbit<10"
  shows "comma_vieta_guard_root e M f orbit (comma_cycle_length f+n)=
    comma_vieta_guard_root e M f orbit n-int (comma_finite_period f orbit)"
proof -
  have closes: "10 dvd comma_cycle_length f*f"
    by (rule comma_cycle_length_admitted(2)[OF sector])
  have phase: "comma_phase_digit f orbit (comma_cycle_length f+n)=
    comma_phase_digit f orbit n"
    by (rule comma_phase_digit_periodic[OF closes])
  have displacement: "comma_period_displacement f orbit (comma_cycle_length f+n)=
    comma_finite_period f orbit+comma_period_displacement f orbit n"
    using comma_period_displacement_shift[OF closes, of orbit n]
      comma_finite_period_refines[OF sector digit] by simp
  show ?thesis by (simp only: comma_vieta_guard_root_def comma_vieta_root_def
    phase displacement of_nat_add; linarith)
qed

lemma comma_entry_guard_root_phase_transport:
  assumes phase: "d=comma_phase_digit f orbit j"
  shows "comma_vieta_guard_root e M f orbit (j+n)=
    comma_vieta_guard_root e M f d n+int d-int orbit-
      int (comma_period_displacement f orbit j)"
  using comma_entry_phase_shift[OF phase, of n]
    comma_entry_displacement_shift[OF phase, of n]
  by (simp only: comma_vieta_guard_root_def comma_vieta_root_def
    comma_entry_phase_shift[OF phase] comma_entry_displacement_shift[OF phase]
    of_nat_add; linarith)

lemma comma_entry_guard_root_potential_transport:
  assumes sector: "1\<le>f" "f\<le>9" and digit: "d<10"
  shows "comma_vieta_guard_root e M f (comma_entry_port_orbit f d)
      (comma_entry_port_position f d+n)=
    comma_vieta_guard_root e M f d n-10*comma_entry_port_potential f d"
proof -
  have law: "comma_entry_port_anchor_law f d"
    by (rule comma_entry_port_anchor_law[OF sector digit])
  have phase: "d=comma_phase_digit f (comma_entry_port_orbit f d)
    (comma_entry_port_position f d)"
    and displacement: "int (comma_period_displacement f (comma_entry_port_orbit f d)
      (comma_entry_port_position f d))=
      10*comma_entry_port_potential f d+int d-int (comma_entry_port_orbit f d)"
    using law by (auto simp: comma_entry_port_anchor_law_def)
  show ?thesis using comma_entry_guard_root_phase_transport[OF phase, of e M n]
    displacement by linarith
qed

lemma comma_entry_port_seed_root:
  assumes sector: "1\<le>f" "f\<le>9" and digit: "d<10"
  shows "comma_phase_digit f (comma_entry_port_orbit f d) (comma_cycle_length f-1)=
      comma_entry_port_seed f d"
    "comma_vieta_guard_root (if f<9 then 1 else 0) (comma_finite_period f d div 10)
      f (comma_entry_port_orbit f d) (comma_cycle_length f-1)+
      int (comma_port_low f (comma_entry_port_seed f d))=0"
  using comma_entry_port_anchor_law[OF sector digit]
  by (auto simp: comma_entry_port_anchor_law_def)

lemma comma_entry_guard_root_repeated:
  assumes sector: "1\<le>f" "f\<le>9" and digit: "orbit<10"
  shows "comma_vieta_guard_root e M f orbit (t*comma_cycle_length f+n)=
    comma_vieta_guard_root e M f orbit n-int t*int (comma_finite_period f orbit)"
proof (induction t)
  case 0 then show ?case by simp
next
  case (Suc t)
  have index: "Suc t*comma_cycle_length f+n=
    comma_cycle_length f+(t*comma_cycle_length f+n)" by (simp add: algebra_simps)
  have step: "comma_vieta_guard_root e M f orbit (Suc t*comma_cycle_length f+n)=
    comma_vieta_guard_root e M f orbit (t*comma_cycle_length f+n)-
      int (comma_finite_period f orbit)"
    using comma_entry_guard_root_periodic[OF sector digit,
      of e M "t*comma_cycle_length f+n"] by (simp only: index)
  show ?case by (simp only: step Suc.IH; simp add: algebra_simps)
qed

lemma comma_entry_port_lifted_seed:
  assumes sector: "1\<le>f" "f\<le>9" and digit: "d<10"
  shows "comma_phase_digit f (comma_entry_port_orbit f d) (10*comma_cycle_length f-1)=
      comma_entry_port_seed f d"
    "comma_vieta_guard_root (if f<9 then 1 else 0) (comma_finite_period f d div 10)
      f (comma_entry_port_orbit f d) (10*comma_cycle_length f-1)+
      int (comma_port_low f (comma_entry_port_seed f d))=
        -9*int (comma_finite_period f d)"
proof -
  let ?L = "comma_cycle_length f"
  let ?o = "comma_entry_port_orbit f d"
  have positive: "0<?L" by (rule comma_cycle_length_admitted(1)[OF sector])
  have index: "10*?L-1=9*?L+(?L-1)" using positive by arith
  have closes: "10 dvd (9*?L)*f"
    using comma_cycle_length_admitted(2)[OF sector] by (simp add: mult.assoc)
  have law: "comma_entry_port_anchor_law f d"
    by (rule comma_entry_port_anchor_law[OF sector digit])
  have orbit: "?o<10" and period: "comma_finite_period f ?o=comma_finite_period f d"
    using law by (auto simp: comma_entry_port_anchor_law_def)
  show "comma_phase_digit f ?o (10*?L-1)=comma_entry_port_seed f d"
    using comma_phase_digit_periodic[OF closes, of ?o "?L-1"]
      comma_entry_port_seed_root(1)[OF sector digit]
    by (simp only: index)
  show "comma_vieta_guard_root (if f<9 then 1 else 0) (comma_finite_period f d div 10)
      f ?o (10*?L-1)+int (comma_port_low f (comma_entry_port_seed f d))=
      -9*int (comma_finite_period f d)"
    using comma_entry_guard_root_repeated[OF sector orbit,
      of "if f<9 then 1 else 0" "comma_finite_period f d div 10" 9 "?L-1"]
      comma_entry_port_seed_root(2)[OF sector digit]
    by (simp only: index period of_nat_numeral; linarith)
qed

text \<open>The crossing count is a proof measure, not a published port
coordinate. Lifting the ordered index avoids truncated subtraction while
accumulated dwell weights transport its exact root interval.\<close>

primrec comma_port_proof_crossings :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_port_proof_crossings f d 0=0"
| "comma_port_proof_crossings f d (Suc k)=comma_port_proof_crossings f d k+
    (if comma_port_previous f (fst (comma_port_weighted_trace f d k))=0 then 2 else 1)"

lemma comma_port_proof_crossings_bound:
  "comma_port_proof_crossings f d k\<le>2*k"
proof (induction k)
  case 0
  show ?case by (simp only: comma_port_proof_crossings.simps(1); simp)
next
  case (Suc k)
  let ?increment = "if comma_port_previous f (fst (comma_port_weighted_trace f d k))=0 then 2 else 1"
  have recurrence: "comma_port_proof_crossings f d (Suc k)=
    comma_port_proof_crossings f d k+?increment"
    by (rule comma_port_proof_crossings.simps(2))
  have increment_bound: "?increment\<le>(2::nat)" by (simp split: if_splits)
  have scale: "2*Suc k=2*k+2" by simp
  show ?case using Suc.IH recurrence increment_bound scale by linarith
qed

lemma comma_port_dwell_positive:
  assumes "1\<le>d" "d\<le>9"
  shows "0<comma_port_dwell f d"
  using assms by (auto simp: comma_port_dwell_def split: if_splits; arith)

lemma comma_port_weighted_root_transport:
  assumes sector: "1\<le>f" "f\<le>9" and digit: "1\<le>d" "d\<le>9"
    and phase: "d=comma_phase_digit f orbit n0"
    and lifted: "2*k+2\<le>n0"
  shows "fst (comma_port_weighted_trace f d k)=
      comma_phase_digit f orbit (n0-comma_port_proof_crossings f d k) \<and>
    comma_vieta_root M f orbit n0+int (comma_port_low f d)+
      10*int (snd (comma_port_weighted_trace f d k))=
      comma_vieta_root M f orbit (n0-comma_port_proof_crossings f d k)+
        int (comma_port_low f (fst (comma_port_weighted_trace f d k)))"
  using lifted
proof (induction k)
  case 0 then show ?case using phase
    by (simp add: comma_port_proof_crossings.simps comma_port_weighted_trace.simps)
next
  case (Suc k)
  let ?C = "comma_port_proof_crossings f d k"
  let ?n = "n0-?C"
  obtain current weight where pair: "comma_port_weighted_trace f d k=(current,weight)"
    by (cases "comma_port_weighted_trace f d k") auto
  let ?cross = "if comma_port_previous f current=0 then 2 else 1"
  have before_bound: "2*k+2\<le>n0" using Suc.prems by arith
  have prior_phase: "current=comma_phase_digit f orbit ?n"
    and prior_root: "comma_vieta_root M f orbit n0+int (comma_port_low f d)+10*int weight=
      comma_vieta_root M f orbit ?n+int (comma_port_low f current)"
    using Suc.IH[OF before_bound] by (simp_all add: pair)
  have current_digit: "1\<le>current" "current\<le>9"
    using comma_port_trace_digit_admitted[OF sector digit, of k] by (simp_all add: pair)
  have n_bound: "2\<le>?n"
    using comma_port_proof_crossings_bound[of f d k] Suc.prems by arith
  have index: "?n=Suc (Suc (?n-2))" using n_bound by arith
  have source_phase: "current=comma_phase_digit f orbit (Suc (Suc (?n-2)))"
    using prior_phase index by simp
  have admitted: "0<comma_port_dwell f current"
    by (rule comma_port_dwell_positive[OF current_digit])
  have pump: "comma_vieta_root M f orbit ?n+int (comma_port_low f current)+
      10*int (comma_port_dwell f current)=
      comma_vieta_root M f orbit (?n-?cross)+
        int (comma_port_low f (comma_port_next f current))"
    using comma_port_pump_refines_ordered_roots
      [OF sector current_digit source_phase,
        where u="comma_port_low f current" and m=0
          and q="comma_port_dwell f current" and M=M]
      admitted index by simp
  have first_index: "?n=Suc (?n-1)" using n_bound by arith
  have second_index: "?n-1=Suc (?n-2)" using n_bound by arith
  have previous: "comma_port_previous f current=comma_phase_digit f orbit (?n-1)"
    using comma_port_actual_previous[OF sector, of orbit "?n-1"]
      prior_phase first_index by simp
  have next_phase: "comma_port_next f current=comma_phase_digit f orbit (?n-?cross)"
  proof (cases "comma_port_previous f current=0")
    case False
    then show ?thesis using previous
      by (simp add: comma_port_next_def Let_def)
  next
    case True
    have second: "comma_port_previous f (comma_port_previous f current)=
      comma_phase_digit f orbit (?n-2)"
      using comma_port_actual_previous[OF sector, of orbit "?n-2"]
        previous second_index by simp
    show ?thesis using True second by (simp add: comma_port_next_def Let_def)
  qed
  have coordinate: "n0-comma_port_proof_crossings f d (Suc k)=?n-?cross"
    by (simp add: pair comma_port_proof_crossings.simps)
  show ?case using prior_root pump next_phase
    by (simp add: pair coordinate Let_def comma_port_weighted_trace.simps algebra_simps)
qed

lemma comma_entry_diagonal_chart:
  fixes eta P H :: nat
  assumes sector: "1\<le>f" "f\<le>9" and digit: "d<10"
  defines "P \<equiv> comma_finite_period f d"
    and "H \<equiv> comma_diagonal_headroom f P d eta"
  shows "(if f<9 then 1 else 0)<H" "H\<le>P+(if f<9 then 1 else 0)"
    "H\<le>540" "(H+d) mod 10=0"
proof -
  let ?b = "1+(if f<9 then 1 else 0)"
  let ?z = "-10*int eta-(int d+int ?b)"
  have catalog: "P\<in>comma_cycle_displacements"
    using comma_finite_period_in_catalog[rule_format, of f d] sector digit
    by (simp add: P_def)
  have positive: "0<P" and decimal: "10 dvd P"
    using comma_entry_period_decimal[OF catalog] by blast+
  have rem_nonnegative: "0\<le>?z mod int P" using positive by simp
  have rem_bound: "nat (?z mod int P)<P" using positive by (simp add: nat_less_iff)
  have cast: "int H=int ?b+?z mod int P"
    using rem_nonnegative by (simp add: H_def comma_diagonal_headroom_def Let_def)
  have expanded_H: "H=?b+nat (?z mod int P)"
    by (simp only: H_def comma_diagonal_headroom_def Let_def)
  show "(if f<9 then 1 else 0)<H" using expanded_H by arith
  have H_upper: "H\<le>P+(if f<9 then 1 else 0)"
    using expanded_H rem_bound by arith
  show "H\<le>P+(if f<9 then 1 else 0)" by (rule H_upper)
  have bound: "P+(if f<9 then 1 else 0)\<le>540"
    using comma_finite_period_guard_bound[OF sector digit]
    by (simp add: P_def comma_finite_guard_extra_def)
  show "H\<le>540" using bound H_upper by arith
  obtain quotient where decimal_witness: "P=10*quotient"
    using decimal by (auto simp: dvd_def)
  have int_witness: "int P=10*int quotient"
    using arg_cong[OF decimal_witness, of int] by (simp only: of_nat_mult of_nat_numeral)
  have divides: "(10::int) dvd int P" by (simp only: int_witness; simp)
  have lift: "(?z mod int P) mod 10=?z mod 10"
    by (rule mod_mod_cancel[OF divides])
  have alignment: "(int H+int d) mod 10=(int ?b+?z+int d) mod 10"
  proof -
    have "(int H+int d) mod 10=(?z mod int P+(int ?b+int d)) mod 10"
      by (simp only: cast; simp add: add.assoc add.commute add.left_commute)
    also have "...=((?z mod int P) mod 10+(int ?b+int d)) mod 10"
      by (rule mod_add_left_eq[symmetric])
    also have "...=(?z mod 10+(int ?b+int d)) mod 10"
      by (simp only: lift)
    also have "...=(?z+(int ?b+int d)) mod 10"
      by (rule mod_add_left_eq)
    also have "...=(int ?b+?z+int d) mod 10"
      by (simp add: add.assoc add.commute add.left_commute)
    finally show ?thesis .
  qed
  have cancel: "int ?b+?z+int d=-10*int eta" by (simp add: algebra_simps)
  have align: "(int H+int d) mod 10=0" by (simp only: alignment cancel; simp)
  have cast_mod: "int ((H+d) mod 10)=(int H+int d) mod 10"
    by (simp only: of_nat_mod of_nat_add of_nat_numeral)
  have "int ((H+d) mod 10)=0" using cast_mod align by arith
  then show "(H+d) mod 10=0" by simp
qed

lemma comma_entry_port_selected_physical:
  fixes eta L P seed row active m index j n u h H :: nat
  assumes sector: "1\<le>f" "f\<le>9" and digit: "d<10"
    and selected: "comma_port_weighted_locator f (comma_entry_port_seed f d)
      (comma_entry_port_row f d eta)=Some k"
  defines "L \<equiv> comma_cycle_length f"
    and "P \<equiv> comma_finite_period f d"
    and "seed \<equiv> comma_entry_port_seed f d"
    and "row \<equiv> comma_entry_port_row f d eta"
    and "active \<equiv> fst (comma_port_weighted_trace f seed k)"
    and "m \<equiv> row-snd (comma_port_weighted_trace f seed k)"
    and "index \<equiv> 10*L-1-comma_port_proof_crossings f seed k"
    and "j \<equiv> comma_entry_port_position f d"
    and "n \<equiv> (index-j) mod L"
    and "u \<equiv> comma_port_low f active+10*m"
    and "h \<equiv> 10*active+f+(if f<9 then 1 else 0)-u"
    and "H \<equiv> comma_diagonal_headroom f P d eta"
  shows "H=comma_period_displacement f d n+h" "comma_near_closed_germ f H=(n,h)"
proof -
  let ?o = "comma_entry_port_orbit f d"
  let ?e = "if f<9 then 1 else 0"
  let ?b = "1+?e"
  let ?w = "snd (comma_port_weighted_trace f seed k)"
  have law: "comma_entry_port_anchor_law f d"
    by (rule comma_entry_port_anchor_law[OF sector digit])
  have L_bound: "2\<le>L" and orbit: "?o<10" and j_bound: "j<L"
    and source_phase: "d=comma_phase_digit f ?o j"
    and seed_digit: "1\<le>seed" "seed\<le>9"
    using law by (auto simp: comma_entry_port_anchor_law_def L_def j_def seed_def)
  have selected': "comma_port_weighted_locator f seed row=Some k"
    using selected by (simp add: seed_def row_def)
  have row_bound: "row<comma_finite_period f seed div 10"
    using comma_entry_port_row_bound[OF sector digit, of eta]
    by (simp only: row_def seed_def)
  obtain selected_k where candidate:
    "selected_k<9" "comma_port_weighted_locator f seed row=Some selected_k"
    "snd (comma_port_weighted_trace f seed selected_k)\<le>row"
    "row<snd (comma_port_weighted_trace f seed (Suc selected_k))"
    using comma_port_weighted_locator_coverage[OF sector seed_digit row_bound] by blast
  have same_selection: "selected_k=k" using candidate(2) selected' by simp
  have k_bound: "k<9" and lower: "?w\<le>row"
    and upper: "row<snd (comma_port_weighted_trace f seed (Suc k))"
    using candidate(1,3,4) by (simp_all only: same_selection)
  have active_digit: "1\<le>active" "active\<le>9"
    using comma_port_trace_digit_admitted[OF sector seed_digit, of k]
    by (simp_all add: active_def)
  have row_split: "row=?w+m" using lower by (simp add: m_def)
  have successor: "snd (comma_port_weighted_trace f seed (Suc k))=?w+
    comma_port_dwell f active"
    by (cases "comma_port_weighted_trace f seed k")
      (simp add: active_def Let_def)
  have m_bound: "m<comma_port_dwell f active" using upper row_split successor by arith
  have u_bound: "u<10*active+f"
    using comma_port_occurrence_admission(1)[OF sector active_digit,
      where u=u and m=m] m_bound by (simp add: u_def)
  have h_positive: "?e<h" using u_bound by (simp only: h_def; arith)
  have h_upper: "h\<le>10*active+f+?e" by (simp only: h_def; arith)
  have h_sum: "u+h=10*active+f+?e" using u_bound by (simp only: h_def; arith)
  have index_bound: "2*k+2\<le>10*L-1" using k_bound L_bound by arith
  have index_j: "j\<le>index"
    using k_bound L_bound j_bound comma_port_proof_crossings_bound[of f seed k]
    by (simp only: index_def; arith)
  have lift_phase: "seed=comma_phase_digit f ?o (10*L-1)"
    using comma_entry_port_lifted_seed(1)[OF sector digit]
    by (simp add: L_def seed_def)
  have transported:
    "active=comma_phase_digit f ?o index"
    "comma_vieta_root (P div 10) f ?o (10*L-1)+int (comma_port_low f seed)+10*int ?w=
      comma_vieta_root (P div 10) f ?o index+int (comma_port_low f active)"
    using comma_port_weighted_root_transport[OF sector seed_digit lift_phase index_bound,
      where M="P div 10"] by (simp_all add: active_def index_def)
  have baseline: "comma_vieta_guard_root ?e (P div 10) f ?o (10*L-1)+
    int (comma_port_low f seed)=-9*int P"
    using comma_entry_port_lifted_seed(2)[OF sector digit]
    by (simp add: L_def P_def seed_def)
  have int_row: "int row=int ?w+int m" using arg_cong[OF row_split, of int]
    by (simp only: of_nat_add)
  have int_u: "int u=int (comma_port_low f active)+10*int m"
    by (simp only: u_def of_nat_add of_nat_mult of_nat_numeral)
  have int_h_sum: "int u+int h=10*int active+int f+int ?e"
    using arg_cong[OF h_sum, of int]
    by (simp only: of_nat_add of_nat_mult of_nat_numeral)
  have root_row: "comma_vieta_guard_root ?e (P div 10) f ?o index+int u=
    10*int row-9*int P"
    using transported(2) baseline int_row int_u
    unfolding comma_vieta_guard_root_def
    by linarith
  have catalog: "P\<in>comma_cycle_displacements"
    using comma_finite_period_in_catalog[rule_format, of f d] sector digit
    by (simp add: P_def)
  have positive: "0<P" and decimal: "10 dvd P"
    using comma_entry_period_decimal[OF catalog] by blast+
  have decimal_eq: "P=10*(P div 10)" using decimal by (simp add: dvd_mult_div_cancel)
  have decimal_int: "int P=10*int (P div 10)"
    using arg_cong[OF decimal_eq, of int] by (simp only: of_nat_mult of_nat_numeral)
  have root_gap: "int (comma_period_displacement f ?o index)+int h=
    10*int P-int ?o-10*int row"
    using root_row int_h_sum decimal_int
    by (simp only: comma_vieta_guard_root_def comma_vieta_root_def of_nat_add of_nat_mult
      of_nat_numeral transported(1)[symmetric]; linarith)
  let ?raw = "index-j"
  let ?t = "?raw div L"
  have split: "?raw=?t*L+n" by (simp add: n_def div_mult_mod_eq)
  have start: "index=j+?raw" using index_j by arith
  have shift: "comma_period_displacement f ?o index=
    comma_period_displacement f ?o j+comma_period_displacement f d ?raw"
    using comma_entry_displacement_shift[OF source_phase, of ?raw]
    by (simp only: start[symmetric])
  have closes: "10 dvd L*f" using comma_cycle_length_admitted(2)[OF sector]
    by (simp add: L_def)
  have repeated_closed: "comma_period_displacement f d (?t*L+n)=
    ?t*P+comma_period_displacement f d n"
    using comma_period_displacement_repeated[OF closes, of d ?t n]
      comma_finite_period_refines[OF sector digit]
    by (simp only: P_def L_def)
  have repeated: "comma_period_displacement f d ?raw=
    ?t*P+comma_period_displacement f d n"
    using repeated_closed by (simp only: split[symmetric])
  have big_closes: "10 dvd (?t*L)*f" using closes by (simp add: mult.assoc)
  have phase_shift: "comma_phase_digit f ?o index=comma_phase_digit f d ?raw"
    using comma_entry_phase_shift[OF source_phase, of ?raw]
    by (simp only: start[symmetric])
  have phase_periodic: "comma_phase_digit f d ?raw=comma_phase_digit f d n"
    using comma_phase_digit_periodic[OF big_closes, of d n]
    by (simp only: split[symmetric])
  have phase: "active=comma_phase_digit f d n"
    using transported(1) phase_shift phase_periodic by arith
  have n_bound: "n<L" using L_bound by (simp add: n_def)
  have next_bound: "comma_period_displacement f d (Suc n)\<le>P"
    using comma_period_displacement_mono[of "Suc n" L f d] n_bound
      comma_finite_period_refines[OF sector digit] by (simp add: P_def L_def)
  have target_lower: "?b\<le>comma_period_displacement f d n+h" using h_positive by arith
  have target_upper: "comma_period_displacement f d n+h\<le>P+?e"
    using next_bound h_upper phase comma_period_displacement_succ[of f d n] by arith
  have int_shift: "int (comma_period_displacement f ?o index)=
    int (comma_period_displacement f ?o j)+int (comma_period_displacement f d ?raw)"
    using arg_cong[OF shift, of int] by (simp only: of_nat_add)
  have int_repeated: "int (comma_period_displacement f d ?raw)=
    int ?t*int P+int (comma_period_displacement f d n)"
    using arg_cong[OF repeated, of int] by (simp only: of_nat_add of_nat_mult)
  have normalize: "-10*int row-(int ?o+int ?b)-int (comma_period_displacement f ?o j)=
    int (comma_period_displacement f d n+h)-int ?b+(int ?t-10)*int P"
    using root_gap int_shift int_repeated
    by (simp only: of_nat_add; simp add: algebra_simps; linarith)
  have H_conjugate: "H=?b+nat ((-10*int row-(int ?o+int ?b)-
    int (comma_period_displacement f ?o j)) mod int P)"
    using comma_entry_port_headroom_conjugacy[OF sector digit, of eta]
    by (simp only: H_def P_def row_def j_def comma_port_conjugate_headroom_def Let_def)
  have source_H: "H=?b+nat ((int (comma_period_displacement f d n+h)-int ?b) mod int P)"
    by (simp only: H_conjugate normalize; simp add: mod_add_eq)
  have bounded_lower: "0\<le>int (comma_period_displacement f d n+h)-int ?b"
    using target_lower by simp
  have bounded_upper: "int (comma_period_displacement f d n+h)-int ?b<int P"
    using target_upper by (simp; arith)
  show exact: "H=comma_period_displacement f d n+h"
    using source_H mod_pos_pos_trivial[OF bounded_lower bounded_upper] target_lower by simp
  have chart: "?e<H" "H\<le>540" "(H+d) mod 10=0"
    using comma_entry_diagonal_chart[OF sector digit, where eta=eta]
    by (simp_all add: H_def P_def)
  have guards: "comma_period_displacement f d n+?e<H"
    "H\<le>comma_period_displacement f d (Suc n)+?e"
    using exact h_positive h_upper phase comma_period_displacement_succ[of f d n] by arith+
  have germ: "comma_near_germ f H=(n,h)"
    using comma_near_germ_from_maximal_displacement[OF sector chart(2) digit chart(3) guards]
      exact by simp
  show "comma_near_closed_germ f H=(n,h)"
    using comma_near_closed_germ_correct_all[of f H] germ by simp
qed

text \<open>The signed anchor is retained as an arithmetic lemma. The executable
weighted consumer below uses only the selected port and its residual dwell;
it does not execute the proof-only crossing count or retain a root itinerary.
The theorem covers the actual Entry target, not the global winning branch.\<close>

definition comma_entry_weighted_headroom ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat option" where
  "comma_entry_weighted_headroom f d eta =
    (let seed=comma_entry_port_seed f d; row=comma_entry_port_row f d eta in
      map_option (\<lambda>k. let active=fst (comma_port_weighted_trace f seed k);
        m=row-snd (comma_port_weighted_trace f seed k) in
        10*active+f+(if f<9 then 1 else 0)-(comma_port_low f active+10*m))
      (comma_port_weighted_locator f seed row))"

lemma comma_entry_weighted_headroom_selected:
  assumes sector: "1\<le>f" "f\<le>9" and digit: "d<10"
    and selected: "comma_port_weighted_locator f (comma_entry_port_seed f d)
      (comma_entry_port_row f d eta)=Some k"
  shows "comma_entry_weighted_headroom f d eta=Some
    (snd (comma_near_closed_germ f
      (comma_diagonal_headroom f (comma_finite_period f d) d eta)))"
proof -
  note physical = comma_entry_port_selected_physical(2)[OF sector digit selected]
  show ?thesis
    by (simp only: comma_entry_weighted_headroom_def Let_def selected option.map
      physical snd_conv)
qed

theorem comma_entry_weighted_target:
  assumes sector: "1\<le>f" "f\<le>9" and offset: "x\<le>98"
    and key: "comma_entry_diagonal_key f r delta x=(d,eta)"
  shows "comma_entry_weighted_headroom f d eta\<noteq>None"
    "comma_fast_sector_target r (Comma_Entry f delta x)=
      Comma_Near f delta (the (comma_entry_weighted_headroom f d eta))"
proof -
  have digit: "d=x mod 10" using key
    by (simp add: comma_entry_diagonal_key_def prod_eq_iff)
  have bound: "d<10" using digit by simp
  obtain k where selected:
    "comma_port_weighted_locator f (comma_entry_port_seed f d)
      (comma_entry_port_row f d eta)=Some k"
    using comma_entry_port_locator_admitted[OF sector bound, where eta=eta] by blast
  have headroom: "comma_entry_weighted_headroom f d eta=Some
    (snd (comma_near_closed_germ f
      (comma_diagonal_headroom f (comma_finite_period f d) d eta)))"
    by (rule comma_entry_weighted_headroom_selected[OF sector bound selected])
  show "comma_entry_weighted_headroom f d eta\<noteq>None"
    using headroom by auto
  have fast: "comma_finite_period_fast f d=comma_finite_period f d"
    by (rule comma_finite_period_fast_correct[OF sector bound])
  have target: "comma_fast_sector_target r (Comma_Entry f delta x)=
    Comma_Near f delta (snd (comma_near_closed_germ f
      (comma_diagonal_headroom f (comma_finite_period f d) d eta)))"
    using comma_entry_diagonal_refines[OF sector offset]
    by (simp only: key Let_def prod.case comma_entry_diagonal_endpoint_def fast)
  show "comma_fast_sector_target r (Comma_Entry f delta x)=
      Comma_Near f delta (the (comma_entry_weighted_headroom f d eta))"
    by (simp only: headroom option.sel target)
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_entry_port_anchor_laws_checked comma_entry_port_headroom_conjugacy
      comma_entry_port_row_bound comma_entry_port_locator_admitted
      comma_entry_phase_shift comma_entry_displacement_shift
      comma_entry_guard_root_periodic comma_entry_guard_root_phase_transport
      comma_entry_guard_root_potential_transport comma_entry_port_seed_root
      comma_entry_guard_root_repeated comma_entry_port_lifted_seed
      comma_port_proof_crossings_bound
      comma_port_weighted_root_transport comma_entry_diagonal_chart
      comma_entry_port_selected_physical
      comma_entry_weighted_headroom_selected comma_entry_weighted_target}) then ()
    else error "Comma Entry port anchor depends on an oracle";
\<close>
end
