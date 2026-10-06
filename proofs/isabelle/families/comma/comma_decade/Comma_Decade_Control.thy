theory Comma_Decade_Control
  imports Comma_Round_Totality.Comma_Round_Closure
begin

ML_file "../comma_entry_arithmetic/proof_profile.ML"

ML \<open>val comma_decade_checkpoint = Comma_Proof_Profile.timer "Decade control"\<close>

text \<open>Admission and the decimal exponent shift belong to the chart
occurrence.  A round retains only its counted canonical control effect.\<close>

fun comma_round_admitted :: "comma_finite_position \<Rightarrow> bool" where
  "comma_round_admitted (Comma_Entry f delta offset) =
    (1 \<le> f \<and> f \<le> 9 \<and> offset \<le> 98)"
| "comma_round_admitted (Comma_Near f delta headroom) =
    (1 \<le> f \<and> f \<le> 9 \<and>
      1 \<le> headroom \<and> headroom \<le> 540)"

text \<open>
The round kernel above intentionally uses the coarse Entry envelope
\(x \le 98\).  Published sector responses and decade roots use the
canonical subdomains below.  Keeping these predicates here gives the
decoder and all downstream control code one owner for the boundary;
it does not change coarse round admission.
\<close>

definition comma_sector_entry_bound :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "comma_sector_entry_bound f x =
    (1 \<le> f \<and> f \<le> 9 \<and> x \<le> 89 + f)"

definition comma_sector_entry_admitted ::
    "comma_finite_position \<Rightarrow> bool" where
  "comma_sector_entry_admitted position =
    (case position of
      Comma_Entry f delta x \<Rightarrow> comma_sector_entry_bound f x
    | Comma_Near f delta h \<Rightarrow> False)"

definition comma_decade_root_admitted ::
    "comma_finite_position \<Rightarrow> bool" where
  "comma_decade_root_admitted position =
    (case position of
      Comma_Entry f delta x \<Rightarrow> f = 1 \<and> x \<le> 90
    | Comma_Near f delta h \<Rightarrow> False)"

lemma comma_sector_entry_admitted_entry [simp]:
  "comma_sector_entry_admitted (Comma_Entry f delta x) =
    (1 \<le> f \<and> f \<le> 9 \<and> x \<le> 89 + f)"
  by (simp add: comma_sector_entry_admitted_def comma_sector_entry_bound_def)

lemma comma_sector_entry_admitted_near [simp]:
  "comma_sector_entry_admitted (Comma_Near f delta h) = False"
  by (simp add: comma_sector_entry_admitted_def)

lemma comma_decade_root_admitted_entry [simp]:
  "comma_decade_root_admitted (Comma_Entry f delta x) =
    (f = 1 \<and> x \<le> 90)"
  by (simp add: comma_decade_root_admitted_def)

lemma comma_decade_root_admitted_near [simp]:
  "comma_decade_root_admitted (Comma_Near f delta h) = False"
  by (simp add: comma_decade_root_admitted_def)

definition comma_canonical_position_admitted ::
    "comma_finite_position \<Rightarrow> bool" where
  "comma_canonical_position_admitted position =
    (case position of
      Comma_Entry f delta x \<Rightarrow> comma_sector_entry_bound f x
    | Comma_Near f delta h \<Rightarrow>
        1 \<le> f \<and> f \<le> 9 \<and> 1 \<le> h \<and> h \<le> 540)"

lemma comma_canonical_position_entry [simp]:
  "comma_canonical_position_admitted (Comma_Entry f delta x) =
    comma_sector_entry_bound f x"
  by (simp add: comma_canonical_position_admitted_def)

lemma comma_canonical_position_near [simp]:
  "comma_canonical_position_admitted (Comma_Near f delta h) =
    (1 \<le> f \<and> f \<le> 9 \<and> 1 \<le> h \<and> h \<le> 540)"
  by (simp add: comma_canonical_position_admitted_def)

lemma comma_canonical_position_implies_round_admitted:
  assumes "comma_canonical_position_admitted position"
  shows "comma_round_admitted position"
  using assms
  by (cases position; simp add: comma_canonical_position_admitted_def
      comma_sector_entry_bound_def; arith)

fun comma_round_delta :: "comma_finite_position \<Rightarrow> nat" where
  "comma_round_delta (Comma_Entry f delta offset) = delta"
| "comma_round_delta (Comma_Near f delta headroom) = delta"

ML \<open>comma_decade_checkpoint "comma_round_admitted_not_invalid"\<close>

lemma comma_round_admitted_not_invalid:
  assumes valid: "comma_round_admitted source"
  shows "comma_finite_step (residue mod 924) source \<noteq> Comma_Invalid"
proof (cases source)
  case (Comma_Entry f delta offset)
  have f: "1 \<le> f" "f \<le> 9" and offset: "offset \<le> 98"
    using valid by (simp_all add: Comma_Entry)
  have positive: "comma_finite_period f (offset mod 10) \<noteq> 0"
    using comma_finite_period_in_catalog[rule_format, of f "offset mod 10"] f
    by (auto simp: comma_cycle_displacements_def)
  show ?thesis using f offset positive
    by (simp add: Comma_Entry comma_finite_step_def
      comma_weighted_step_def Let_def)
next
  case (Comma_Near f delta headroom)
  show ?thesis using valid
    by (simp add: Comma_Near comma_finite_step_def
      comma_weighted_step_def Let_def split: if_splits)
qed

ML \<open>comma_decade_checkpoint "comma_round_next_admitted"\<close>

lemma comma_near_next_canonical:
  assumes sector: "1\<le>f" "f\<le>9"
    and headroom: "1\<le>h" "h\<le>540"
    and move: "comma_finite_step (residue mod 924) (Comma_Near f delta h)=
      Comma_Next target"
  shows "comma_canonical_position_admitted target"
proof -
  have digit: "(10-h mod 10) mod 10\<le>9" by simp
  show ?thesis using move sector headroom digit
    by (auto simp: comma_canonical_position_admitted_def
      comma_sector_entry_bound_def comma_finite_step_def
      comma_weighted_step_def Let_def split: if_splits; arith)
qed

lemma comma_round_next_admitted:
  assumes valid: "comma_round_admitted source"
    and move: "comma_finite_step (residue mod 924) source =
      Comma_Next target"
  shows "comma_round_admitted target"
proof (cases source)
  case (Comma_Entry f delta offset)
  have f: "1 \<le> f" "f \<le> 9" and offset: "offset \<le> 98"
    using valid by (simp_all add: Comma_Entry)
  have positive: "comma_finite_period f (offset mod 10) \<noteq> 0"
    using comma_finite_period_in_catalog[rule_format, of f "offset mod 10"] f
    by (auto simp: comma_cycle_displacements_def)
  have target: "target = Comma_Near f delta
      (comma_finite_headroom f (residue mod 924) delta offset)"
    using move f offset positive
    by (simp add: Comma_Entry comma_finite_step_def
      comma_weighted_step_def Let_def)
  have exponent: "5 \<le> 924 + residue" by simp
  have headroom: "1 \<le> comma_finite_headroom f (residue mod 924)
      delta offset"
    using comma_finite_entry_headroom_admitted(1)
      [OF f exponent offset, of delta] by simp
  have upper: "comma_finite_headroom f (residue mod 924)
      delta offset \<le> 540"
    using comma_round_entry_headroom_bound[OF f offset] .
  show ?thesis using target f headroom upper by simp
next
  case (Comma_Near f delta headroom)
  have f: "1 \<le> f" "f \<le> 9"
    and headroom: "1 \<le> headroom" "headroom \<le> 540"
    using valid by (simp_all add: Comma_Near)
  have canonical: "comma_canonical_position_admitted target"
    by (rule comma_near_next_canonical[OF f headroom])
      (use move in \<open>simp only: Comma_Near\<close>)
  show ?thesis
    by (rule comma_canonical_position_implies_round_admitted[OF canonical])
qed

lemma comma_round_next_delta:
  assumes valid: "comma_round_admitted source"
    and move: "comma_finite_step (residue mod 924) source =
      Comma_Next target"
  shows "(if comma_round_crossing source target then
      comma_round_delta target = Suc (comma_round_delta source)
    else comma_round_delta target = comma_round_delta source)"
  using valid move
  by (cases source; cases target)
    (auto simp: comma_round_crossing_def comma_finite_step_def
      comma_weighted_step_def Let_def split: if_splits)


text \<open>Counts are canonical chart steps, not literal ticks. Terminal
inspection consumes one chart operation but is not a Next edge, and
consumes zero literal ticks. The invalid convention below excludes the
failing inspection; diagnostic evaluator cost must still charge that call.\<close>
fun comma_round_consumed_steps :: "nat \<Rightarrow> comma_round_result \<Rightarrow> nat" where
  "comma_round_consumed_steps n Comma_Round_Invalid = n"
| "comma_round_consumed_steps n (Comma_Round_Fork a d) = Suc n"
| "comma_round_consumed_steps n (Comma_Round_Landmine d) = Suc n"
| "comma_round_consumed_steps n (Comma_Round_Cross p) = Suc n"

definition comma_round_internal_control_steps :: "nat \<Rightarrow> nat" where
  "comma_round_internal_control_steps n = n"

lemma comma_round_prefix_admitted:
  assumes "comma_round_prefix_steps n r p t" "comma_round_admitted p"
  shows "comma_round_admitted t"
  using assms
  by (induction n arbitrary: p) (auto intro: comma_round_next_admitted)

lemma comma_round_close_admitted:
  assumes close: "comma_round_close r p = (n,t,result)"
    and valid: "comma_round_admitted p"
  shows "comma_round_admitted t" "result \<noteq> Comma_Round_Invalid"
proof -
  have trace: "comma_round_prefix_steps n r p t"
    using comma_round_close_refines_trace[OF close] by simp
  show admitted: "comma_round_admitted t"
    using comma_round_prefix_admitted[OF trace valid] .
  show "result \<noteq> Comma_Round_Invalid"
    using comma_round_close_refines_trace[OF close]
      comma_round_admitted_not_invalid[OF admitted, of r]
    by (cases result) auto
qed

lemma comma_round_cross_consumed:
  assumes "comma_round_close r p = (n,t,Comma_Round_Cross q)"
  shows "comma_round_prefix_steps
    (comma_round_consumed_steps n (Comma_Round_Cross q)) r p q"
  using comma_round_close_cross_prefix[OF assms] by simp

lemma comma_round_terminal_inspection:
  assumes "comma_round_close r p = (n,t,Comma_Round_Fork a d)"
  shows "comma_finite_run
    (comma_round_consumed_steps n (Comma_Round_Fork a d))
    (r mod 924) p = Some (Comma_Fork_At a d)"
  using comma_round_close_fork_finite_run[OF assms] by simp

lemma comma_round_landmine_inspection:
  assumes "comma_round_close r p = (n,t,Comma_Round_Landmine d)"
  shows "comma_finite_run
    (comma_round_consumed_steps n (Comma_Round_Landmine d))
    (r mod 924) p = Some (Comma_Landmine_At d)"
  using comma_round_close_landmine_finite_run[OF assms] by simp

fun comma_shift_round_result :: "nat \<Rightarrow> comma_round_result \<Rightarrow> comma_round_result" where
  "comma_shift_round_result k (Comma_Round_Fork a d) = Comma_Round_Fork a (d+k)"
| "comma_shift_round_result k (Comma_Round_Landmine d) = Comma_Round_Landmine (d+k)"
| "comma_shift_round_result k (Comma_Round_Cross p) = Comma_Round_Cross (comma_shift_position k p)"
| "comma_shift_round_result k Comma_Round_Invalid = Comma_Round_Invalid"

definition comma_shift_round_close where
  "comma_shift_round_close k answer =
    (case answer of (n,t,result) \<Rightarrow>
      (n,comma_shift_position k t,comma_shift_round_result k result))"

lemma comma_round_crossing_shift [simp]:
  "comma_round_crossing (comma_shift_position k p) (comma_shift_position k q) =
    comma_round_crossing p q"
  by (cases p; cases q) (simp_all add: comma_round_crossing_def)

lemma comma_round_step_shift:
  "comma_finite_step (r mod 924) (comma_shift_position k p) =
    comma_shift_move k (comma_finite_step (((r+k) mod 924) mod 924) p)"
  using comma_finite_step_phase_shift[of "r mod 924" k p]
  by (simp add: mod_add_left_eq)

ML \<open>comma_decade_checkpoint "comma_round_close_phase_shift"\<close>

lemma comma_round_close_phase_shift:
  "comma_round_close r (comma_shift_position k p) =
    comma_shift_round_close k (comma_round_close ((r+k) mod 924) p)"
proof (induction p arbitrary: r rule: measure_induct_rule[where f=comma_round_measure])
  case (less p)
  let ?phase = "(r+k) mod 924"
  note left = comma_round_close.simps[of r "comma_shift_position k p"]
  note right = comma_round_close.simps[of ?phase p]
  show ?case
  proof (cases "comma_finite_step (?phase mod 924) p")
    case (Comma_Next q)
    have moved: "comma_finite_step (r mod 924) (comma_shift_position k p) =
      Comma_Next (comma_shift_position k q)"
      by (simp only: comma_round_step_shift Comma_Next comma_shift_move.simps)
    show ?thesis
    proof (cases "comma_round_crossing p q")
      case True
      show ?thesis
        using left right
        by (simp only: moved Comma_Next comma_finite_move.case
          comma_round_crossing_shift True if_True
          comma_shift_round_close_def prod.case comma_shift_round_result.simps)
    next
      case False
      have decrease: "comma_round_measure q < comma_round_measure p"
        by (rule comma_round_next_decreases[OF Comma_Next False])
      have ih: "comma_round_close r (comma_shift_position k q) =
        comma_shift_round_close k (comma_round_close ?phase q)"
        by (rule less.IH[OF decrease])
      obtain n t result where answer:
        "comma_round_close ?phase q = (n,t,result)"
        by (cases "comma_round_close ?phase q") auto
      show ?thesis
        using left right
        by (simp only: moved Comma_Next comma_finite_move.case
          comma_round_crossing_shift False if_False ih answer
          comma_shift_round_close_def prod.case Let_def)
    qed
  next
    case (Comma_Fork a d)
    show ?thesis
      using left right
      by (simp only: comma_round_step_shift Comma_Fork comma_shift_move.simps
        comma_finite_move.case comma_shift_round_close_def prod.case
        comma_shift_round_result.simps)
  next
    case (Comma_Landmine d)
    show ?thesis
      using left right
      by (simp only: comma_round_step_shift Comma_Landmine comma_shift_move.simps
        comma_finite_move.case comma_shift_round_close_def prod.case
        comma_shift_round_result.simps)
  next
    case Comma_Invalid
    show ?thesis
      using left right
      by (simp only: comma_round_step_shift Comma_Invalid comma_shift_move.simps
        comma_finite_move.case comma_shift_round_close_def prod.case
        comma_shift_round_result.simps)
  qed
qed

lemma comma_round_close_phase_normalized:
  "comma_round_close r (Comma_Entry f d x) =
    comma_shift_round_close d
      (comma_round_close ((r+d) mod 924) (Comma_Entry f 0 x))"
  using comma_round_close_phase_shift[of r d "Comma_Entry f 0 x"] by simp

lemma comma_round_close_delta:
  assumes close: "comma_round_close r p = (n,t,result)"
    and valid: "comma_round_admitted p"
  shows "comma_round_delta t = comma_round_delta p"
  using close valid
proof (induction r p arbitrary: n t result rule: comma_round_close.induct)
  case (1 r p)
  show ?case
    using 1 comma_round_next_admitted comma_round_next_delta
    by (cases "comma_finite_step (r mod 924) p")
      (auto simp: comma_round_close.simps split: if_splits prod.splits)
qed

lemma comma_round_close_crossing_shape:
  assumes close: "comma_round_close r p = (n,t,Comma_Round_Cross q)"
  shows "\<exists>d h x. t = Comma_Near 9 d h \<and>
    q = Comma_Entry 1 (Suc d) x \<and> x \<le> 90 \<and>
    comma_normalize_position r q = Comma_Entry 1 ((r+d+1) mod 924) x"
proof -
  have move: "comma_finite_step (r mod 924) t = Comma_Next q"
    and crossing: "comma_round_crossing t q"
    using comma_round_close_refines_trace[OF close] by simp_all
  obtain d h x where shape: "t = Comma_Near 9 d h"
    "q = Comma_Entry 1 (Suc d) x" "x \<le> 90"
    using comma_round_crossing_offset_bound[OF move crossing] by blast
  show ?thesis using shape by (auto simp: add_Suc_right)
qed


lemma comma_round_close_crossing_phase:
  assumes close: "comma_round_close r p = (n,t,Comma_Round_Cross q)"
    and valid: "comma_round_admitted p"
  shows "\<exists>x\<le>90. q = Comma_Entry 1 (Suc (comma_round_delta p)) x \<and>
    comma_normalize_position r q =
      Comma_Entry 1 ((r + comma_round_delta p + 1) mod 924) x"
  using comma_round_close_crossing_shape[OF close]
    comma_round_close_delta[OF close valid]
  by auto


lemma comma_round_crossing_next_normalized:
  assumes close: "comma_round_close r p = (n,t,Comma_Round_Cross q)"
    and valid: "comma_round_admitted p"
  shows "\<exists>x\<le>90. comma_round_close r q =
    comma_shift_round_close (Suc (comma_round_delta p))
      (comma_round_close ((r + comma_round_delta p + 1) mod 924)
        (Comma_Entry 1 0 x))"
proof -
  obtain x where x: "x \<le> 90"
    "q = Comma_Entry 1 (Suc (comma_round_delta p)) x"
    using comma_round_close_crossing_phase[OF close valid] by blast
  show ?thesis
    using x comma_round_close_phase_normalized[of r 1 "Suc (comma_round_delta p)" x]
    by (auto simp: add_Suc_right)
qed


datatype comma_decade_state = Comma_Decade nat nat

datatype comma_decade_outcome =
    Comma_Decade_Fork nat nat
  | Comma_Decade_Landmine nat
  | Comma_Decade_Continue comma_decade_state
  | Comma_Decade_Invalid

fun comma_decade_admitted :: "comma_decade_state \<Rightarrow> bool" where
  "comma_decade_admitted (Comma_Decade phase offset) =
    (phase < 924 \<and> offset \<le> 90)"

fun comma_decade_decode :: "nat \<Rightarrow> comma_round_result \<Rightarrow> comma_decade_outcome" where
  "comma_decade_decode r (Comma_Round_Fork a d) = Comma_Decade_Fork a d"
| "comma_decade_decode r (Comma_Round_Landmine d) = Comma_Decade_Landmine d"
| "comma_decade_decode r (Comma_Round_Cross (Comma_Entry f d x)) =
    (if comma_decade_root_admitted (Comma_Entry f d x)
     then Comma_Decade_Continue (Comma_Decade ((r+d) mod 924) x)
      else Comma_Decade_Invalid)"
| "comma_decade_decode r (Comma_Round_Cross (Comma_Near f d h)) = Comma_Decade_Invalid"
| "comma_decade_decode r Comma_Round_Invalid = Comma_Decade_Invalid"

fun comma_decade_control :: "comma_decade_state \<Rightarrow> comma_decade_outcome" where
  "comma_decade_control (Comma_Decade r x) =
    (case comma_round_close r (Comma_Entry 1 0 x) of
      (n,t,result) \<Rightarrow> comma_decade_decode r result)"

ML \<open>comma_decade_checkpoint "comma_decade_control_closed"\<close>

lemma comma_decade_control_closed:
  assumes valid: "comma_decade_admitted s"
    and control: "comma_decade_control s = outcome"
  shows "outcome \<noteq> Comma_Decade_Invalid"
    "\<And>q. outcome = Comma_Decade_Continue q \<Longrightarrow> comma_decade_admitted q"
proof -
  obtain r x where s: "s = Comma_Decade r x" by (cases s) auto
  obtain n t result where close:
    "comma_round_close r (Comma_Entry 1 0 x) = (n,t,result)"
    by (cases "comma_round_close r (Comma_Entry 1 0 x)") auto
  have entry: "comma_round_admitted (Comma_Entry 1 0 x)"
    using valid by (simp add: s)
  have not_invalid: "result \<noteq> Comma_Round_Invalid"
    using comma_round_close_admitted(2)[OF close entry] .
  have crossing: "\<And>q. result = Comma_Round_Cross q \<Longrightarrow>
    \<exists>d h x. t = Comma_Near 9 d h \<and> q = Comma_Entry 1 (Suc d) x \<and> x \<le> 90"
    using comma_round_close_crossing_shape[of r "Comma_Entry 1 0 x" n t]
      close by blast
  have decode: "outcome = comma_decade_decode r result"
    using control by (simp only: s comma_decade_control.simps close prod.case)
  show "outcome \<noteq> Comma_Decade_Invalid"
    using decode not_invalid crossing
    by (cases result) auto
  fix q assume "outcome = Comma_Decade_Continue q"
  then show "comma_decade_admitted q"
    using decode not_invalid crossing
    by (cases result) auto
qed

text \<open>This is a constructor-totality rank, separate from the future
safety ranks for losing branches. The checker permits any strict decrease;
it does not require the exact-height convention of comma_rank_witness.
No concrete rank table or numerical bound is assumed to have passed.\<close>
definition comma_decade_rank_check :: "(comma_decade_state \<Rightarrow> nat) \<Rightarrow> bool" where
  "comma_decade_rank_check rank =
    (\<forall>s. comma_decade_admitted s \<longrightarrow>
      (case comma_decade_control s of
        Comma_Decade_Continue q \<Rightarrow>
          comma_decade_admitted q \<and> rank q < rank s
      | Comma_Decade_Invalid \<Rightarrow> False
      | _ \<Rightarrow> True))"

inductive comma_decade_finishes :: "comma_decade_state \<Rightarrow> nat \<Rightarrow> bool" where
  fork: "comma_decade_control s = Comma_Decade_Fork a d \<Longrightarrow>
    comma_decade_finishes s 1"
| landmine: "comma_decade_control s = Comma_Decade_Landmine d \<Longrightarrow>
    comma_decade_finishes s 1"
| crossing: "comma_decade_control s = Comma_Decade_Continue q \<Longrightarrow>
    comma_decade_finishes q n \<Longrightarrow> comma_decade_finishes s (Suc n)"

ML \<open>comma_decade_checkpoint "comma_decade_checked_rank_totality"\<close>

theorem comma_decade_checked_rank_totality:
  assumes checked: "comma_decade_rank_check rank"
    and valid: "comma_decade_admitted s"
  shows "\<exists>n. comma_decade_finishes s n \<and> n \<le> Suc (rank s)"
  using valid
proof (induction "rank s" arbitrary: s rule: less_induct)
  case less
  have check: "case comma_decade_control s of
      Comma_Decade_Continue q \<Rightarrow> comma_decade_admitted q \<and> rank q < rank s
    | Comma_Decade_Invalid \<Rightarrow> False | _ \<Rightarrow> True"
    using checked less.prems by (simp add: comma_decade_rank_check_def)
  show ?case
  proof (cases "comma_decade_control s")
    case (Comma_Decade_Fork a d)
    then show ?thesis using comma_decade_finishes.fork by fastforce
  next
    case (Comma_Decade_Landmine d)
    then show ?thesis using comma_decade_finishes.landmine by fastforce
  next
    case (Comma_Decade_Continue q)
    have q: "comma_decade_admitted q" "rank q < rank s"
      using check Comma_Decade_Continue by simp_all
    obtain n where finish: "comma_decade_finishes q n" and bound: "n \<le> Suc (rank q)"
      using less.hyps[OF q(2) q(1)] by blast
    have "comma_decade_finishes s (Suc n)"
      by (rule comma_decade_finishes.crossing[OF Comma_Decade_Continue finish])
    moreover have "Suc n \<le> Suc (rank s)" using bound q(2) by arith
    ultimately show ?thesis by blast
  next
    case Comma_Decade_Invalid
    then show ?thesis using check by simp
  qed
qed
ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_round_close_admitted comma_round_close_phase_shift
      comma_round_close_phase_normalized comma_round_close_crossing_shape
      comma_decade_control_closed comma_decade_checked_rank_totality})
    then () else error "Comma decade control depends on an oracle";
\<close>
ML \<open>comma_decade_checkpoint "complete"\<close>
end
