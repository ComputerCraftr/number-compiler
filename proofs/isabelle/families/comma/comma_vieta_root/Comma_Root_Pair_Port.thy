theory Comma_Root_Pair_Port
  imports Comma_Vieta_Root_Frame
begin

text \<open>This local port factors the authenticated root residual. Absolute
source clock, exponent transport and inter-sector re-entry remain occurrence
obligations. The predecessor uses nonnegative shifted modulo; natural-number
truncated subtraction is not a decimal rotation.\<close>

definition comma_port_low :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_port_low f d=(if f<9 then (d+f+1) mod 10 else (d+9) mod 10)"

definition comma_port_dwell :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_port_dwell f d=(if f<9 then d+(if 9-f\<le>d \<and> d<9 then 1 else 0) else d+1)"

definition comma_port_previous :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_port_previous f d=(d+10-f) mod 10"

definition comma_port_next :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_port_next f d=(let previous=comma_port_previous f d
    in if previous=0 then comma_port_previous f previous else previous)"

definition comma_port_first_residual :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_port_first_residual f d=comma_port_low f d+10*comma_port_dwell f d-(10*d+f)"

definition comma_port_local_law :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "comma_port_local_law f d =
    (comma_port_low f d<10 \<and> comma_port_low f d<10*d+f \<and>
     comma_port_dwell f d=comma_vieta_root_run f d (comma_port_low f d) \<and>
     comma_port_first_residual f d<10 \<and>
     1\<le>comma_port_next f d \<and> comma_port_next f d\<le>9 \<and>
     ((10*comma_port_previous f d+f\<le>comma_port_first_residual f d) =
       (comma_port_previous f d=0)) \<and>
     (if comma_port_first_residual f d<10*comma_port_previous f d+f
      then (comma_port_previous f d,comma_port_first_residual f d)
      else (comma_port_previous f (comma_port_previous f d),
        comma_port_first_residual f d-(10*comma_port_previous f d+f))) =
       (comma_port_next f d,comma_port_low f (comma_port_next f d)))"

text \<open>The finite check below proves the executable local identities;
it is not an imported row table, terminal-label certificate or source rank.
The general occurrence theorem below then quantifies over arbitrary m.\<close>

lemma comma_port_local_laws_checked:
  "list_all (\<lambda>f. list_all (comma_port_local_law f)
    [1..<10]) [1..<10]"
  by (tactic \<open>simp_tac
    (Comma_Entry_Arithmetic.natural_context @{context} |> Simplifier.add_simps
      @{thms list_all_Nil_iff list_all_Cons_iff upt_rec comma_port_local_law_def
        comma_port_low_def comma_port_dwell_def comma_port_previous_def
        comma_port_next_def comma_port_first_residual_def comma_vieta_root_run_def}) 1\<close>)

lemma comma_port_local_law:
  assumes "1\<le>f" "f\<le>9" "1\<le>d" "d\<le>9"
  shows "comma_port_local_law f d"
proof -
  have f_member: "f\<in>set [1..<10]" using assms(1,2) by simp
  have d_member: "d\<in>set [1..<10]" using assms(3,4) by simp
  show ?thesis using comma_port_local_laws_checked f_member d_member
    by (auto simp: list_all_iff)
qed

lemma comma_port_occurrence_admission:
  assumes sector: "1\<le>f" "f\<le>9" and digit: "1\<le>d" "d\<le>9"
    and occurrence: "u=comma_port_low f d+10*m"
    and admitted: "m<comma_port_dwell f d"
  shows "u<10*d+f" "0<comma_port_dwell f d-m"
proof -
  have law: "comma_port_local_law f d" by (rule comma_port_local_law[OF sector digit])
  have low: "comma_port_low f d<10" "comma_port_low f d<10*d+f"
    and dwell: "comma_port_dwell f d=comma_vieta_root_run f d (comma_port_low f d)"
    using law by (auto simp: comma_port_local_law_def)
  have safe: "comma_port_low f d+10*m<10*d+f"
    using comma_vieta_root_run_first_crossing(4)[OF sector low, of m] admitted dwell by simp
  show "u<10*d+f" using occurrence safe by simp
  show "0<comma_port_dwell f d-m" using admitted by arith
qed

lemma comma_port_pumped_first_hit:
  assumes sector: "1\<le>f" "f\<le>9" and digit: "1\<le>d" "d\<le>9"
    and occurrence: "u=comma_port_low f d+10*m"
    and admitted: "m<comma_port_dwell f d"
    and count: "q=comma_port_dwell f d-m"
  shows "0<q \<and> 10*d+f\<le>u+10*q \<and> u+10*q<10*d+f+10 \<and>
    (\<forall>j<q. u+10*j<10*d+f) \<and>
    u+10*q-(10*d+f)=comma_port_first_residual f d"
proof -
  have law: "comma_port_local_law f d" by (rule comma_port_local_law[OF sector digit])
  have low: "comma_port_low f d<10" "comma_port_low f d<10*d+f"
    and dwell: "comma_port_dwell f d=comma_vieta_root_run f d (comma_port_low f d)"
    using law by (auto simp: comma_port_local_law_def)
  have endpoint: "u+10*q=comma_port_low f d+10*comma_port_dwell f d"
    using occurrence count admitted by arith
  have crossing: "10*d+f\<le>u+10*q" "u+10*q<10*d+f+10"
    using comma_vieta_root_run_first_crossing(2,3)[OF sector low] dwell endpoint by simp_all
  have prefix: "\<forall>j<q. u+10*j<10*d+f"
  proof (intro allI impI)
    fix j assume "j<q"
    then have before: "m+j<comma_port_dwell f d" using count admitted by arith
    have safe: "comma_port_low f d+10*(m+j)<10*d+f"
      using comma_vieta_root_run_first_crossing(4)[OF sector low, of "m+j"] before dwell by simp
    show "u+10*j<10*d+f" using safe occurrence by (simp add: algebra_simps)
  qed
  show ?thesis using count admitted crossing prefix endpoint
    by (auto simp: comma_port_first_residual_def)
qed

lemma comma_port_last_row:
  assumes sector: "1\<le>f" "f\<le>9" and digit: "1\<le>d" "d\<le>9"
    and occurrence: "u=comma_port_low f d+10*m"
    and admitted: "m<comma_port_dwell f d"
    and count: "q=comma_port_dwell f d-m"
  shows "comma_vieta_row_port (10*d+f) (10*comma_port_previous f d+f)
    (u+10*(q-1)) =
      (if comma_port_previous f d=0 then 2 else 1,
        comma_port_low f (comma_port_next f d))"
proof -
  have pump: "0<q" "10*d+f\<le>u+10*q"
    "u+10*q-(10*d+f)=comma_port_first_residual f d"
    using comma_port_pumped_first_hit[OF sector digit occurrence admitted count] by blast+
  have last: "u+10*(q-1)+10=u+10*q" using pump(1) by arith
  have law: "comma_port_local_law f d" by (rule comma_port_local_law[OF sector digit])
  show ?thesis using law pump last
    by (auto simp: comma_port_local_law_def comma_vieta_row_port_def not_less split: if_splits)
qed

lemma comma_port_phase_inverse_checked:
  "list_all (\<lambda>f. list_all (\<lambda>d.
    comma_port_previous f ((d+f) mod 10)=d)
    [0..<10]) [1..<10]"
  by (tactic \<open>simp_tac
    (Comma_Entry_Arithmetic.natural_context @{context} |> Simplifier.add_simps
      @{thms list_all_Nil_iff list_all_Cons_iff upt_rec comma_port_previous_def}) 1\<close>)

lemma comma_port_actual_previous:
  assumes sector: "1\<le>f" "f\<le>9"
  shows "comma_port_previous f (comma_phase_digit f orbit (Suc n))=
    comma_phase_digit f orbit n"
proof -
  have f_member: "f\<in>set [1..<10]" using sector by simp
  have bound: "comma_phase_digit f orbit n<10" by (simp add: comma_phase_digit_def)
  have member: "comma_phase_digit f orbit n\<in>set [0..<10]"
    using bound by simp
  have inverse: "comma_port_previous f ((comma_phase_digit f orbit n+f) mod 10)=
      comma_phase_digit f orbit n"
    using comma_port_phase_inverse_checked f_member member by (auto simp: list_all_iff)
  show ?thesis using inverse comma_vieta_phase_digit_successor by simp
qed

lemma comma_port_pump_refines_ordered_roots:
  assumes sector: "1\<le>f" "f\<le>9" and digit: "1\<le>d" "d\<le>9"
    and source_phase: "d=comma_phase_digit f orbit (Suc (Suc j))"
    and occurrence: "u=comma_port_low f d+10*m"
    and admitted: "m<comma_port_dwell f d"
    and count: "q=comma_port_dwell f d-m"
  defines "crossed \<equiv> if comma_port_previous f d=0 then 2 else 1"
  shows "comma_vieta_root M f orbit (Suc (Suc j))+int u+10*int q=
      comma_vieta_root M f orbit (Suc (Suc j)-crossed)+
        int (comma_port_low f (comma_port_next f d))"
proof -
  have pump: "0<q" "\<forall>k<q. u+10*k<10*d+f"
    using comma_port_pumped_first_hit[OF sector digit occurrence admitted count] by blast+
  have last: "q-1<q" using pump(1) by arith
  have chamber: "u+10*(q-1)<10*d+f" using pump(2) last by blast
  have previous: "comma_port_previous f d=comma_phase_digit f orbit (Suc j)"
    using comma_port_actual_previous[OF sector, of orbit "Suc j"] source_phase by simp
  have port: "comma_vieta_row_port
      (comma_vieta_phase_gap f orbit (Suc (Suc j)))
      (comma_vieta_phase_gap f orbit (Suc j)) (u+10*(q-1))=
        (crossed,comma_port_low f (comma_port_next f d))"
    using comma_port_last_row[OF sector digit occurrence admitted count]
      source_phase previous by (simp add: comma_vieta_phase_gap_def crossed_def)
  have actual_chamber: "u+10*(q-1)<comma_vieta_phase_gap f orbit (Suc (Suc j))"
    using chamber source_phase by (simp add: comma_vieta_phase_gap_def)
  have equation: "comma_vieta_root M f orbit (Suc (Suc j))+int (u+10*(q-1))+10=
      comma_vieta_root M f orbit (Suc (Suc j)-crossed)+
        int (comma_port_low f (comma_port_next f d))"
    using comma_vieta_row_port_refines[OF sector actual_chamber port, of M] by blast
  have endpoint: "int (u+10*(q-1))+10=int u+10*int q"
    using pump(1) by (simp add: of_nat_diff; linarith)
  show ?thesis using equation endpoint by simp
qed

text \<open>Weighted cycles below retain only the returned digit and weight,
not a path history. Their length is obtained from the existing decimal phase
cycle owner, puncturing exactly the orbit containing zero.\<close>

definition comma_port_cycle_length :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_port_cycle_length f d=(let L=comma_cycle_length f
    in L-(if d mod (10 div L)=0 then 1 else 0))"

primrec comma_port_weighted_trace :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat\<times>nat" where
  "comma_port_weighted_trace f d 0=(d,0)"
| "comma_port_weighted_trace f d (Suc n)=
    (let (current,weight)=comma_port_weighted_trace f d n
     in (comma_port_next f current,weight+comma_port_dwell f current))"

lemma comma_port_weighted_cycles_checked:
  "list_all (\<lambda>f. list_all (\<lambda>d.
    0<comma_port_cycle_length f d \<and> comma_port_cycle_length f d\<le>9 \<and>
    comma_port_weighted_trace f d (comma_port_cycle_length f d)=
      (d,comma_finite_period f d div 10)) [1..<10]) [1..<10]"
  by (tactic \<open>
    let
      val ctxt = @{context}
      val arithmetic = Comma_Entry_Arithmetic.natural_context ctxt
      val (certify, _) = Comma_Entry_Arithmetic.make_certifier ctxt
      fun number n = HOLogic.mk_number @{typ nat} n
      fun closed_value th = #2 (HOLogic.dest_number (Thm.term_of (Thm.rhs_of th)))
      val recursion = map (Simplifier.simplify arithmetic)
        @{thms comma_port_weighted_trace.simps(2)[where n=0]
          comma_port_weighted_trace.simps(2)[where n=1]
          comma_port_weighted_trace.simps(2)[where n=2]
          comma_port_weighted_trace.simps(2)[where n=3]
          comma_port_weighted_trace.simps(2)[where n=4]
          comma_port_weighted_trace.simps(2)[where n=5]
          comma_port_weighted_trace.simps(2)[where n=6]
          comma_port_weighted_trace.simps(2)[where n=7]
          comma_port_weighted_trace.simps(2)[where n=8]}
      val length_context = arithmetic |> Simplifier.add_simps
        @{thms comma_port_cycle_length_def comma_compiled_cycle_length_facts}
      val step_context = arithmetic |> Simplifier.add_simps
        @{thms comma_port_next_def comma_port_previous_def comma_port_dwell_def}
      fun trace_term f d n =
        @{term comma_port_weighted_trace} $ number f $ number d $ number n
      fun check_pair th =
        let
          val (digit, weight) = HOLogic.dest_prod (Thm.term_of (Thm.rhs_of th))
          val _ = HOLogic.dest_number digit
          val _ = HOLogic.dest_number weight
        in certify th end
      fun port f d =
        let
          val length = certify (Simplifier.rewrite length_context
            (Thm.cterm_of ctxt (@{term comma_port_cycle_length} $ number f $ number d)))
          val count = closed_value length
          val _ = if 0<count andalso count<=9 then ()
            else error "Weighted port produced an unbounded cycle"
          val zero = check_pair (Simplifier.rewrite
            (arithmetic |> Simplifier.add_simps @{thms comma_port_weighted_trace.simps(1)})
            (Thm.cterm_of ctxt (trace_term f d 0)))
          fun successor n previous = check_pair (Simplifier.rewrite
            (step_context |> Simplifier.add_simps [previous, nth recursion (n-1)])
            (Thm.cterm_of ctxt (trace_term f d n)))
          val final = fold successor (1 upto count) zero
        in [length, final] end
      val facts = maps (fn f => maps (port f) (1 upto 9)) (1 upto 9)
    in simp_tac (arithmetic |> Simplifier.add_simps facts |> Simplifier.add_simps
      @{thms list_all_Nil_iff list_all_Cons_iff upt_rec comma_compiled_period_facts}) 1 end
    \<close>)

lemma comma_port_weighted_cycle:
  assumes sector: "1\<le>f" "f\<le>9" and digit: "1\<le>d" "d\<le>9"
  shows "0<comma_port_cycle_length f d \<and> comma_port_cycle_length f d\<le>9 \<and>
    comma_port_weighted_trace f d (comma_port_cycle_length f d)=
      (d,comma_finite_period f d div 10)"
proof -
  have f_member: "f\<in>set [1..<10]" using sector by simp
  have d_member: "d\<in>set [1..<10]" using digit by simp
  show ?thesis using comma_port_weighted_cycles_checked f_member d_member
    by (auto simp: list_all_iff)
qed

definition comma_port_weighted_locator ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat option" where
  "comma_port_weighted_locator f d row=List.find
    (\<lambda>k. row<snd (comma_port_weighted_trace f d (Suc k)))
    [0..<comma_port_cycle_length f d]"

lemma comma_port_weighted_locator_coverage:
  assumes sector: "1\<le>f" "f\<le>9" and digit: "1\<le>d" "d\<le>9"
    and row: "row<comma_finite_period f d div 10"
  shows "\<exists>k<9. comma_port_weighted_locator f d row=Some k \<and>
    snd (comma_port_weighted_trace f d k)\<le>row \<and>
    row<snd (comma_port_weighted_trace f d (Suc k))"
proof -
  let ?L = "comma_port_cycle_length f d"
  have length: "0<?L" "?L\<le>9"
    and cycle: "comma_port_weighted_trace f d ?L=(d,comma_finite_period f d div 10)"
    using comma_port_weighted_cycle[OF sector digit] by blast+
  have last: "?L-1<?L" "Suc (?L-1)=?L" using length(1) by arith+
  have witness: "?L-1\<in>set [0..<?L]"
    "row<snd (comma_port_weighted_trace f d (Suc (?L-1)))"
    using last cycle row by simp_all
  have witness_exists: "\<exists>k\<in>set [0..<?L].
    row<snd (comma_port_weighted_trace f d (Suc k))" using witness by blast
  have not_none: "comma_port_weighted_locator f d row\<noteq>None"
    using witness_exists
    by (simp only: comma_port_weighted_locator_def find_None_iff; blast)
  obtain k where selected: "comma_port_weighted_locator f d row=Some k"
    using not_none by (cases "comma_port_weighted_locator f d row") auto
  have index: "k<?L" and upper: "row<snd (comma_port_weighted_trace f d (Suc k))"
    and earlier: "\<forall>j<k. \<not>(row<snd (comma_port_weighted_trace f d (Suc j)))"
    using selected by (auto simp only: comma_port_weighted_locator_def find_Some_iff
      length_upt diff_zero nth_upt add_0_left)
  have lower: "snd (comma_port_weighted_trace f d k)\<le>row"
  proof (cases k)
    case 0
    then show ?thesis by simp
  next
    case (Suc j)
    have prior: "j<k" using Suc by simp
    have "\<not>(row<snd (comma_port_weighted_trace f d (Suc j)))"
      using earlier prior by blast
    then show ?thesis by (simp only: Suc not_less)
  qed
  show ?thesis using selected index length(2) lower upper by auto
qed

text \<open>The validator below states the physical checks separately from
weighted diagonal selection. Its actual-phase equality is a source arithmetic
obligation, not an identification of a diagonal dwell with physical time.
Coverage and totality of the weighted locator are not premises hidden here.\<close>

definition comma_port_prefix_validation ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "comma_port_prefix_validation f orbit H n d h =
    (d=comma_phase_digit f orbit n \<and>
     h=H-comma_period_displacement f orbit n \<and>
     (if f<9 then 1 else 0)<h \<and>
     h\<le>10*d+f+(if f<9 then 1 else 0))"

lemma comma_port_validation_guards:
  assumes checked: "comma_port_prefix_validation f orbit H n d h"
  shows "comma_period_displacement f orbit n+(if f<9 then 1 else 0)<H"
    "H\<le>comma_period_displacement f orbit (Suc n)+(if f<9 then 1 else 0)"
proof -
  have phase: "d=comma_phase_digit f orbit n"
    and residual: "h=H-comma_period_displacement f orbit n"
    and positive: "(if f<9 then 1 else 0)<h"
    and terminal: "h\<le>10*d+f+(if f<9 then 1 else 0)"
    using checked by (auto simp: comma_port_prefix_validation_def)
  have fits: "comma_period_displacement f orbit n\<le>H"
    using residual positive by arith
  have reconstruct: "H=comma_period_displacement f orbit n+h"
    using residual fits by arith
  show "comma_period_displacement f orbit n+(if f<9 then 1 else 0)<H"
    using reconstruct positive by arith
  show "H\<le>comma_period_displacement f orbit (Suc n)+(if f<9 then 1 else 0)"
    using reconstruct terminal phase
    by (simp only: comma_period_displacement_succ; arith)
qed

lemma comma_port_validation_refines_prefix:
  assumes sector: "1\<le>f" "f\<le>9" and source_extent: "H\<le>540"
    and source_digit: "orbit<10" and source_chart: "(H+orbit) mod 10=0"
    and checked: "comma_port_prefix_validation f orbit H n d h"
  shows "comma_near_prefix n f H h \<and> comma_near_germ f H=(n,h) \<and>
    (10-h mod 10) mod 10=d"
proof -
  have guards: "comma_period_displacement f orbit n+(if f<9 then 1 else 0)<H"
    "H\<le>comma_period_displacement f orbit (Suc n)+(if f<9 then 1 else 0)"
    using comma_port_validation_guards[OF checked] by blast+
  have residual: "h=H-comma_period_displacement f orbit n"
    and phase: "d=comma_phase_digit f orbit n"
    using checked by (auto simp: comma_port_prefix_validation_def)
  have prefix: "comma_near_prefix n f H h"
    using comma_near_prefix_from_displacement
      [OF sector source_extent source_digit source_chart guards(1)] residual by simp
  have germ: "comma_near_germ f H=(n,h)"
    using comma_near_germ_from_maximal_displacement
      [OF sector source_extent source_digit source_chart guards] residual by simp
  have fits: "comma_period_displacement f orbit n\<le>H" using guards(1) by arith
  have digit: "(10-h mod 10) mod 10=d"
    using comma_near_phase_headroom_digit[OF source_digit source_chart fits]
      residual phase by simp
  show ?thesis using prefix germ digit by blast
qed

lemma comma_port_validation_terminal:
  assumes sector: "1\<le>f" "f\<le>9" and source_extent: "H\<le>540"
    and source_digit: "orbit<10" and source_chart: "(H+orbit) mod 10=0"
    and checked: "comma_port_prefix_validation f orbit H n d h"
  shows "comma_fast_step r (Comma_Near f delta h)=
    (if f<9 then
      (if 10*d+f+1-h=0 then Comma_Fork (f+1) delta
       else Comma_Next (Comma_Entry (f+1) delta (10*d+f+1-h)))
     else
      (if 10*d+9-h<8 then Comma_Landmine delta
       else Comma_Next (Comma_Entry 1 (Suc delta) (10*d+9-h-8))))"
proof -
  have residual: "h=H-comma_period_displacement f orbit n"
    and positive: "(if f<9 then 1 else 0)<h"
    and terminal: "h\<le>10*d+f+(if f<9 then 1 else 0)"
    using checked by (auto simp: comma_port_prefix_validation_def)
  have valid: "1\<le>h" "h\<le>540" using positive residual source_extent by arith+
  have digit: "d=(10-h mod 10) mod 10"
    using comma_port_validation_refines_prefix
      [OF sector source_extent source_digit source_chart checked] by simp
  show ?thesis
  proof (cases "f<9")
    case True
    have bound: "h\<le>10*d+f+1" using terminal True by simp
    have exact: "h+(10*d+f+1-h)=10*d+f+1" using bound by arith
    show ?thesis using comma_vieta_ordinary_terminal(1)
      [OF sector(1) True valid digit exact, where r=r and delta=delta] True by simp
  next
    case False
    have nine: "f=9" using sector False by arith
    have bound: "h\<le>10*d+9" using terminal nine by simp
    have exact: "h+(10*d+9-h)=10*d+9" using bound by arith
    show ?thesis using comma_vieta_sector_nine_terminal(1)
      [OF valid digit exact, where r=r and delta=delta] False nine by simp
  qed
qed

text \<open>The pair field is an oriented projection, not a second semantic
coordinate. Swapping gaps preserves the sum and reverses the difference.\<close>

lemma comma_root_pair_reconstruction:
  fixes a b :: int
  shows "((a+b)+(a-b)) div 2=a" "((a+b)-(a-b)) div 2=b"
  by (simp_all add: algebra_simps)

lemma comma_root_pair_reflection:
  fixes a b :: int
  shows "b+a=a+b" "b-a=-(a-b)"
  by simp_all

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_port_local_laws_checked comma_port_local_law
      comma_port_occurrence_admission comma_port_pumped_first_hit
      comma_port_last_row comma_port_phase_inverse_checked comma_port_actual_previous
      comma_port_pump_refines_ordered_roots comma_port_weighted_cycles_checked
      comma_port_weighted_cycle comma_port_weighted_locator_coverage
      comma_port_validation_guards
      comma_port_validation_refines_prefix comma_port_validation_terminal
      comma_root_pair_reconstruction comma_root_pair_reflection})
    then () else error "Comma root pair port depends on an oracle";
\<close>
end
