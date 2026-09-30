theory Comma_Decade_Orbit_Quotient
  imports Comma_Fast_Control.Comma_Fast_Kernel
    Comma_Decade_Residual_Core.Comma_Decade_Residual_Core
begin

text \<open>Subtraction is signed before reduction modulo 460. Natural
truncated subtraction would not give the sector-1 orbit invariant.\<close>

definition comma_digit_orbit_sum :: "nat \<Rightarrow> int" where
  "comma_digit_orbit_sum d=5*(int d)^2-4*int d"

definition comma_offset_orbit :: "nat \<Rightarrow> nat" where
  "comma_offset_orbit x=nat ((int x-comma_digit_orbit_sum (x mod 10)) mod 460) div 10"

lemma comma_digit_orbit_sum_step:
  "comma_digit_orbit_sum (Suc d)-comma_digit_orbit_sum d=10*int d+1"
  by (simp add: comma_digit_orbit_sum_def power2_eq_square algebra_simps)

lemma comma_digit_orbit_sum_wrap:
  "comma_digit_orbit_sum 10=460" "comma_digit_orbit_sum 0=0"
  by (simp_all add: comma_digit_orbit_sum_def)

lemma comma_offset_orbit_bound:
  "comma_offset_orbit x<46"
proof -
  have bound: "(int x-comma_digit_orbit_sum (x mod 10)) mod 460<460" by simp
  have "nat ((int x-comma_digit_orbit_sum (x mod 10)) mod 460)<460"
    using bound by simp
  then show ?thesis unfolding comma_offset_orbit_def by arith
qed

lemma comma_offset_orbit_step:
  "comma_offset_orbit (x+10*(x mod 10)+1)=comma_offset_orbit x"
proof -
  let ?d = "x mod 10"
  have digit: "?d<10" by simp
  have next_digit: "(x+10*?d+1) mod 10=(?d+1) mod 10"
    by (simp add: mod_add_left_eq mod_Suc_eq)
  show ?thesis
  proof (cases "?d=9")
    case True
    have wrapped: "(x+91) mod 10=0"
      using next_digit True by (simp add: add.commute)
    have residual: "(int x+91) mod 460=(int x-369) mod 460"
    proof -
      have shift: "int x+91=(int x-369)+460" by simp
      show ?thesis by (subst shift) (rule mod_add_self2)
    qed
    show ?thesis
      by (simp add: comma_offset_orbit_def True wrapped comma_digit_orbit_sum_def residual algebra_simps)
  next
    case False
    have bound: "?d+1<10" using digit False by arith
    have difference: "comma_digit_orbit_sum (?d+1)-comma_digit_orbit_sum ?d=10*int ?d+1"
      using comma_digit_orbit_sum_step[of ?d] by simp
    have step: "comma_digit_orbit_sum (?d+1)=comma_digit_orbit_sum ?d+10*int ?d+1"
      using difference by linarith
    have advanced: "(x+10*?d+1) mod 10=?d+1"
      using next_digit mod_less[OF bound] by simp
    show ?thesis
      by (simp only: comma_offset_orbit_def advanced step;
        simp add: algebra_simps)
  qed
qed

definition comma_offset_representatives :: "nat list" where
  "comma_offset_representatives =
    [0,10,20,30,40,50,60,70,80,90,9,19,29,39,49,59,69,79,8,18,28,38,48,58,68,
     7,17,27,37,47,57,6,16,26,36,46,5,15,25,35,4,14,24,3,13,2]"

definition comma_offset_representative :: "nat \<Rightarrow> nat" where
  "comma_offset_representative x=comma_offset_representatives!comma_offset_orbit x"

lemma comma_offset_representatives_checked:
  "list_all (\<lambda>i. comma_offset_representatives!i\<le>90 \<and>
    comma_offset_orbit (comma_offset_representatives!i)=i) [0..<46]"
  by (tactic \<open>
    simp_tac (Comma_Entry_Arithmetic.natural_context @{context} addsimps
      @{thms comma_offset_representatives_def comma_offset_orbit_def comma_digit_orbit_sum_def
        power2_eq_square list_all_Nil_iff list_all_Cons_iff upt_rec nth_Cons'
        of_nat_numeral of_nat_0 of_nat_1 zmod_zminus1_eq_if zmod_zminus2_eq_if}) 1
  \<close>)

lemma comma_offset_representative_admitted:
  "comma_offset_representative x\<le>90"
  "comma_offset_orbit (comma_offset_representative x)=comma_offset_orbit x"
  using comma_offset_representatives_checked comma_offset_orbit_bound[of x]
  by (auto simp: list_all_iff comma_offset_representative_def)

lemma comma_sector_one_period:
  assumes "d<10"
  shows "comma_finite_period_fast 1 d=460"
proof -
  have "comma_finite_period_fast 1 d=(replicate 10 460)!d"
    by (simp add: comma_finite_period_fast_def eval_nat_numeral)
  then show ?thesis using assms by simp
qed

lemma comma_sector_one_phase:
  "comma_entry_alphabet_phase 1 r 0 x=(r mod 924+919) mod 22"
proof -
  have period: "comma_finite_period_fast 1 (x mod 10)=460"
    by (rule comma_sector_one_period) simp
  show ?thesis
    by (simp only: comma_entry_alphabet_phase_def period;
      simp add: comma_short_period_def)
qed

definition comma_offset_endpoint_check :: bool where
  "comma_offset_endpoint_check =
    list_all (\<lambda>x. list_all (\<lambda>k.
      comma_entry_alphabet_endpoint 1 x k=
        comma_entry_alphabet_endpoint 1 (comma_offset_representative x) k)
      [0..<22]) [0..<91]"

text \<open>The representative data above supplies no transition. This finite
check recomputes sector endpoints from the existing checked arithmetic owner.
Its domain has 22 local phases, not 924 full decade trajectories.\<close>
lemma comma_offset_endpoint_checked: "comma_offset_endpoint_check"
  by (tactic \<open>
    let
      val kernel = Comma_Fast_Kernel.make @{context}
      val context = #context kernel addsimps
        @{thms comma_offset_endpoint_check_def comma_offset_representative_def
          comma_offset_representatives_def comma_offset_orbit_def comma_digit_orbit_sum_def
          power2_eq_square}
    in simp_tac context 1 end
  \<close>)

lemma comma_offset_endpoint_representative:
  assumes "x\<le>90" "k<22"
  shows "comma_entry_alphabet_endpoint 1 x k=
    comma_entry_alphabet_endpoint 1 (comma_offset_representative x) k"
  using comma_offset_endpoint_checked assms
  by (auto simp: comma_offset_endpoint_check_def list_all_iff)

lemma comma_sector_one_orbit_congruent:
  assumes x: "x\<le>90" and y: "y\<le>90"
    and same: "comma_offset_orbit x=comma_offset_orbit y"
  shows "comma_fast_sector_target r (Comma_Entry 1 0 x)=
    comma_fast_sector_target r (Comma_Entry 1 0 y)"
proof -
  have representatives: "comma_offset_representative x=comma_offset_representative y"
    using same by (simp only: comma_offset_representative_def)
  have endpoint: "comma_entry_alphabet_endpoint 1 x ((r mod 924+919) mod 22)=
    comma_entry_alphabet_endpoint 1 y ((r mod 924+919) mod 22)"
    using comma_offset_endpoint_representative[OF x, of "(r mod 924+919) mod 22"]
      comma_offset_endpoint_representative[OF y, of "(r mod 924+919) mod 22"]
    by (simp add: representatives)
  show ?thesis using x y
    by (simp only: comma_sector_entry_alphabet comma_sector_one_phase endpoint;
      simp)
qed

theorem comma_decade_control_orbit_congruent:
  assumes "x\<le>90" "y\<le>90" "comma_offset_orbit x=comma_offset_orbit y"
  shows "comma_fast_decade_control (Comma_Decade r x)=
    comma_fast_decade_control (Comma_Decade r y)"
proof -
  have sectors: "comma_fast_sector_target r (Comma_Entry 1 0 x)=
    comma_fast_sector_target r (Comma_Entry 1 0 y)"
    by (rule comma_sector_one_orbit_congruent[OF assms])
  have rounds: "comma_fast_round_aux 9 r (Comma_Entry 1 0 x)=
    comma_fast_round_aux 9 r (Comma_Entry 1 0 y)"
    using comma_fast_round_aux_eval[of 9 r "Comma_Entry 1 0 x"]
      comma_fast_round_aux_eval[of 9 r "Comma_Entry 1 0 y"]
    by (simp only: sectors)
  show ?thesis by (simp only: comma_fast_decade_control.simps rounds)
qed

lemma comma_decade_control_orbit_representative:
  assumes "x\<le>90"
  shows "comma_fast_decade_control (Comma_Decade r x)=
    comma_fast_decade_control (Comma_Decade r (comma_offset_representative x))"
  by (rule comma_decade_control_orbit_congruent[OF assms
    comma_offset_representative_admitted(1)])
    (simp only: comma_offset_representative_admitted(2))

text \<open>Candidate summaries may be transported only when both labels agree.
Control equality alone never authenticates a supplied height or terminal table.\<close>
lemma comma_decade_summary_step_orbit_transport:
  assumes offset: "x\<le>90"
    and height: "h (Comma_Decade r x)=h (Comma_Decade r (comma_offset_representative x))"
    and terminal: "t (Comma_Decade r x)=t (Comma_Decade r (comma_offset_representative x))"
  shows "comma_fast_decade_summary_step h t (Comma_Decade r x)=
    comma_fast_decade_summary_step h t (Comma_Decade r (comma_offset_representative x))"
  by (simp only: comma_fast_decade_summary_step_def
    comma_decade_control_orbit_representative[OF offset] height terminal)

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_decade_control_orbit_representative
      comma_decade_summary_step_orbit_transport comma_offset_orbit_bound comma_offset_orbit_step
      comma_offset_representatives_checked comma_offset_endpoint_checked
      comma_decade_control_orbit_congruent})
    then () else error "Decade orbit quotient depends on an oracle";
\<close>
end
