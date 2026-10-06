theory Comma_Temporal_Action
  imports Comma_Even_Port_Action
begin

text \<open>The complete weighted port trace has an exact cycle factorization.
Only its bounded remainder is iterated; the cycle count is an arithmetic
weight, not a retained event word. The source port may be zero, so the proof
starts with one authenticated transition before applying the punctured-cycle
theorem.\<close>

lemma comma_port_action_power_offset:
  "comma_port_action_power f n (d,w) =
    (fst (comma_port_weighted_trace f d n),
      w + snd (comma_port_weighted_trace f d n))"
proof (induction n)
  case 0
  then show ?case by (simp add: comma_port_action_power_def)
next
  case (Suc n)
  have successor: "comma_port_action_power f (Suc n) (d,w) =
    comma_port_action f (comma_port_action_power f n (d,w))"
    by (simp add: comma_port_action_power_def)
  obtain a b where trace: "comma_port_weighted_trace f d n = (a,b)"
    by (cases "comma_port_weighted_trace f d n") auto
  show ?case
    by (simp only: successor Suc.IH trace comma_port_action_def
        comma_port_weighted_trace.simps; simp)
qed

lemma comma_port_action_power_add:
  "comma_port_action_power f (m+n) s =
    comma_port_action_power f n (comma_port_action_power f m s)"
proof (induction n)
  case 0
  then show ?case by (simp add: comma_port_action_power_def)
next
  case (Suc n)
  have exponent: "m+Suc n=Suc (m+n)" by simp
  have left: "comma_port_action_power f (m+Suc n) s =
      comma_port_action f (comma_port_action_power f (m+n) s)"
    by (simp only: exponent; simp add: comma_port_action_power_def)
  have right: "comma_port_action_power f (Suc n)
      (comma_port_action_power f m s) =
      comma_port_action f (comma_port_action_power f n
        (comma_port_action_power f m s))"
    by (simp add: comma_port_action_power_def)
  show ?case by (simp only: left right Suc.IH)
qed

lemma comma_port_action_cycle_offset:
  assumes sector: "1\<le>f" "f\<le>9"
    and digit: "1\<le>d" "d\<le>9"
  shows "comma_port_action_power f (comma_port_cycle_length f d) (d,w) =
    (d,w+comma_finite_period f d div 10)"
proof -
  have cycle:
    "comma_port_weighted_trace f d (comma_port_cycle_length f d) =
      (d,comma_finite_period f d div 10)"
    using comma_port_weighted_cycle[OF sector digit] by blast
  show ?thesis
    by (simp only: comma_port_action_power_offset cycle fst_conv snd_conv)
qed

lemma comma_port_action_cycle_multiple:
  assumes sector: "1\<le>f" "f\<le>9"
    and digit: "1\<le>d" "d\<le>9"
  shows "comma_port_action_power f
      (c*comma_port_cycle_length f d) (d,w) =
    (d,w+c*(comma_finite_period f d div 10))"
proof (induction c)
  case 0
  then show ?case by (simp add: comma_port_action_power_def)
next
  case (Suc c)
  have previous: "comma_port_action_power f
      (c*comma_port_cycle_length f d) (d,w)=
      (d,w+c*(comma_finite_period f d div 10))"
    using Suc.IH by blast
  have split: "Suc c*comma_port_cycle_length f d=
      c*comma_port_cycle_length f d+comma_port_cycle_length f d"
    by (simp add: algebra_simps)
  have cycle: "comma_port_action_power f (comma_port_cycle_length f d)
      (d,w+c*(comma_finite_period f d div 10))=
      (d,w+c*(comma_finite_period f d div 10)+
        comma_finite_period f d div 10)"
    by (rule comma_port_action_cycle_offset[OF sector digit])
  show ?case
    by (simp only: split comma_port_action_power_add previous cycle;
        simp add: algebra_simps)
qed

lemma comma_port_next_admitted:
  assumes sector: "1\<le>f" "f\<le>9" and digit: "d\<le>9"
  shows "1\<le>comma_port_next f d \<and> comma_port_next f d\<le>9"
proof (cases "d=0")
  case True
  have positive: "0<10-f" and below: "10-f<10" using sector by arith+
  have next_eq: "comma_port_next f d=10-f"
    using True positive below
    by (simp add: comma_port_next_def comma_port_previous_def mod_less)
  then show ?thesis using positive below by arith
next
  case False
  have positive_digit: "1\<le>d" using digit False by arith
  have law: "comma_port_local_law f d"
    by (rule comma_port_local_law[OF sector positive_digit digit])
  show ?thesis using law by (auto simp: comma_port_local_law_def)
qed

definition comma_port_weighted_factorized ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat\<times>nat" where
  "comma_port_weighted_factorized f d n =
    (if n=0 then (d,0) else
    let d1=comma_port_next f d;
         L=comma_port_cycle_length f d1;
         m=n-1;
         c=m div L;
         r=m mod L;
         P=comma_finite_period f d1 div 10;
         tail=comma_port_weighted_trace f d1 r
     in (fst tail,comma_port_dwell f d+c*P+snd tail))"

theorem comma_port_weighted_temporal_factorization:
  assumes sector: "1\<le>f" "f\<le>9"
    and digit: "d\<le>9" and positive: "0<n"
  shows "comma_port_weighted_trace f d n =
      comma_port_weighted_factorized f d n"
proof -
  let ?d1 = "comma_port_next f d"
  let ?L = "comma_port_cycle_length f ?d1"
  let ?m = "n-1"
  let ?c = "?m div ?L"
  let ?r = "?m mod ?L"
  let ?P = "comma_finite_period f ?d1 div 10"
  have first_bounds: "1\<le>?d1" "?d1\<le>9"
    using comma_port_next_admitted[OF sector digit] by blast+
  have cycle_multiple:
    "comma_port_action_power f (?c*?L) (?d1,w)=(?d1,w+?c*?P)" for w
    using comma_port_action_cycle_multiple[OF sector first_bounds] by blast
  have remainder: "comma_port_action_power f ?r (?d1,w)=
    (fst (comma_port_weighted_trace f ?d1 ?r),
      w+snd (comma_port_weighted_trace f ?d1 ?r))" for w
    by (rule comma_port_action_power_offset)
  have m_split: "?m=?c*?L+?r"
    using div_mult_mod_eq[of ?m ?L] by (simp add: mult.commute)
  have n_split: "n=1+(?c*?L+?r)"
    using positive m_split by (cases n) auto
  have startup:
    "comma_port_action_power f 1 (d,0)=(?d1,comma_port_dwell f d)"
    using comma_port_action_power_trace[of f 1 d]
    by (simp add: comma_port_weighted_trace.simps)
  have split_action: "comma_port_action_power f n (d,0)=
      comma_port_action_power f (1+(?c*?L+?r)) (d,0)"
    by (rule arg_cong[OF n_split])
  have joined:
    "comma_port_action_power f n (d,0)=
      (fst (comma_port_weighted_trace f ?d1 ?r),
        comma_port_dwell f d+?c*?P+
          snd (comma_port_weighted_trace f ?d1 ?r))"
    by (subst split_action)
      (simp only: comma_port_action_power_add startup cycle_multiple remainder)
  have trace: "comma_port_weighted_trace f d n =
      (fst (comma_port_weighted_trace f ?d1 ?r),
        comma_port_dwell f d+?c*?P+
          snd (comma_port_weighted_trace f ?d1 ?r))"
    using comma_port_action_power_trace[of f n d] joined by simp
  have nonzero: "n\<noteq>0" using positive by arith
  show ?thesis
    using trace by (simp add: comma_port_weighted_factorized_def Let_def nonzero)
qed

lemma comma_port_weighted_factorized_remainder:
  assumes sector: "1\<le>f" "f\<le>9"
    and digit: "d\<le>9" and positive: "0<n"
  shows "(n-1) mod comma_port_cycle_length f (comma_port_next f d) <
      comma_port_cycle_length f (comma_port_next f d)"
    and "comma_port_cycle_length f (comma_port_next f d)\<le>9"
proof -
  have next_bounds: "1\<le>comma_port_next f d" "comma_port_next f d\<le>9"
    using comma_port_next_admitted[OF sector digit] by blast+
  have cycle: "0<comma_port_cycle_length f (comma_port_next f d)"
      "comma_port_cycle_length f (comma_port_next f d)\<le>9"
    using comma_port_weighted_cycle[OF sector next_bounds] by blast+
  show "(n-1) mod comma_port_cycle_length f (comma_port_next f d) <
      comma_port_cycle_length f (comma_port_next f d)"
    using cycle by simp
  show "comma_port_cycle_length f (comma_port_next f d)\<le>9"
    by (rule cycle(2))
qed

lemma comma_cycle_length_catalog_small:
  assumes sector: "1\<le>f" "f\<le>9"
  shows "comma_cycle_length f\<in>{2,5,10}"
proof -
  have checked: "\<forall>x\<in>set [1,2,3,4,5,6,7,8,9].
    comma_cycle_length x\<in>{2,5,10}"
    by code_simp
  have member: "f\<in>set [1,2,3,4,5,6,7,8,9]"
    using sector by (auto; arith)
  show ?thesis using checked member by blast
qed

lemma comma_port_cycle_length_divides_180:
  assumes sector: "1\<le>f" "f\<le>9" and digit: "1\<le>d" "d\<le>9"
  shows "comma_port_cycle_length f d\<in>{1,2,4,5,9}"
    and "comma_port_cycle_length f d dvd 180"
proof -
  have base: "comma_cycle_length f\<in>{2,5,10}"
    by (rule comma_cycle_length_catalog_small[OF sector])
  then consider (two) "comma_cycle_length f=2" | (five) "comma_cycle_length f=5"
    | (ten) "comma_cycle_length f=10" by auto
  then show "comma_port_cycle_length f d\<in>{1,2,4,5,9}"
  proof cases
    case two
    then show ?thesis by (cases "d mod 5=0")
      (simp_all add: comma_port_cycle_length_def)
  next
    case five
    then show ?thesis by (cases "d mod 2=0")
      (simp_all add: comma_port_cycle_length_def)
  next
    case ten
    then show ?thesis by (simp add: comma_port_cycle_length_def)
  qed
  then show "comma_port_cycle_length f d dvd 180"
    by (auto simp: dvd_eq_mod_eq_0)
qed

definition comma_port_temporal_iterate :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_port_temporal_iterate f n d=fst (comma_port_action_power f n (d,0))"

lemma comma_port_temporal_iterate_period_180:
  assumes sector: "1\<le>f" "f\<le>9" and digit: "d\<le>9" and positive: "0<n"
  shows "comma_port_temporal_iterate f (n+180) d=
    comma_port_temporal_iterate f n d"
proof -
  let ?d1 = "comma_port_next f d"
  let ?L = "comma_port_cycle_length f ?d1"
  have first_bounds: "1\<le>?d1" "?d1\<le>9"
    using comma_port_next_admitted[OF sector digit] by blast+
  have divides: "?L dvd 180"
    by (rule comma_port_cycle_length_divides_180(2)[OF sector first_bounds])
  have rem_same: "(n-1+180) mod ?L=(n-1) mod ?L"
  proof -
    have zero: "180 mod ?L=0"
      using divides by (simp add: mod_eq_0_iff_dvd)
    show ?thesis by (subst mod_add_eq[symmetric];
      simp only: zero add_0_right mod_mod_trivial)
  qed
  have exponent_shift: "n+180-1=n-1+180" using positive by arith
  have rem_same_shifted: "(n+180-1) mod ?L=(n-1) mod ?L"
    by (simp only: exponent_shift rem_same)
  have factor_n: "comma_port_weighted_trace f d n=
      comma_port_weighted_factorized f d n"
    by (rule comma_port_weighted_temporal_factorization[OF sector digit positive])
  have factor_next: "comma_port_weighted_trace f d (n+180)=
      comma_port_weighted_factorized f d (n+180)"
    by (rule comma_port_weighted_temporal_factorization[OF sector digit]; arith)
  show ?thesis
    using factor_n factor_next rem_same positive
    by (simp add: comma_port_temporal_iterate_def comma_port_action_power_trace
      comma_port_weighted_factorized_def Let_def rem_same_shifted)
qed

text \<open>The following 181 labels preserve only the exact port endpoint.
They neither identify exact dwell weights nor summarize the harmonic/reset
observer. Their application theorem is not a native-decade or branch-safety
refinement, and the cardinality theorem is not a Moore-minimality theorem.\<close>

datatype comma_port_time_class = Comma_Port_Time_Zero | Comma_Port_Time_Pos nat

definition comma_port_time_class_of :: "nat \<Rightarrow> comma_port_time_class" where
  "comma_port_time_class_of n =
    (if n=0 then Comma_Port_Time_Zero else Comma_Port_Time_Pos ((n-1) mod 180))"

fun comma_port_time_compose ::
  "comma_port_time_class \<Rightarrow> comma_port_time_class \<Rightarrow>
   comma_port_time_class" where
  "comma_port_time_compose Comma_Port_Time_Zero x=x"
| "comma_port_time_compose x Comma_Port_Time_Zero=x"
| "comma_port_time_compose (Comma_Port_Time_Pos a) (Comma_Port_Time_Pos b)=
    Comma_Port_Time_Pos ((a+b+1) mod 180)"

definition comma_port_time_carrier :: "comma_port_time_class set" where
  "comma_port_time_carrier={Comma_Port_Time_Zero} \<union>
    Comma_Port_Time_Pos ` {0..<180}"

lemma comma_port_time_carrier_card:
  "card comma_port_time_carrier=181"
proof -
  have injective: "inj_on Comma_Port_Time_Pos {0..<180}"
    by (auto simp: inj_on_def)
  have size: "card (Comma_Port_Time_Pos ` {0..<180})=180"
    by (subst card_image[OF injective]) simp
  have finite_image: "finite (Comma_Port_Time_Pos ` {0..<180})" by simp
  have absent: "Comma_Port_Time_Zero \<notin> Comma_Port_Time_Pos ` {0..<180}"
    by auto
  show ?thesis using size finite_image absent
    by (simp add: comma_port_time_carrier_def)
qed

lemma comma_port_time_class_of_admitted:
  "comma_port_time_class_of n \<in> comma_port_time_carrier"
  by (cases n) (auto simp: comma_port_time_class_of_def comma_port_time_carrier_def)

lemma comma_port_time_class_add:
  "comma_port_time_class_of (m+n)=
    comma_port_time_compose (comma_port_time_class_of m) (comma_port_time_class_of n)"
proof -
  have residues: "Suc (a mod 180+b mod 180) mod 180=Suc (a+b) mod 180"
    for a b :: nat
  proof -
    have "(a mod 180+b mod 180+1) mod 180=(a+b+1) mod 180"
      by (rule mod_add_cong[OF mod_add_eq refl])
    then show ?thesis by simp
  qed
  show ?thesis by (cases m; cases n;
    simp add: comma_port_time_class_of_def residues)
qed

lemma comma_port_time_representative:
  assumes "t\<in>comma_port_time_carrier"
  shows "\<exists>n. comma_port_time_class_of n=t"
proof (cases t)
  case Comma_Port_Time_Zero
  then show ?thesis by (rule_tac x=0 in exI)
    (simp add: comma_port_time_class_of_def)
next
  case (Comma_Port_Time_Pos r)
  have bound: "r<180" using assms Comma_Port_Time_Pos
    by (auto simp: comma_port_time_carrier_def)
  show ?thesis by (rule_tac x="Suc r" in exI)
    (simp add: comma_port_time_class_of_def Comma_Port_Time_Pos bound)
qed

lemma comma_port_time_compose_assoc:
  assumes "a\<in>comma_port_time_carrier" "b\<in>comma_port_time_carrier"
    "c\<in>comma_port_time_carrier"
  shows "comma_port_time_compose a (comma_port_time_compose b c)=
    comma_port_time_compose (comma_port_time_compose a b) c"
proof -
  obtain i where a: "comma_port_time_class_of i=a"
    using comma_port_time_representative[OF assms(1)] by blast
  obtain j where b: "comma_port_time_class_of j=b"
    using comma_port_time_representative[OF assms(2)] by blast
  obtain k where c: "comma_port_time_class_of k=c"
    using comma_port_time_representative[OF assms(3)] by blast
  show ?thesis unfolding a[symmetric] b[symmetric] c[symmetric]
    by (simp only: comma_port_time_class_add[symmetric] add.assoc)
qed

lemma comma_port_temporal_iterate_period_180_multiple:
  assumes sector: "1\<le>f" "f\<le>9" and digit: "d\<le>9"
    and positive: "0<n"
  shows "comma_port_temporal_iterate f (n+180*k) d=
    comma_port_temporal_iterate f n d"
proof (induction k)
  case 0
  then show ?case by simp
next
  case (Suc k)
  have prior_positive: "0<n+180*k" using positive by arith
  have exponent: "n+180*Suc k=(n+180*k)+180" by arith
  have shift:
    "comma_port_temporal_iterate f ((n+180*k)+180) d=
      comma_port_temporal_iterate f (n+180*k) d"
    by (rule comma_port_temporal_iterate_period_180[OF sector digit];
        use prior_positive in arith)
  show ?case by (simp only: exponent shift Suc.IH)
qed

definition comma_port_time_apply ::
  "nat \<Rightarrow> nat \<Rightarrow> comma_port_time_class \<Rightarrow> nat" where
  "comma_port_time_apply f d t = (case t of
      Comma_Port_Time_Zero \<Rightarrow> d
    | Comma_Port_Time_Pos r \<Rightarrow> comma_port_temporal_iterate f (Suc r) d)"

theorem comma_port_time_apply_class_of_exact:
  assumes sector: "1\<le>f" "f\<le>9" and digit: "d\<le>9"
  shows "comma_port_time_apply f d (comma_port_time_class_of n)=
    comma_port_temporal_iterate f n d"
proof (cases n)
  case 0
  then show ?thesis
    by (simp add: comma_port_time_apply_def comma_port_time_class_of_def
        comma_port_temporal_iterate_def comma_port_action_power_def)
next
  case (Suc m)
  let ?q = "m div 180"
  let ?r = "m mod 180"
  have decomposition: "Suc m=Suc ?r+180*?q"
    using div_mult_mod_eq[of m 180] by (simp add: mult.commute)
  have class_key:
    "comma_port_time_class_of (Suc m)=Comma_Port_Time_Pos ?r"
    by (simp add: comma_port_time_class_of_def)
  have reduced:
    "comma_port_temporal_iterate f (Suc ?r+180*?q) d=
      comma_port_temporal_iterate f (Suc ?r) d"
    by (rule comma_port_temporal_iterate_period_180_multiple[OF sector digit];
        simp)
  have applied:
    "comma_port_time_apply f d (comma_port_time_class_of (Suc m))=
      comma_port_temporal_iterate f (Suc ?r) d"
    using class_key by (simp add: comma_port_time_apply_def)
  have literal:
    "comma_port_temporal_iterate f (Suc m) d=
      comma_port_temporal_iterate f (Suc ?r) d"
    using decomposition reduced by (simp only: decomposition reduced)
  show ?thesis using Suc applied literal by simp
qed

ML \<open>
  val checked = @{thms comma_port_action_power_offset
    comma_port_weighted_temporal_factorization comma_port_time_class_add
    comma_port_time_compose_assoc comma_port_temporal_iterate_period_180
    comma_port_temporal_iterate_period_180_multiple
    comma_port_time_apply_class_of_exact};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Temporal action depends on an oracle";
\<close>
end
