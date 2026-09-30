theory Comma_Pair_Field
  imports Comma_Root_Pair_Port
begin

text \<open>This reversible pair encoding retains the raw predecessor,
including zero, until the second physical root has been tested. There is no
puncture bit: it is derived from the right field. Puncturing belongs only to
the existing next authenticated port. This is local arithmetic, not Entry
admission, a future branch classifier, or a reduction to cycle ActionIDs.\<close>

datatype comma_pair_field = Comma_Pair_Field nat nat

fun comma_pair_sum :: "comma_pair_field \<Rightarrow> nat" where
  "comma_pair_sum (Comma_Pair_Field s difference)=s"

fun comma_pair_difference :: "comma_pair_field \<Rightarrow> nat" where
  "comma_pair_difference (Comma_Pair_Field s difference)=difference"

definition comma_pair_encode :: "nat \<Rightarrow> nat \<Rightarrow> comma_pair_field" where
  "comma_pair_encode f d =
    (let p=comma_port_previous f d in Comma_Pair_Field (d+p) (d+9-p))"

definition comma_pair_left_digit :: "comma_pair_field \<Rightarrow> nat" where
  "comma_pair_left_digit X =
    (comma_pair_sum X+comma_pair_difference X-9) div 2"

definition comma_pair_right_digit :: "comma_pair_field \<Rightarrow> nat" where
  "comma_pair_right_digit X =
    (comma_pair_sum X+9-comma_pair_difference X) div 2"

definition comma_pair_sector :: "comma_pair_field \<Rightarrow> nat" where
  "comma_pair_sector X=(comma_pair_difference X+1) mod 10"

definition comma_pair_decode :: "comma_pair_field \<Rightarrow> nat\<times>nat" where
  "comma_pair_decode X=(comma_pair_sector X,comma_pair_left_digit X)"

definition comma_pair_admitted :: "comma_pair_field \<Rightarrow> bool" where
  "comma_pair_admitted X =
    (1\<le>comma_pair_sector X \<and> comma_pair_sector X\<le>9 \<and>
     1\<le>comma_pair_left_digit X \<and> comma_pair_left_digit X\<le>9 \<and>
     comma_pair_encode (comma_pair_sector X) (comma_pair_left_digit X)=X)"

definition comma_pair_encoding_law :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "comma_pair_encoding_law f d =
    (let X=comma_pair_encode f d in
      comma_pair_decode X=(f,d) \<and>
      comma_pair_right_digit X=comma_port_previous f d \<and>
      comma_pair_right_digit X\<le>9 \<and>
      comma_pair_sum X\<le>18 \<and> comma_pair_difference X\<le>18 \<and>
      (comma_pair_sum X+comma_pair_difference X-9) mod 2=0 \<and>
      (comma_pair_sum X+9-comma_pair_difference X) mod 2=0 \<and>
      (comma_pair_right_digit X=0)=(d=f))"

lemma comma_pair_encoding_laws_checked:
  "list_all (\<lambda>f. list_all (comma_pair_encoding_law f) [1..<10]) [1..<10]"
  by (tactic \<open>simp_tac
    (Comma_Entry_Arithmetic.natural_context @{context} addsimps
      @{thms list_all_Nil_iff list_all_Cons_iff upt_rec
        comma_pair_encoding_law_def comma_pair_encode_def comma_pair_decode_def
        comma_pair_left_digit_def comma_pair_right_digit_def comma_pair_sector_def
        comma_pair_sum.simps comma_pair_difference.simps comma_port_previous_def Let_def}) 1\<close>)

lemma comma_pair_encoding_law:
  assumes "1\<le>f" "f\<le>9" "1\<le>d" "d\<le>9"
  shows "comma_pair_encoding_law f d"
  using comma_pair_encoding_laws_checked assms by (auto simp: list_all_iff)

theorem comma_pair_field_decode:
  assumes "1\<le>f" "f\<le>9" "1\<le>d" "d\<le>9"
  shows "comma_pair_decode (comma_pair_encode f d)=(f,d)"
    "comma_pair_right_digit (comma_pair_encode f d)=comma_port_previous f d"
  using comma_pair_encoding_law[OF assms]
  by (auto simp: comma_pair_encoding_law_def Let_def)

lemma comma_pair_encoded_admitted:
  assumes "1\<le>f" "f\<le>9" "1\<le>d" "d\<le>9"
  shows "comma_pair_admitted (comma_pair_encode f d)"
  using comma_pair_field_decode(1)[OF assms] assms
  by (auto simp: comma_pair_decode_def comma_pair_admitted_def)

theorem comma_pair_field_encode:
  assumes "comma_pair_admitted X"
  shows "comma_pair_encode (fst (comma_pair_decode X)) (snd (comma_pair_decode X))=X"
  using assms by (simp add: comma_pair_admitted_def comma_pair_decode_def)

theorem comma_pair_field_bijection:
  "bij_betw (\<lambda>(f,d). comma_pair_encode f d)
    ({1..9}\<times>{1..9}) {X. comma_pair_admitted X}"
proof (unfold bij_betw_def, intro conjI)
  show "inj_on (\<lambda>(f,d). comma_pair_encode f d) ({1..9}\<times>{1..9})"
  proof (rule inj_onI)
    fix x y
    assume x: "x\<in>{1..9}\<times>{1..9}" and y: "y\<in>{1..9}\<times>{1..9}"
      and equal: "(case x of (f,d) \<Rightarrow> comma_pair_encode f d)=
        (case y of (f,d) \<Rightarrow> comma_pair_encode f d)"
    obtain f d where x_pair: "x=(f,d)" by (cases x) auto
    obtain a b where y_pair: "y=(a,b)" by (cases y) auto
    have x_bounds: "1\<le>f" "f\<le>9" "1\<le>d" "d\<le>9"
      using x by (simp_all add: x_pair)
    have y_bounds: "1\<le>a" "a\<le>9" "1\<le>b" "b\<le>9"
      using y by (simp_all add: y_pair)
    have decoded: "(f,d)=(a,b)"
      using arg_cong[OF equal, of comma_pair_decode]
        comma_pair_field_decode(1)[OF x_bounds]
        comma_pair_field_decode(1)[OF y_bounds]
      by (simp only: x_pair y_pair prod.case)
    show "x=y" using decoded by (simp only: x_pair y_pair)
  qed
  show "(\<lambda>(f,d). comma_pair_encode f d) ` ({1..9}\<times>{1..9}) =
    {X. comma_pair_admitted X}"
  proof (rule set_eqI, intro iffI)
    fix X assume "X\<in>(\<lambda>(f,d). comma_pair_encode f d) ` ({1..9}\<times>{1..9})"
    then show "X\<in>{X. comma_pair_admitted X}"
      using comma_pair_encoded_admitted by auto
  next
    fix X assume "X\<in>{X. comma_pair_admitted X}"
    then have bounds: "(comma_pair_sector X,comma_pair_left_digit X)\<in>{1..9}\<times>{1..9}"
      and encoded: "comma_pair_encode (comma_pair_sector X) (comma_pair_left_digit X)=X"
      by (auto simp: comma_pair_admitted_def)
    show "X\<in>(\<lambda>(f,d). comma_pair_encode f d) ` ({1..9}\<times>{1..9})"
      using bounds encoded by (force intro: image_eqI)
  qed
qed

lemma comma_pair_field_bounds:
  assumes "comma_pair_admitted X"
  shows "comma_pair_sum X\<le>18" "comma_pair_difference X\<le>18"
    "comma_pair_right_digit X\<le>9"
  using comma_pair_encoding_law[of "comma_pair_sector X" "comma_pair_left_digit X"] assms
  by (auto simp: comma_pair_admitted_def comma_pair_encoding_law_def Let_def)

definition comma_pair_step :: "comma_pair_field \<Rightarrow> comma_pair_field" where
  "comma_pair_step X=comma_pair_encode (comma_pair_sector X)
    (comma_port_next (comma_pair_sector X) (comma_pair_left_digit X))"

theorem comma_pair_step_conjugate:
  assumes "1\<le>f" "f\<le>9" "1\<le>d" "d\<le>9"
  shows "comma_pair_step (comma_pair_encode f d)=comma_pair_encode f (comma_port_next f d)"
  using comma_pair_field_decode(1)[OF assms]
  by (simp add: comma_pair_step_def comma_pair_decode_def)

lemma comma_pair_step_closed:
  assumes "comma_pair_admitted X"
  shows "comma_pair_admitted (comma_pair_step X)"
proof -
  have f: "1\<le>comma_pair_sector X" "comma_pair_sector X\<le>9"
    and d: "1\<le>comma_pair_left_digit X" "comma_pair_left_digit X\<le>9"
    using assms by (auto simp: comma_pair_admitted_def)
  have law: "comma_port_local_law (comma_pair_sector X) (comma_pair_left_digit X)"
    by (rule comma_port_local_law[OF f d])
  have successor_bounds: "1\<le>comma_port_next (comma_pair_sector X) (comma_pair_left_digit X)"
    "comma_port_next (comma_pair_sector X) (comma_pair_left_digit X)\<le>9"
    using law by (auto simp: comma_port_local_law_def)
  show ?thesis using comma_pair_encoded_admitted[OF f successor_bounds]
    by (simp only: comma_pair_step_def)
qed

definition comma_pair_first_gap :: "comma_pair_field \<Rightarrow> nat" where
  "comma_pair_first_gap X=5*(comma_pair_sum X+comma_pair_difference X-9)+comma_pair_sector X"

definition comma_pair_second_gap :: "comma_pair_field \<Rightarrow> nat" where
  "comma_pair_second_gap X=5*(comma_pair_sum X+9-comma_pair_difference X)+comma_pair_sector X"

definition comma_pair_gap_law :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "comma_pair_gap_law f d = (let X=comma_pair_encode f d in
    comma_pair_first_gap X=10*d+f \<and>
    comma_pair_second_gap X=10*comma_port_previous f d+f \<and>
    comma_pair_first_gap X+comma_pair_second_gap X=10*comma_pair_sum X+2*f)"

lemma comma_pair_gap_laws_checked:
  "list_all (\<lambda>f. list_all (comma_pair_gap_law f) [1..<10]) [1..<10]"
  by (tactic \<open>simp_tac
    (Comma_Entry_Arithmetic.natural_context @{context} addsimps
      @{thms list_all_Nil_iff list_all_Cons_iff upt_rec comma_pair_gap_law_def
        comma_pair_first_gap_def comma_pair_second_gap_def comma_pair_encode_def
        comma_pair_sector_def comma_pair_sum.simps comma_pair_difference.simps
        comma_port_previous_def Let_def}) 1\<close>)

theorem comma_pair_adjacent_thresholds:
  assumes "1\<le>f" "f\<le>9" "1\<le>d" "d\<le>9"
  shows "comma_pair_first_gap (comma_pair_encode f d)=10*d+f"
    "comma_pair_second_gap (comma_pair_encode f d)=10*comma_port_previous f d+f"
    "comma_pair_first_gap (comma_pair_encode f d)+comma_pair_second_gap (comma_pair_encode f d)=
      10*comma_pair_sum (comma_pair_encode f d)+2*f"
proof -
  have law: "comma_pair_gap_law f d" using comma_pair_gap_laws_checked assms
    by (auto simp: list_all_iff)
  show "comma_pair_first_gap (comma_pair_encode f d)=10*d+f"
    "comma_pair_second_gap (comma_pair_encode f d)=10*comma_port_previous f d+f"
    "comma_pair_first_gap (comma_pair_encode f d)+comma_pair_second_gap (comma_pair_encode f d)=
      10*comma_pair_sum (comma_pair_encode f d)+2*f"
    using law by (auto simp: comma_pair_gap_law_def Let_def)
qed

lemma comma_pair_physical_zero:
  assumes "1\<le>f" "f\<le>9"
  shows "comma_pair_right_digit (comma_pair_encode f f)=0"
    "comma_pair_second_gap (comma_pair_encode f f)=f"
  using comma_pair_field_decode(2)[OF assms assms]
    comma_pair_adjacent_thresholds(2)[OF assms assms]
  by (simp_all add: comma_port_previous_def)

lemma comma_pair_gap_carry_decomposition:
  assumes "1\<le>f" "f\<le>9" "1\<le>d" "d\<le>9"
  shows "comma_pair_first_gap (comma_pair_encode f d)+comma_pair_second_gap (comma_pair_encode f d)=
    10*(comma_pair_sum (comma_pair_encode f d)+(2*f) div 10)+(2*f) mod 10"
    "(2*f) div 10\<le>1"
proof -
  have division: "10*((2*f) div 10)+(2*f) mod 10=2*f"
    using div_mult_mod_eq[of "2*f" 10]
    by (simp only: mult.commute)
  show "comma_pair_first_gap (comma_pair_encode f d)+comma_pair_second_gap (comma_pair_encode f d)=
    10*(comma_pair_sum (comma_pair_encode f d)+(2*f) div 10)+(2*f) mod 10"
    using comma_pair_adjacent_thresholds(3)[OF assms] division
    by (simp only: distrib_left; arith)
  show "(2*f) div 10\<le>1" using assms(2) by arith
qed

lemma comma_pair_zero_regression:
  "comma_pair_second_gap (comma_pair_encode 1 1)=1"
  "10*comma_port_next 1 1+1=91"
  "comma_pair_encode 1 1\<noteq>comma_pair_encode 2 1"
  by (simp_all add: comma_pair_second_gap_def comma_pair_encode_def
    comma_pair_sector_def comma_port_next_def comma_port_previous_def)

theorem comma_pair_last_row_refines:
  assumes "1\<le>f" "f\<le>9" "1\<le>d" "d\<le>9"
    "u=comma_port_low f d+10*m" "m<comma_port_dwell f d"
    "q=comma_port_dwell f d-m"
  shows "comma_vieta_row_port (comma_pair_first_gap (comma_pair_encode f d))
    (comma_pair_second_gap (comma_pair_encode f d)) (u+10*(q-1)) =
      (if comma_pair_right_digit (comma_pair_encode f d)=0 then 2 else 1,
        comma_port_low f (comma_port_next f d))"
  using comma_port_last_row[OF assms]
    comma_pair_adjacent_thresholds(1,2)[OF assms(1-4)]
    comma_pair_field_decode(2)[OF assms(1-4)]
  by simp

text \<open>The two raw fields encode all 81 ports. No claim is made here
that local cycle weights determine recursive future continuation. Absolute
exponent, physical transition weight and source authority remain separate.\<close>

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_pair_encoding_laws_checked comma_pair_field_decode
      comma_pair_field_encode comma_pair_field_bijection comma_pair_step_conjugate
      comma_pair_step_closed comma_pair_adjacent_thresholds comma_pair_physical_zero
      comma_pair_gap_carry_decomposition comma_pair_zero_regression comma_pair_last_row_refines})
    then () else error "Comma pair field depends on an oracle";
\<close>
end
