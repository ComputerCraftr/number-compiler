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

definition comma_pair_center :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_pair_center f d=(d+comma_port_previous f d) div 2 mod 5"

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

lemma comma_pair_previous_split:
  assumes "1\<le>f" "f\<le>9" "d\<le>9"
  shows "comma_port_previous f d=(if f\<le>d then d-f else d+10-f)"
proof -
  show ?thesis
  proof (cases "f\<le>d")
    case True
    have shifted: "d+10-f=(d-f)+10" using True by arith
    have remainder: "d-f<10" using assms by arith
    have modulo: "(d+10-f) mod 10=d-f"
    proof -
      have "(d+10-f) mod 10=((d-f)+10) mod 10"
        by (simp only: shifted)
      also have "...=(d-f) mod 10"
        by (rule mod_add_self2)
      also have "...=d-f" using remainder by simp
      finally show ?thesis .
    qed
    show ?thesis using True shifted modulo by (simp add: comma_port_previous_def)
  next
    case False
    have bound: "d+10-f<10" using False assms by arith
    show ?thesis using False bound by (simp add: comma_port_previous_def)
  qed
qed

lemma comma_pair_encoded_arithmetic:
  assumes "1\<le>f" "f\<le>9" "d\<le>9"
  shows "comma_pair_sum (comma_pair_encode f d)=d+comma_port_previous f d"
    "comma_pair_difference (comma_pair_encode f d)=d+9-comma_port_previous f d"
    "comma_pair_sum (comma_pair_encode f d)+comma_pair_difference (comma_pair_encode f d)-9=2*d"
    "comma_pair_sum (comma_pair_encode f d)+9-comma_pair_difference (comma_pair_encode f d)=
      2*comma_port_previous f d"
    "comma_pair_sector (comma_pair_encode f d)=f"
    "comma_pair_left_digit (comma_pair_encode f d)=d"
    "comma_pair_right_digit (comma_pair_encode f d)=comma_port_previous f d"
    "comma_port_previous f d\<le>9"
    "(comma_port_previous f d=0)=(d=f)"
proof -
  let ?p = "comma_port_previous f d"
  have previous: "?p=(if f\<le>d then d-f else d+10-f)"
    by (rule comma_pair_previous_split[OF assms])
  have p_bound: "?p\<le>9" using previous assms by (auto split: if_splits; arith)
  have p_zero: "(?p=0)=(d=f)"
    using previous assms by (auto split: if_splits; arith)
  have sum_value: "comma_pair_sum (comma_pair_encode f d)=d+?p"
    by (simp add: comma_pair_encode_def Let_def)
  have difference_value: "comma_pair_difference (comma_pair_encode f d)=d+9-?p"
    by (simp add: comma_pair_encode_def Let_def)
  have p_fits: "?p\<le>d+9" using p_bound assms by arith
  have left_numerator:
    "comma_pair_sum (comma_pair_encode f d)+comma_pair_difference (comma_pair_encode f d)-9=2*d"
    using sum_value difference_value p_fits by arith
  have right_numerator:
    "comma_pair_sum (comma_pair_encode f d)+9-comma_pair_difference (comma_pair_encode f d)=2*?p"
    using sum_value difference_value p_fits by arith
  have sector_value: "d+9-?p+1=(if d<f then f else f+10)"
    using previous assms by (auto split: if_splits; arith)
  have sector_mod: "(d+9-?p+1) mod 10=f"
  proof (cases "d<f")
    case True
    have f_bound: "f<10" using assms by arith
    show ?thesis using sector_value True f_bound by simp
  next
    case False
    have f_bound: "f<10" using assms by arith
    show ?thesis using sector_value False f_bound by (simp add: mod_add_self2)
  qed
  show "comma_pair_sum (comma_pair_encode f d)=d+comma_port_previous f d"
    using sum_value by simp
  show "comma_pair_difference (comma_pair_encode f d)=d+9-comma_port_previous f d"
    using difference_value by simp
  show "comma_pair_sum (comma_pair_encode f d)+comma_pair_difference (comma_pair_encode f d)-9=2*d"
    using left_numerator by simp
  show "comma_pair_sum (comma_pair_encode f d)+9-comma_pair_difference (comma_pair_encode f d)=
      2*comma_port_previous f d"
    using right_numerator by simp
  show "comma_pair_sector (comma_pair_encode f d)=f"
    unfolding comma_pair_sector_def comma_pair_encode_def
    using sector_mod by (simp add: Let_def)
  show "comma_pair_left_digit (comma_pair_encode f d)=d"
    unfolding comma_pair_left_digit_def using left_numerator by simp
  show "comma_pair_right_digit (comma_pair_encode f d)=comma_port_previous f d"
    unfolding comma_pair_right_digit_def using right_numerator by simp
  show "comma_port_previous f d\<le>9" using p_bound by simp
  show "(comma_port_previous f d=0)=(d=f)" using p_zero by simp
qed

lemma comma_pair_difference_factored:
  assumes "1\<le>f" "f\<le>9" "d\<le>9"
  shows "comma_pair_difference (comma_pair_encode f d)=
    f-1+10*(if d<f then 0 else 1)"
proof (cases "d<f")
  case True
  have previous: "comma_port_previous f d=(if f\<le>d then d-f else d+10-f)"
    by (rule comma_pair_previous_split[OF assms])
  have raw: "comma_pair_difference (comma_pair_encode f d)=d+9-comma_port_previous f d"
    by (simp only: comma_pair_encode_def Let_def comma_pair_difference.simps)
  have not_f_le_d: "\<not> f\<le>d" using True by arith
  have difference: "d+9-comma_port_previous f d=f-1"
    using previous assms not_f_le_d by arith
  have d_lt_f: "d<f" using True .
  show ?thesis
    by (simp only: raw difference d_lt_f if_True; arith)
next
  case False
  have previous: "comma_port_previous f d=(if f\<le>d then d-f else d+10-f)"
    by (rule comma_pair_previous_split[OF assms])
  have difference: "d+9-comma_port_previous f d=f+9"
    using previous False by arith
  have not_lt: "\<not> d<f" using False by arith
  have raw: "comma_pair_difference (comma_pair_encode f d)=d+9-comma_port_previous f d"
    by (simp only: comma_pair_encode_def Let_def comma_pair_difference.simps)
  show ?thesis
    using assms by (simp only: raw difference not_lt if_False; arith)
qed

lemma comma_pair_center_closed_form:
  assumes "1\<le>f" "f\<le>9" "d\<le>9"
  shows "comma_pair_center f d=(d+10-(f+1) div 2) mod 5"
proof (cases "even f")
  case True
  then obtain k where fk: "f=2*k" by (auto elim: evenE)
  have k4: "k\<le>4" using assms(2) fk by arith
  show ?thesis
  proof (cases "f\<le>d")
    case True
    have previous: "comma_port_previous f d=d-f"
      using comma_pair_previous_split[OF assms] True by simp
    have sum: "d+comma_port_previous f d=2*(d-k)"
      using previous fk True by arith
    have half: "(d+comma_port_previous f d) div 2=d-k"
      by (simp only: sum; simp)
    have ceil: "(f+1) div 2=k" using fk by simp
    have shifted: "d+10-k=(d-k)+10" using fk True by arith
    have shift_mod: "((d-k)+10) mod 5=(d-k) mod 5"
      by (subst mod_add_right_eq[symmetric]; simp)
    show ?thesis
      unfolding comma_pair_center_def
      using half ceil shifted shift_mod
      by (simp only: half ceil shifted shift_mod)
  next
    case False
    have previous: "comma_port_previous f d=d+10-f"
      using comma_pair_previous_split[OF assms] False by simp
    have sum: "d+comma_port_previous f d=2*(d+5-k)"
      using previous fk k4 by arith
    have half: "(d+comma_port_previous f d) div 2=d+5-k"
      by (simp only: sum; simp)
    have ceil: "(f+1) div 2=k" using fk by simp
    have shifted: "d+10-k=(d+5-k)+5" using fk k4 by arith
    have shift_mod: "((d+5-k)+5) mod 5=(d+5-k) mod 5"
      by (subst mod_add_right_eq[symmetric]; simp)
    show ?thesis
      unfolding comma_pair_center_def
      using half ceil shifted shift_mod
      by (simp only: half ceil shifted shift_mod)
  qed
next
  case False
  then obtain k where fk: "f=2*k+1" by (auto elim: oddE)
  have k4: "k\<le>4" using assms(2) fk by arith
  show ?thesis
  proof (cases "f\<le>d")
    case True
    have previous: "comma_port_previous f d=d-f"
      using comma_pair_previous_split[OF assms] True by simp
    have sum: "d+comma_port_previous f d=2*(d-k-1)+1"
      using previous fk True by arith
    have half: "(d+comma_port_previous f d) div 2=d-k-1"
      by (simp only: sum; simp)
    have ceil: "(f+1) div 2=k+1" using fk by simp
    have shifted: "d+10-(k+1)=(d-k-1)+10" using fk True by arith
    have shift_mod: "((d-k-1)+10) mod 5=(d-k-1) mod 5"
      by (subst mod_add_right_eq[symmetric]; simp)
    show ?thesis
      unfolding comma_pair_center_def
      using half ceil shifted shift_mod
      by (simp only: half ceil shifted shift_mod)
  next
    case False
    have previous: "comma_port_previous f d=d+10-f"
      using comma_pair_previous_split[OF assms] False by simp
    have sum: "d+comma_port_previous f d=2*(d+4-k)+1"
      using previous fk k4 by arith
    have half: "(d+comma_port_previous f d) div 2=d+4-k"
      by (simp only: sum; simp)
    have ceil: "(f+1) div 2=k+1" using fk by simp
    have shifted: "d+10-(k+1)=(d+4-k)+5" using fk k4 by arith
    have shift_mod: "((d+4-k)+5) mod 5=(d+4-k) mod 5"
      by (subst mod_add_right_eq[symmetric]; simp)
    show ?thesis
      unfolding comma_pair_center_def
      using half ceil shifted shift_mod
      by (simp only: half ceil shifted shift_mod)
  qed
qed

lemma comma_pair_center_mod_shift:
  fixes a k :: nat
  assumes "k\<le>10"
  shows "(a mod 5+10-k) mod 5=(a+10-k) mod 5"
proof -
  have left: "a mod 5+10-k=a mod 5+(10-k)" using assms by arith
  have right: "a+10-k=a+(10-k)" using assms by arith
  show ?thesis by (simp only: left right mod_add_left_eq)
qed

lemma comma_pair_center_previous:
  assumes "1\<le>f" "f\<le>9" "d\<le>9"
  shows "comma_pair_center f (comma_port_previous f d)=
    (comma_pair_center f d+10-f) mod 5"
proof -
  let ?p = "comma_port_previous f d"
  let ?c = "(f+1) div 2"
  have split: "?p=(if f\<le>d then d-f else d+10-f)"
    by (rule comma_pair_previous_split[OF assms])
  have bound: "?p\<le>9" using split assms by (auto split: if_splits; arith)
  have c_bound: "?c\<le>5" using assms(2) by arith
  have source: "comma_pair_center f d=(d+10-?c) mod 5"
    by (rule comma_pair_center_closed_form[OF assms])
  have target: "comma_pair_center f ?p=(?p+10-?c) mod 5"
    by (rule comma_pair_center_closed_form[OF assms(1,2) bound])
  have f10: "f\<le>10" using assms(2) by arith
  have shift: "((d+10-?c) mod 5+10-f) mod 5=(d+10-?c+10-f) mod 5"
    by (rule comma_pair_center_mod_shift[OF f10])
  show ?thesis
  proof (cases "f\<le>d")
    case True
    have previous: "?p=d-f" using split True by simp
    have offset: "d+10-?c+10-f=(?p+10-?c)+10"
      using previous True c_bound by arith
    have periodic: "((?p+10-?c)+10) mod 5=(?p+10-?c) mod 5"
      by (subst mod_add_right_eq[symmetric]; simp)
    show ?thesis by (simp only: source target shift offset periodic)
  next
    case False
    have previous: "?p=d+10-f" using split False by simp
    have offset: "d+10-?c+10-f=?p+10-?c"
      using previous assms c_bound by arith
    show ?thesis by (simp only: source target shift offset)
  qed
qed

lemma comma_pair_center_next:
  assumes "1\<le>f" "f\<le>9" "d\<le>9"
  shows "comma_pair_center f (comma_port_next f d)=
    (if comma_port_previous f d=0 then
      (comma_pair_center f d+20-2*f) mod 5
     else (comma_pair_center f d+10-f) mod 5)"
proof (cases "comma_port_previous f d=0")
  case False
  have advance: "comma_port_next f d=comma_port_previous f d"
    by (simp only: comma_port_next_def Let_def False if_False)
  show ?thesis
    by (simp only: False if_False advance comma_pair_center_previous[OF assms])
next
  case True
  have advance: "comma_port_next f d=comma_port_previous f 0"
    by (simp only: comma_port_next_def Let_def True if_True HOL.simp_thms)
  have zero_bound: "(0::nat)\<le>9" by simp
  have zero: "comma_pair_center f 0=(comma_pair_center f d+10-f) mod 5"
    using comma_pair_center_previous[OF assms] by (simp only: True)
  have target: "comma_pair_center f (comma_port_previous f 0)=
      (comma_pair_center f 0+10-f) mod 5"
    by (rule comma_pair_center_previous[OF assms(1,2) zero_bound])
  have f10: "f\<le>10" using assms(2) by arith
  have shift: "((comma_pair_center f d+10-f) mod 5+10-f) mod 5=
      (comma_pair_center f d+10-f+10-f) mod 5"
    by (rule comma_pair_center_mod_shift[OF f10])
  have offset: "comma_pair_center f d+10-f+10-f=comma_pair_center f d+20-2*f"
    using f10 by arith
  show ?thesis by (simp only: True if_True advance target zero shift offset HOL.simp_thms)
qed

lemma comma_pair_encoding_law_point:
  assumes "1\<le>f" "f\<le>9" "1\<le>d" "d\<le>9"
  shows "comma_pair_encoding_law f d"
proof -
  have arithmetic: "comma_pair_sum (comma_pair_encode f d)=d+comma_port_previous f d"
    "comma_pair_difference (comma_pair_encode f d)=d+9-comma_port_previous f d"
    "comma_pair_sum (comma_pair_encode f d)+comma_pair_difference (comma_pair_encode f d)-9=2*d"
    "comma_pair_sum (comma_pair_encode f d)+9-comma_pair_difference (comma_pair_encode f d)=
      2*comma_port_previous f d"
    "comma_pair_sector (comma_pair_encode f d)=f"
    "comma_pair_left_digit (comma_pair_encode f d)=d"
    "comma_pair_right_digit (comma_pair_encode f d)=comma_port_previous f d"
    "comma_port_previous f d\<le>9"
    "(comma_port_previous f d=0)=(d=f)"
    by (rule comma_pair_encoded_arithmetic[OF assms(1,2,4)])+
  have sum_bound: "comma_pair_sum (comma_pair_encode f d)\<le>18"
    using arithmetic(1) arithmetic(8) assms by arith
  have difference_bound: "comma_pair_difference (comma_pair_encode f d)\<le>18"
    using arithmetic(2) assms by arith
  have even_left:
    "(comma_pair_sum (comma_pair_encode f d)+comma_pair_difference (comma_pair_encode f d)-9) mod 2=0"
    using arithmetic(3) by simp
  have even_right:
    "(comma_pair_sum (comma_pair_encode f d)+9-comma_pair_difference (comma_pair_encode f d)) mod 2=0"
    using arithmetic(4) by simp
  show ?thesis
    unfolding comma_pair_encoding_law_def
    using arithmetic sum_bound difference_bound even_left even_right
    by (simp add: Let_def comma_pair_decode_def)
qed

lemma comma_pair_encoding_laws_checked:
  "list_all (\<lambda>f. list_all (comma_pair_encoding_law f) [1..<10]) [1..<10]"
  using comma_pair_encoding_law_point
  by (auto simp: list_all_iff)

lemma comma_pair_encoding_law:
  assumes "1\<le>f" "f\<le>9" "1\<le>d" "d\<le>9"
  shows "comma_pair_encoding_law f d"
  by (rule comma_pair_encoding_law_point[OF assms])

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

lemma comma_pair_gap_law_point:
  assumes "1\<le>f" "f\<le>9" "1\<le>d" "d\<le>9"
  shows "comma_pair_gap_law f d"
proof -
  have arithmetic: "comma_pair_sum (comma_pair_encode f d)=d+comma_port_previous f d"
    "comma_pair_difference (comma_pair_encode f d)=d+9-comma_port_previous f d"
    "comma_pair_sum (comma_pair_encode f d)+comma_pair_difference (comma_pair_encode f d)-9=2*d"
    "comma_pair_sum (comma_pair_encode f d)+9-comma_pair_difference (comma_pair_encode f d)=
      2*comma_port_previous f d"
    "comma_pair_sector (comma_pair_encode f d)=f"
    by (rule comma_pair_encoded_arithmetic[OF assms(1,2,4)])+
  have first: "comma_pair_first_gap (comma_pair_encode f d)=10*d+f"
    using arithmetic by (simp add: comma_pair_first_gap_def)
  have second:
    "comma_pair_second_gap (comma_pair_encode f d)=10*comma_port_previous f d+f"
    using arithmetic by (simp add: comma_pair_second_gap_def)
  have total:
    "comma_pair_first_gap (comma_pair_encode f d)+comma_pair_second_gap (comma_pair_encode f d)=
      10*comma_pair_sum (comma_pair_encode f d)+2*f"
    using first second arithmetic(1) by arith
  show ?thesis
    unfolding comma_pair_gap_law_def
    using first second total by (simp add: Let_def)
qed

lemma comma_pair_gap_laws_checked:
  "list_all (\<lambda>f. list_all (comma_pair_gap_law f) [1..<10]) [1..<10]"
  using comma_pair_gap_law_point
  by (auto simp: list_all_iff)

theorem comma_pair_adjacent_thresholds:
  assumes "1\<le>f" "f\<le>9" "1\<le>d" "d\<le>9"
  shows "comma_pair_first_gap (comma_pair_encode f d)=10*d+f"
    "comma_pair_second_gap (comma_pair_encode f d)=10*comma_port_previous f d+f"
    "comma_pair_first_gap (comma_pair_encode f d)+comma_pair_second_gap (comma_pair_encode f d)=
      10*comma_pair_sum (comma_pair_encode f d)+2*f"
proof -
  have law: "comma_pair_gap_law f d" by (rule comma_pair_gap_law_point[OF assms])
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
    @{thms comma_pair_previous_split comma_pair_difference_factored
      comma_pair_center_closed_form comma_pair_center_previous comma_pair_center_next
      comma_pair_encoding_laws_checked comma_pair_field_decode
      comma_pair_field_encode comma_pair_field_bijection comma_pair_step_conjugate
      comma_pair_step_closed comma_pair_adjacent_thresholds comma_pair_physical_zero
      comma_pair_gap_carry_decomposition comma_pair_zero_regression comma_pair_last_row_refines})
    then () else error "Comma pair field depends on an oracle";
\<close>
end
