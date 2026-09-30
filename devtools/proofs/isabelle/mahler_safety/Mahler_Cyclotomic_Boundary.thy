theory Mahler_Cyclotomic_Boundary
  imports Generated_Mahler_Safety
begin

text \<open>Words are chronological: the head is the earliest temporal bit.
These certificates concern the sign of one current tail. They do not certify
all shifted tails, a Z-number, or Antihydra ledger survival.\<close>

fun mahler_bit_int :: "bool \<Rightarrow> int" where
  "mahler_bit_int False=0"
| "mahler_bit_int True=1"

fun mahler_word_carry :: "bool list \<Rightarrow> int" where
  "mahler_word_carry []=0"
| "mahler_word_carry (e#w)=mahler_bit_int e*3^(length w)+2*mahler_word_carry w"

definition mahler_signed_carry :: "bool list \<Rightarrow> int" where
  "mahler_signed_carry w=3^(length w)-2^(length w)-2*mahler_word_carry w"

lemma mahler_word_carry_snoc:
  "mahler_word_carry (w@[e])=3*mahler_word_carry w+mahler_bit_int e*2^(length w)"
  by (induction w) (simp_all add: power_Suc algebra_simps)

lemma mahler_signed_carry_snoc:
  "mahler_signed_carry (w@[e])=
    3*mahler_signed_carry w+(1-2*mahler_bit_int e)*2^(length w)"
  by (simp add: mahler_signed_carry_def mahler_word_carry_snoc power_Suc algebra_simps)

lemma mahler_signed_carry_empty [simp]: "mahler_signed_carry []=0"
  by (simp add: mahler_signed_carry_def)

lemma mahler_signed_carry_odd:
  assumes "w\<noteq>[]"
  shows "odd (mahler_signed_carry w)"
  using assms by (simp add: mahler_signed_carry_def)

lemma mahler_signed_carry_no_edges:
  assumes "w\<noteq>[]"
  shows "mahler_signed_carry w\<noteq>2^(length w)"
    "mahler_signed_carry w\<noteq>-(2^(length w))"
  using mahler_signed_carry_odd[OF assms] assms by auto

definition mahler_eta :: "bool list \<Rightarrow> real" where
  "mahler_eta w=of_int (mahler_signed_carry w)/2^(length w)"

lemma mahler_eta_snoc:
  "mahler_eta (w@[e])=(3/2)*mahler_eta w+(1-2*of_int (mahler_bit_int e))/2"
  by (simp add: mahler_eta_def mahler_signed_carry_snoc power_Suc field_simps algebra_simps)

definition mahler_tail_enclosed :: "bool list \<Rightarrow> real \<Rightarrow> bool" where
  "mahler_tail_enclosed w t =
    ((of_int (mahler_signed_carry w)-2^(length w))/3^(length w)\<le>t \<and>
     t\<le>(of_int (mahler_signed_carry w)+2^(length w))/3^(length w))"

lemma mahler_tail_remainder_enclosed:
  fixes u :: real
  assumes "-1\<le>u" "u\<le>1"
  shows "mahler_tail_enclosed w
    ((of_int (mahler_signed_carry w)+2^(length w)*u)/3^(length w))"
proof -
  have positive: "0\<le>(2::real)^(length w)" by simp
  have lo: "2^(length w)*(-1)\<le>(2::real)^(length w)*u"
    by (rule mult_left_mono[OF assms(1) positive])
  have hi: "(2::real)^(length w)*u\<le>2^(length w)*1"
    by (rule mult_left_mono[OF assms(2) positive])
  show ?thesis using lo hi
    by (simp add: mahler_tail_enclosed_def divide_le_cancel; linarith)
qed

lemma mahler_current_tail_safe:
  assumes enclosed: "mahler_tail_enclosed w t"
    and safe: "2^(length w)<mahler_signed_carry w"
  shows "0<t"
proof -
  have cast: "(of_int (2^(length w))::real)<of_int (mahler_signed_carry w)"
    using safe by (simp only: of_int_less_iff)
  have lower: "0<(of_int (mahler_signed_carry w)-2^(length w)::real)"
    using cast by simp
  have "0<(of_int (mahler_signed_carry w)-2^(length w))/(3::real)^(length w)"
    using lower by simp
  then show ?thesis using enclosed unfolding mahler_tail_enclosed_def by linarith
qed

lemma mahler_current_tail_fail:
  assumes enclosed: "mahler_tail_enclosed w t"
    and fail: "mahler_signed_carry w\<le>-(2^(length w))"
  shows "t\<le>0"
proof -
  have cast: "(of_int (mahler_signed_carry w)::real)\<le>of_int (-(2^(length w)))"
    using fail by (simp only: of_int_le_iff)
  have upper: "(of_int (mahler_signed_carry w)+2^(length w)::real)\<le>0"
    using cast by simp
  have "(of_int (mahler_signed_carry w)+2^(length w))/(3::real)^(length w)\<le>0"
    by (rule divide_nonpos_nonneg[OF upper]) simp
  then show ?thesis using enclosed unfolding mahler_tail_enclosed_def by linarith
qed

fun mahler_boundary_step :: "bool \<Rightarrow> int\<times>int \<Rightarrow> int\<times>int" where
  "mahler_boundary_step False (A,B)=(3*A,2*B-A)"
| "mahler_boundary_step True (A,B)=(2*A-B,3*B)"

lemma mahler_boundary_one_fail_port:
  "2*A<B \<Longrightarrow> fst (mahler_boundary_step True (A,B))<0"
  by simp

lemma mahler_boundary_zero_safe_port:
  "2*B<A \<Longrightarrow> snd (mahler_boundary_step False (A,B))<0"
  by simp

lemma mahler_boundary_vieta:
  "fst (mahler_boundary_step e (mahler_boundary_step e (A,B)))
      -5*fst (mahler_boundary_step e (A,B))+6*A=0"
  "snd (mahler_boundary_step e (mahler_boundary_step e (A,B)))
      -5*snd (mahler_boundary_step e (A,B))+6*B=0"
  by (cases e; simp add: algebra_simps)+

definition mahler_boundary_coordinates :: "bool list \<Rightarrow> int\<times>int" where
  "mahler_boundary_coordinates w=
    (mahler_signed_carry w+2^(length w),2^(length w)-mahler_signed_carry w)"

lemma mahler_boundary_sum:
  "fst (mahler_boundary_coordinates w)+snd (mahler_boundary_coordinates w)=2^(Suc (length w))"
  by (simp add: mahler_boundary_coordinates_def power_Suc algebra_simps)

lemma mahler_boundary_snoc:
  "mahler_boundary_coordinates (w@[e])=mahler_boundary_step e (mahler_boundary_coordinates w)"
  by (cases e) (simp_all add: mahler_boundary_coordinates_def mahler_signed_carry_snoc power_Suc algebra_simps)

lemma mahler_boundary_zero_run:
  "(mahler_boundary_step False ^^ k) (A,B)=
    (3^k*A,2^k*B-(3^k-2^k)*A)"
  by (induction k) (simp_all add: funpow_Suc_right power_Suc algebra_simps)

lemma mahler_boundary_one_run:
  "(mahler_boundary_step True ^^ k) (A,B)=
    (2^k*A-(3^k-2^k)*B,3^k*B)"
  by (induction k) (simp_all add: funpow_Suc_right power_Suc algebra_simps)

lemma mahler_boundary_repeat:
  "mahler_boundary_coordinates (w@replicate k e)=
    (mahler_boundary_step e ^^ k) (mahler_boundary_coordinates w)"
proof (induction k)
  case 0
  show ?case by simp
next
  case (Suc k)
  have snoc: "replicate (Suc k) e=replicate k e@[e]"
    by (simp add: replicate_append_same)
  show ?case
    by (simp only: snoc append_assoc[symmetric] mahler_boundary_snoc Suc.IH
      funpow.simps o_apply)
qed

lemma mahler_boundary_safe_step:
  assumes "0<A+B" "B<0"
  shows "snd (mahler_boundary_step e (A,B))<0"
proof (cases e)
  case False
  show ?thesis using assms by (simp only: False mahler_boundary_step.simps snd_conv; linarith)
next
  case True
  show ?thesis using assms by (simp only: True mahler_boundary_step.simps snd_conv; linarith)
qed

lemma mahler_boundary_fail_step:
  assumes "0<A+B" "A\<le>0"
  shows "fst (mahler_boundary_step e (A,B))\<le>0"
proof (cases e)
  case False
  show ?thesis using assms by (simp only: False mahler_boundary_step.simps fst_conv; linarith)
next
  case True
  show ?thesis using assms by (simp only: True mahler_boundary_step.simps fst_conv; linarith)
qed

lemma mahler_safe_absorbing:
  assumes "2^(length w)<mahler_signed_carry w"
  shows "2^(length (w@[e]))<mahler_signed_carry (w@[e])"
proof -
  obtain A B where coordinates: "mahler_boundary_coordinates w=(A,B)"
    by (cases "mahler_boundary_coordinates w") auto
  have positive: "0<A+B"
    using mahler_boundary_sum[of w] by (simp add: coordinates)
  have safe: "B<0"
    using coordinates assms by (simp add: mahler_boundary_coordinates_def)
  have step: "snd (mahler_boundary_step e (A,B))<0"
    by (rule mahler_boundary_safe_step[OF positive safe])
  have target: "mahler_boundary_coordinates (w@[e])=mahler_boundary_step e (A,B)"
    by (simp only: mahler_boundary_snoc coordinates)
  have "snd (mahler_boundary_coordinates (w@[e]))<0"
    using step by (simp only: target)
  then show ?thesis by (simp add: mahler_boundary_coordinates_def)
qed

lemma mahler_fail_absorbing:
  assumes "mahler_signed_carry w\<le>-(2^(length w))"
  shows "mahler_signed_carry (w@[e])\<le>-(2^(length (w@[e])))"
proof -
  obtain A B where coordinates: "mahler_boundary_coordinates w=(A,B)"
    by (cases "mahler_boundary_coordinates w") auto
  have positive: "0<A+B"
    using mahler_boundary_sum[of w] by (simp add: coordinates)
  have fail: "A\<le>0"
    using coordinates assms by (simp add: mahler_boundary_coordinates_def)
  have step: "fst (mahler_boundary_step e (A,B))\<le>0"
    by (rule mahler_boundary_fail_step[OF positive fail])
  have target: "mahler_boundary_coordinates (w@[e])=mahler_boundary_step e (A,B)"
    by (simp only: mahler_boundary_snoc coordinates)
  have "fst (mahler_boundary_coordinates (w@[e]))\<le>0"
    using step by (simp only: target)
  then show ?thesis by (simp add: mahler_boundary_coordinates_def)
qed

lemma mahler_safe_all_extensions:
  assumes "2^(length w)<mahler_signed_carry w"
  shows "2^(length (w@v))<mahler_signed_carry (w@v)"
proof (induction v rule: rev_induct)
  case Nil
  show ?case using assms by simp
next
  case (snoc e v)
  have "2^(length ((w@v)@[e]))<mahler_signed_carry ((w@v)@[e])"
    by (rule mahler_safe_absorbing[OF snoc.IH])
  then show ?case by (simp only: append_assoc)
qed

lemma mahler_fail_all_extensions:
  assumes "mahler_signed_carry w\<le>-(2^(length w))"
  shows "mahler_signed_carry (w@v)\<le>-(2^(length (w@v)))"
proof (induction v rule: rev_induct)
  case Nil
  show ?case using assms by simp
next
  case (snoc e v)
  have "mahler_signed_carry ((w@v)@[e])\<le>-(2^(length ((w@v)@[e])))"
    by (rule mahler_fail_absorbing[OF snoc.IH])
  then show ?case by (simp only: append_assoc)
qed

lemma mahler_boundary_strict_cone:
  assumes "w\<noteq>[]"
  shows "(-(2^(length w))<mahler_signed_carry w \<and> mahler_signed_carry w\<le>2^(length w)) =
    (0<fst (mahler_boundary_coordinates w) \<and> 0<snd (mahler_boundary_coordinates w))"
  using mahler_signed_carry_no_edges[OF assms]
  by (simp add: mahler_boundary_coordinates_def; linarith)

lemma mahler_six_bit_boundary:
  assumes "\<not>(a\<and>b)" "\<not>(b\<and>c)" "\<not>(c\<and>d)" "\<not>(d\<and>e)" "\<not>(e\<and>f)"
  shows "(-64<mahler_signed_carry [a,b,c,d,e,f] \<and> mahler_signed_carry [a,b,c,d,e,f]\<le>64) =
    ([a,b,c,d,e,f]=[True,False,True,False,False,False] \<or>
     [a,b,c,d,e,f]=[True,False,False,True,False,False] \<or>
     [a,b,c,d,e,f]=[True,False,False,True,False,True])"
  using assms
  by (cases a; cases b; cases c; cases d; cases e; cases f;
    simp_all add: mahler_signed_carry_def)

lemma mahler_three_boundary_coordinates:
  "mahler_boundary_coordinates [True,False,True,False,False,False]=(27,101)"
  "mahler_boundary_coordinates [True,False,False,True,False,False]=(99,29)"
  "mahler_boundary_coordinates [True,False,False,True,False,True]=(35,93)"
  by (simp_all add: mahler_boundary_coordinates_def mahler_signed_carry_def)


fun mahler_source_word :: "nat \<Rightarrow> nat \<Rightarrow> bool list" where
  "mahler_source_word D 0=[]"
| "mahler_source_word D (Suc n)=mahler_source_word D n@[odd (mahler_orbit D n)]"

lemma mahler_source_word_length [simp]: "length (mahler_source_word D n)=n"
  by (induction n) simp_all

lemma mahler_source_word_numeral [simp]:
  "mahler_source_word D (numeral n)=
    mahler_source_word D (pred_numeral n)@[odd (mahler_orbit D (pred_numeral n))]"
  by (simp only: numeral_eq_Suc mahler_source_word.simps)

lemma mahler_source_step_numerator:
  "2*int (mahler_D_step D)=3*int D+mahler_bit_int (odd D)"
  by (cases D rule: nat_mod_two_cases)
    (simp_all add: mahler_D_step_def algebra_simps)

theorem mahler_source_carry_bridge:
  "2^n*int (mahler_orbit D n)=3^n*int D+mahler_word_carry (mahler_source_word D n)"
proof (induction n)
  case 0
  show ?case by simp
next
  case (Suc n)
  have step: "2*int (mahler_orbit D (Suc n))=
      3*int (mahler_orbit D n)+mahler_bit_int (odd (mahler_orbit D n))"
    using mahler_source_step_numerator[of "mahler_orbit D n"] by simp
  have scaled: "2^n*(2*int (mahler_orbit D (Suc n)))=
      2^n*(3*int (mahler_orbit D n)+mahler_bit_int (odd (mahler_orbit D n)))"
    by (simp only: step)
  show ?case using scaled Suc.IH
    by (simp only: mahler_source_word.simps mahler_word_carry_snoc mahler_source_word_length power_Suc;
      simp_all add: algebra_simps; linarith)
qed

corollary mahler_source_signed_bridge:
  "mahler_signed_carry (mahler_source_word D n)=
    3^n*(2*int D+1)-2^n*(2*int (mahler_orbit D n)+1)"
  using mahler_source_carry_bridge[of n D]
  by (simp only: mahler_signed_carry_def mahler_source_word_length;
    simp_all add: algebra_simps; linarith)

lemma mahler_six_survivor_tail_partition:
  "\<forall>r\<in>surviving_residues.
    (if r\<in>{9,13,45} then
      -64<mahler_signed_carry (mahler_source_word r 6) \<and>
      mahler_signed_carry (mahler_source_word r 6)\<le>64
     else 64<mahler_signed_carry (mahler_source_word r 6))"
  by (simp add: surviving_residues_def mahler_signed_carry_def mahler_D_step_def)

lemma mahler_six_survivor_current_safe_count:
  "card (surviving_residues-{9,13,45})=15"
  by (simp add: surviving_residues_def)

lemma mahler_six_source_boundary_coordinates:
  "mahler_boundary_coordinates (mahler_source_word 9 6)=(27,101)"
  "mahler_boundary_coordinates (mahler_source_word 13 6)=(99,29)"
  "mahler_boundary_coordinates (mahler_source_word 45 6)=(35,93)"
  by (simp_all add: mahler_boundary_coordinates_def mahler_signed_carry_def mahler_D_step_def)

corollary mahler_six_survivor_current_tail_safe:
  assumes "r\<in>surviving_residues" "r\<notin>{9,13,45}"
    "mahler_tail_enclosed (mahler_source_word r 6) t"
  shows "0<t"
proof -
  have "64<mahler_signed_carry (mahler_source_word r 6)"
    using mahler_six_survivor_tail_partition assms(1,2) by auto
  then have threshold: "2^(length (mahler_source_word r 6))<mahler_signed_carry (mahler_source_word r 6)"
    by simp
  show ?thesis by (rule mahler_current_tail_safe[OF assms(3) threshold])
qed

text \<open>The enclosure theorem accepts an explicit bounded real remainder.
Connecting a concrete infinite tail to that remainder is a separate source
obligation; the six-bit theorem assumes no adjacent ones rather than assuming
a global Mahler-admissibility theorem.\<close>

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms mahler_signed_carry_snoc mahler_signed_carry_no_edges mahler_eta_snoc
      mahler_tail_remainder_enclosed mahler_current_tail_safe mahler_current_tail_fail
      mahler_boundary_snoc mahler_boundary_zero_run mahler_boundary_one_run
      mahler_boundary_one_fail_port mahler_boundary_zero_safe_port mahler_boundary_vieta
      mahler_safe_all_extensions mahler_fail_all_extensions mahler_six_bit_boundary
      mahler_source_carry_bridge mahler_source_signed_bridge
      mahler_six_survivor_tail_partition mahler_six_survivor_current_safe_count
      mahler_six_source_boundary_coordinates mahler_six_survivor_current_tail_safe})
    then () else error "Mahler cyclotomic boundary depends on an oracle";
\<close>
end
