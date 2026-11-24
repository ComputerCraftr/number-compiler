theory Mahler_CF_Minimal_Prefix
  imports Mahler_Continued_Fraction_Refinement Mahler_Finite_Safety_Refinement
    Mahler_CF_Pow5_Source
begin

text \<open>
The exact continuant \<open>q, r, p, s\<close> represents the map
\<open>(p + t*s)/(q + t*r)\<close>.  Its endpoint interval is the physical
continued-fraction cylinder.  Positive coefficients map a following tail in
\<open>[0,1]\<close> to another tail in that same interval.
\<close>

definition mahler_cf_value ::
  "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "mahler_cf_value q r p s t = (p + t*s) / (q + t*r)"

definition mahler_cf_low ::
  "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "mahler_cf_low q r p s = min (p/q) ((p+s)/(q+r))"

definition mahler_cf_high ::
  "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "mahler_cf_high q r p s = max (p/q) ((p+s)/(q+r))"

lemma mahler_cf_inlet_between:
  fixes q r p s t :: real
  assumes q: "0 < q" and r: "0 \<le> r" and t: "0 \<le> t" "t \<le> 1"
  shows "mahler_cf_low q r p s \<le> mahler_cf_value q r p s t"
    "mahler_cf_value q r p s t \<le> mahler_cf_high q r p s"
proof -
  have qr: "0 < q+r" using q r by simp
  have denominator: "0 < q+t*r" using q r t by (intro add_pos_nonneg mult_nonneg_nonneg) auto
  let ?u = "(q*(1-t))/(q+t*r)"
  let ?v = "((q+r)*t)/(q+t*r)"
  have u: "0 \<le> ?u" using q t denominator by (intro divide_nonneg_nonneg mult_nonneg_nonneg) auto
  have v: "0 \<le> ?v" using qr t denominator by (intro divide_nonneg_nonneg mult_nonneg_nonneg) auto
  have weights: "?u+?v=1"
    using denominator by (simp add: add_divide_distrib[symmetric] field_simps algebra_simps)
  have left_weight: "?u*(p/q) = ((1-t)*p)/(q+t*r)"
    using q by (simp add: divide_inverse ac_simps)
  have right_weight: "?v*((p+s)/(q+r)) = (t*(p+s))/(q+t*r)"
    using qr by (simp add: divide_inverse ac_simps)
  have weighted:
    "mahler_cf_value q r p s t =
      ?u*(p/q) + ?v*((p+s)/(q+r))"
  proof -
    have numerator: "(1-t)*p + t*(p+s) = p+t*s"
      by (simp add: algebra_simps)
    show ?thesis
      by (simp only: left_weight right_weight mahler_cf_value_def
        add_divide_distrib[symmetric] numerator)
  qed
  have upper: "?u*(p/q) + ?v*((p+s)/(q+r)) \<le>
      max (p/q) ((p+s)/(q+r))"
    by (rule convex_bound_le) (use u v weights in auto)
  have lower: "?u*(-(p/q)) + ?v*(-((p+s)/(q+r))) \<le>
      max (-(p/q)) (-((p+s)/(q+r)))"
    by (rule convex_bound_le) (use u v weights in auto)
  have negated: "- mahler_cf_value q r p s t \<le> - mahler_cf_low q r p s"
    using lower weighted by (simp add: mahler_cf_low_def minus_min_eq_max)
  show "mahler_cf_low q r p s \<le> mahler_cf_value q r p s t"
    using negated by simp
  show "mahler_cf_value q r p s t \<le> mahler_cf_high q r p s"
    using upper weighted by (simp add: mahler_cf_high_def)
qed

lemma mahler_cf_digit_tail:
  fixes coefficient t :: real
  assumes c: "1 \<le> coefficient" and t: "0 \<le> t" "t \<le> 1"
  shows "0 \<le> 1/(coefficient+t)" "1/(coefficient+t) \<le> 1"
proof -
  have positive: "0 < coefficient+t" using c t by linarith
  show "0 \<le> 1/(coefficient+t)" using positive by simp
  show "1/(coefficient+t) \<le> 1"
    using c t positive by (simp add: divide_le_eq)
qed

lemma mahler_cf_digit_value:
  fixes q r p s coefficient t :: real
  assumes q: "0 < q" and r: "0 \<le> r"
      and c: "1 \<le> coefficient" and t: "0 \<le> t"
  shows "mahler_cf_value (q*coefficient+r) q (p*coefficient+s) p t =
    mahler_cf_value q r p s (1/(coefficient+t))"
proof -
  have positive: "0 < coefficient+t" using c t by linarith
  have first: "0 < q*coefficient+r+t*q"
    using q r c t by (intro add_pos_nonneg mult_pos_pos mult_nonneg_nonneg) auto
  have numerator: "p + 1/(coefficient+t)*s = (p*(coefficient+t)+s)/(coefficient+t)"
    using positive by (simp add: add_divide_distrib)
  have denominator: "q + 1/(coefficient+t)*r = (q*(coefficient+t)+r)/(coefficient+t)"
    using positive by (simp add: add_divide_distrib)
  have cancel: "((p*(coefficient+t)+s)/(coefficient+t)) /
      ((q*(coefficient+t)+r)/(coefficient+t)) =
      (p*(coefficient+t)+s)/(q*(coefficient+t)+r)"
    using positive by (simp add: divide_divide_times_eq)
  show ?thesis unfolding mahler_cf_value_def
    using numerator denominator cancel by (simp add: algebra_simps)
qed

theorem mahler_cf_digit_cylinder_nested:
  fixes q r p s coefficient :: real
  assumes q: "0 < q" and r: "0 \<le> r" and c: "1 \<le> coefficient"
  shows "mahler_cf_low q r p s \<le>
      mahler_cf_low (q*coefficient+r) q (p*coefficient+s) p"
    "mahler_cf_high (q*coefficient+r) q (p*coefficient+s) p \<le>
      mahler_cf_high q r p s"
proof -
  have "0 < q*coefficient+r" using q r c
    by (intro add_pos_nonneg mult_pos_pos) auto
  then have child:
    "mahler_cf_low (q*coefficient+r) q (p*coefficient+s) p =
      min (mahler_cf_value (q*coefficient+r) q (p*coefficient+s) p 0)
          (mahler_cf_value (q*coefficient+r) q (p*coefficient+s) p 1)"
    "mahler_cf_high (q*coefficient+r) q (p*coefficient+s) p =
      max (mahler_cf_value (q*coefficient+r) q (p*coefficient+s) p 0)
          (mahler_cf_value (q*coefficient+r) q (p*coefficient+s) p 1)"
    by (simp_all add: mahler_cf_low_def mahler_cf_high_def mahler_cf_value_def)
  have bounds0: "mahler_cf_low q r p s \<le>
      mahler_cf_value (q*coefficient+r) q (p*coefficient+s) p 0"
    "mahler_cf_value (q*coefficient+r) q (p*coefficient+s) p 0 \<le>
      mahler_cf_high q r p s"
    using mahler_cf_inlet_between[OF q r mahler_cf_digit_tail[OF c, of 0]]
    by (simp_all add: mahler_cf_digit_value[OF q r c])
  have bounds1: "mahler_cf_low q r p s \<le>
      mahler_cf_value (q*coefficient+r) q (p*coefficient+s) p 1"
    "mahler_cf_value (q*coefficient+r) q (p*coefficient+s) p 1 \<le>
      mahler_cf_high q r p s"
    using mahler_cf_inlet_between[OF q r mahler_cf_digit_tail[OF c, of 1]]
    by (simp_all add: mahler_cf_digit_value[OF q r c])
  show "mahler_cf_low q r p s \<le>
      mahler_cf_low (q*coefficient+r) q (p*coefficient+s) p"
    using child bounds0 bounds1 by simp
  show "mahler_cf_high (q*coefficient+r) q (p*coefficient+s) p \<le>
      mahler_cf_high q r p s"
    using child bounds0 bounds1 by simp
qed


fun mahler_cf_extend ::
  "real \<times> real \<times> real \<times> real \<Rightarrow> nat \<Rightarrow>
    real \<times> real \<times> real \<times> real" where
  "mahler_cf_extend (q,r,p,s) digit =
    (q * of_nat (Suc digit) + r, q, p * of_nat (Suc digit) + s, p)"

definition mahler_cf_prefix ::
  "nat list \<Rightarrow> real \<times> real \<times> real \<times> real" where
  "mahler_cf_prefix digits = fold (\<lambda>digit state. mahler_cf_extend state digit) digits (1,0,0,1)"


fun mahler_cf_matrix_coordinates ::
  "nat ordered_matrix2 \<Rightarrow> real \<times> real \<times> real \<times> real" where
  "mahler_cf_matrix_coordinates (Ordered_Matrix2 q r p s) =
    (of_nat q, of_nat r, of_nat p, of_nat s)"

theorem mahler_cf_prefix_is_ordered_continuant:
  "mahler_cf_prefix digits =
    mahler_cf_matrix_coordinates (mahler_cf_word digits)"
proof (induction digits rule: rev_induct)
  case Nil
  then show ?case by (simp add: mahler_cf_prefix_def mahler_cf_word_def ordered_matrix2_identity_def)
next
  case (snoc digit digits)
  then show ?case
    by (cases "mahler_cf_word digits")
      (simp add: mahler_cf_prefix_def mahler_cf_word_append
        mahler_cf_word_def mahler_cf_digit_def algebra_simps)
qed

lemma mahler_cf_extend_positive:
  fixes q r :: real
  assumes "0 < q" "0 \<le> r"
  shows "0 < q * of_nat (Suc digit) + r" "0 \<le> q"
  using assms by (auto intro!: add_pos_nonneg mult_pos_pos)

lemma mahler_cf_prefix_positive:
  assumes "mahler_cf_prefix digits = (q,r,p,s)"
  shows "0 < q" "0 \<le> r"
proof -
  let ?P = "\<lambda>(state :: real \<times> real \<times> real \<times> real). case state of (a,b,c,d) \<Rightarrow> 0 < a \<and> 0 \<le> b"
  have step: "\<And>digit state. ?P state \<Longrightarrow> ?P (mahler_cf_extend state digit)"
  proof -
    fix digit :: nat and state :: "real \<times> real \<times> real \<times> real"
    obtain a b c d where state: "state = (a,b,c,d)" by (cases state) auto
    assume valid: "?P state"
    have ab: "0 < a" "0 \<le> b" using valid by (simp_all add: state)
    have step_positive: "0 < a * of_nat (Suc digit) + b"
      by (rule mahler_cf_extend_positive(1)[OF ab])
    show "?P (mahler_cf_extend state digit)" using ab step_positive by (simp add: state)
  qed
  have "?P (fold (\<lambda>digit state. mahler_cf_extend state digit) digits (1,0,0,1))"
  proof (rule fold_invariant[where Q="\<lambda>_. True"])
    show "\<And>x. x \<in> set digits \<Longrightarrow> True" by simp
    show "?P (1,0,0,1)" by simp
    show "\<And>x state. True \<Longrightarrow> ?P state \<Longrightarrow>
        ?P (mahler_cf_extend state x)" by (rule step)
  qed
  then show "0 < q" "0 \<le> r"
    using assms by (simp_all add: mahler_cf_prefix_def)
qed


lemma mahler_cf_extend_nonsingular:
  fixes q r p s :: real
  assumes "q*s \<noteq> r*p"
  shows "(q * of_nat (Suc digit) + r)*p \<noteq>
    q*(p * of_nat (Suc digit) + s)"
  using assms by (simp add: algebra_simps)

lemma mahler_cf_prefix_nonsingular:
  assumes "mahler_cf_prefix digits = (q,r,p,s)"
  shows "q*s \<noteq> r*p"
proof -
  let ?P = "\<lambda>(state :: real \<times> real \<times> real \<times> real). case state of (a,b,c,d) \<Rightarrow> a*d \<noteq> b*c"
  have step: "\<And>digit state. ?P state \<Longrightarrow> ?P (mahler_cf_extend state digit)"
  proof -
    fix digit :: nat and state :: "real \<times> real \<times> real \<times> real"
    obtain a b c d where state: "state = (a,b,c,d)" by (cases state) auto
    assume valid: "?P state"
    have det: "a*d \<noteq> b*c" using valid by (simp add: state)
    have preserved: "(a * of_nat (Suc digit) + b)*c \<noteq> a*(c * of_nat (Suc digit) + d)"
      by (rule mahler_cf_extend_nonsingular[OF det])
    show "?P (mahler_cf_extend state digit)" using preserved by (simp add: state)
  qed
  have "?P (fold (\<lambda>digit state. mahler_cf_extend state digit) digits (1,0,0,1))"
  proof (rule fold_invariant[where Q="\<lambda>_. True"])
    show "\<And>x. x \<in> set digits \<Longrightarrow> True" by simp
    show "?P (1,0,0,1)" by simp
    show "\<And>x state. True \<Longrightarrow> ?P state \<Longrightarrow>
        ?P (mahler_cf_extend state x)" by (rule step)
  qed
  then show ?thesis using assms by (simp add: mahler_cf_prefix_def)
qed

lemma mahler_cf_prefix_strict:
  assumes source: "mahler_cf_prefix digits = (q,r,p,s)"
  shows "mahler_cf_low q r p s < mahler_cf_high q r p s"
proof -
  have positive: "0 < q" "0 \<le> r"
    using mahler_cf_prefix_positive[OF source] by auto
  have distinct: "q*s \<noteq> r*p"
    by (rule mahler_cf_prefix_nonsingular[OF source])
  have "p/q \<noteq> (p+s)/(q+r)" using positive distinct
    by (auto simp: divide_simps algebra_simps)
  then show ?thesis by (simp add: mahler_cf_low_def mahler_cf_high_def)
qed

lemma mahler_cf_prefix_append_digit:
  "mahler_cf_prefix (digits @ [digit]) =
    mahler_cf_extend (mahler_cf_prefix digits) digit"
  by (simp add: mahler_cf_prefix_def)

theorem mahler_cf_prefix_digit_nested:
  assumes source: "mahler_cf_prefix digits = (q,r,p,s)"
      and successor: "mahler_cf_prefix (digits @ [digit]) = (q',r',p',s')"
  shows "mahler_cf_low q r p s \<le> mahler_cf_low q' r' p' s'"
    "mahler_cf_high q' r' p' s' \<le> mahler_cf_high q r p s"
proof -
  have positive: "0 < q" "0 \<le> r"
    using mahler_cf_prefix_positive[OF source] by auto
  have child: "(q',r',p',s') =
      (q * of_nat (Suc digit) + r, q, p * of_nat (Suc digit) + s, p)"
    using successor source by (metis mahler_cf_prefix_append_digit mahler_cf_extend.simps)
  show "mahler_cf_low q r p s \<le> mahler_cf_low q' r' p' s'"
    using mahler_cf_digit_cylinder_nested(1)[OF positive, of "of_nat (Suc digit)"] child
    by simp
  show "mahler_cf_high q' r' p' s' \<le> mahler_cf_high q r p s"
    using mahler_cf_digit_cylinder_nested(2)[OF positive, of "of_nat (Suc digit)"] child
    by simp
qed

theorem mahler_cf_source_prefix_nested:
  fixes q r p s q' r' p' s' :: real
    and source_digits future_digits :: "nat list"
  assumes source: "mahler_cf_prefix source_digits = (q,r,p,s)"
      and later: "mahler_cf_prefix (source_digits @ future_digits) = (q',r',p',s')"
  shows "mahler_cf_low q r p s \<le> mahler_cf_low q' r' p' s'"
    "mahler_cf_high q' r' p' s' \<le> mahler_cf_high q r p s"
proof -
  have extend:
    "\<And>q r p s q' r' p' s'. mahler_cf_prefix source_digits = (q,r,p,s) \<Longrightarrow>
       mahler_cf_prefix (source_digits @ future_digits) = (q',r',p',s') \<Longrightarrow>
       mahler_cf_low q r p s \<le> mahler_cf_low q' r' p' s' \<and>
       mahler_cf_high q' r' p' s' \<le> mahler_cf_high q r p s"
  proof (induction future_digits arbitrary: source_digits)
    case Nil
    then show ?case by simp
  next
    case (Cons digit rest)
    obtain a b c d where midpoint:
      "mahler_cf_prefix (source_digits @ [digit]) = (a,b,c,d)"
      by (cases "mahler_cf_prefix (source_digits @ [digit])") auto
    have first:
      "mahler_cf_low q r p s \<le> mahler_cf_low a b c d"
      "mahler_cf_high a b c d \<le> mahler_cf_high q r p s"
      using mahler_cf_prefix_digit_nested[OF Cons.prems(1) midpoint] by auto
    have following:
      "mahler_cf_low a b c d \<le> mahler_cf_low q' r' p' s'"
      "mahler_cf_high q' r' p' s' \<le> mahler_cf_high a b c d"
      using Cons.IH[OF midpoint] Cons.prems(2) by auto
    show ?case using first following by auto
  qed
  show "mahler_cf_low q r p s \<le> mahler_cf_low q' r' p' s'"
    using extend[OF source later] by blast
  show "mahler_cf_high q' r' p' s' \<le> mahler_cf_high q r p s"
    using extend[OF source later] by blast
qed

definition mahler_cf_decides :: "real \<Rightarrow> real \<Rightarrow> bool \<Rightarrow> bool" where
  "mahler_cf_decides left right is_complete \<longleftrightarrow>
    0 \<le> left \<and> left < right \<and> right \<le> 1/2 \<and>
      (is_complete \<or> right \<le> 1/3 \<or> 1/3 \<le> left)"

lemma mahler_cf_decision_narrows:
  fixes left right next_left next_right :: real
  assumes decided: "mahler_cf_decides left right is_complete"
      and nested: "left \<le> next_left" "next_left < next_right" "next_right \<le> right"
  shows "mahler_cf_decides next_left next_right is_complete"
  using assms by (auto simp: mahler_cf_decides_def; linarith)

lemma mahler_cf_positive_affine_nesting:
  fixes lower upper next_lower next_upper gain innovation denominator :: real
  assumes "0 < gain" "0 < denominator"
      and "lower \<le> next_lower" "next_upper \<le> upper"
  shows "(gain*lower-innovation)/denominator \<le>
      (gain*next_lower-innovation)/denominator"
    "(gain*next_upper-innovation)/denominator \<le>
      (gain*upper-innovation)/denominator"
  using assms by (auto simp: divide_le_cancel)

definition mahler_cf_prefix_decides ::
  "nat list \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> bool \<Rightarrow> bool"
where
  "mahler_cf_prefix_decides digits gain innovation denominator is_complete =
    (case mahler_cf_prefix digits of (q,r,p,s) \<Rightarrow>
      mahler_cf_decides
        ((gain * mahler_cf_low q r p s - innovation) / denominator)
        ((gain * mahler_cf_high q r p s - innovation) / denominator)
        is_complete)"

theorem mahler_cf_physical_prefix_decision_monotone:
  fixes gain innovation denominator :: real and prefix suffix :: "nat list"
  assumes gain: "0 < gain" and denominator: "0 < denominator"
    and decision: "mahler_cf_prefix_decides prefix gain innovation denominator is_complete"
  shows "mahler_cf_prefix_decides (prefix @ suffix)
      gain innovation denominator is_complete"
proof -
  obtain q r p s where source: "mahler_cf_prefix prefix = (q,r,p,s)"
    by (cases "mahler_cf_prefix prefix") auto
  obtain q' r' p' s' where next_source:
    "mahler_cf_prefix (prefix @ suffix) = (q',r',p',s')"
    by (cases "mahler_cf_prefix (prefix @ suffix)") auto
  have nested:
    "mahler_cf_low q r p s \<le> mahler_cf_low q' r' p' s'"
    "mahler_cf_high q' r' p' s' \<le> mahler_cf_high q r p s"
    using mahler_cf_source_prefix_nested[OF source next_source] by auto
  have image:
    "(gain * mahler_cf_low q r p s - innovation) / denominator \<le>
      (gain * mahler_cf_low q' r' p' s' - innovation) / denominator"
    "(gain * mahler_cf_high q' r' p' s' - innovation) / denominator \<le>
      (gain * mahler_cf_high q r p s - innovation) / denominator"
    by (rule mahler_cf_positive_affine_nesting[OF gain denominator nested])+
  have strict: "mahler_cf_low q' r' p' s' < mahler_cf_high q' r' p' s'"
    by (rule mahler_cf_prefix_strict[OF next_source])
  have strict_image:
    "(gain * mahler_cf_low q' r' p' s' - innovation) / denominator <
      (gain * mahler_cf_high q' r' p' s' - innovation) / denominator"
    using strict gain denominator by (simp add: divide_less_cancel; linarith)
  have parent:
    "mahler_cf_decides ((gain * mahler_cf_low q r p s - innovation) / denominator)
      ((gain * mahler_cf_high q r p s - innovation) / denominator) is_complete"
    using decision source by (simp add: mahler_cf_prefix_decides_def)
  show ?thesis
    using mahler_cf_decision_narrows[OF parent image(1) strict_image image(2)]
      next_source by (simp add: mahler_cf_prefix_decides_def)
qed

lemma mahler_cf_physical_take_monotone:
  fixes gain innovation denominator :: real and prefix source :: "nat list"
  assumes "0 < gain" "0 < denominator" "i \<le> j"
      and "mahler_cf_prefix_decides (prefix @ take i source)
        gain innovation denominator is_complete"
  shows "mahler_cf_prefix_decides (prefix @ take j source)
    gain innovation denominator is_complete"
proof -
  have "take j source = take i source @ take (j-i) (drop i source)"
    using take_add[of i "j-i" source] assms(3) by simp
  then show ?thesis
    using mahler_cf_physical_prefix_decision_monotone[OF assms(1,2,4),
      of "take (j-i) (drop i source)"]
    by (simp add: append.assoc)
qed


text \<open>A source issuer supplies the chronological sequence of nested
physical prefixes. The skip and search conclusions hold for that sequence
without storing an occurrence word in an action identity.\<close>

definition mahler_cf_first_decisive ::
  "(nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> nat option" where
  "mahler_cf_first_decisive decided limit =
    (if \<exists>i\<le>limit. decided i then Some (LEAST i. decided i) else None)"

theorem mahler_cf_whole_block_skip:
  fixes decided :: "nat \<Rightarrow> bool" and limit :: nat
  assumes monotone: "\<And>i j. i \<le> j \<Longrightarrow> j \<le> limit \<Longrightarrow>
      decided i \<Longrightarrow> decided j"
      and absent: "\<not> decided limit"
  shows "\<forall>i\<le>limit. \<not> decided i"
proof (intro allI impI notI)
  fix i assume bound: "i \<le> limit" and hit: "decided i"
  have refl: "limit \<le> limit" by simp
  have "decided limit" by (rule monotone[OF bound refl hit])
  with absent show False by contradiction
qed

theorem mahler_cf_first_decisive_exact:
  fixes decided :: "nat \<Rightarrow> bool" and limit :: nat
  assumes found: "mahler_cf_first_decisive decided limit = Some index"
  shows "index \<le> limit" "decided index" "\<forall>i<index. \<not> decided i"
proof -
  have exists: "\<exists>i\<le>limit. decided i"
    using found by (cases "\<exists>i\<le>limit. decided i") (simp_all add: mahler_cf_first_decisive_def)
  obtain witness where witness: "witness \<le> limit" "decided witness"
    using exists by blast
  have least: "decided (LEAST i. decided i)"
    by (rule LeastI) (rule witness(2))
  have bound: "(LEAST i. decided i) \<le> witness"
    by (rule Least_le) (rule witness(2))
  have index: "index = (LEAST i. decided i)"
    using found exists by (simp add: mahler_cf_first_decisive_def)
  show "index \<le> limit" using index bound witness by simp
  show "decided index" using index least by simp
  show "\<forall>i<index. \<not> decided i" using index by (metis not_less_Least)
qed

definition mahler_cf_midpoint_step ::
  "(nat \<Rightarrow> bool) \<Rightarrow> nat \<times> nat \<Rightarrow> nat \<times> nat" where
  "mahler_cf_midpoint_step P s =
    (case s of (l,h) \<Rightarrow>
      if l < h then
        (let m = (l+h) div 2 in if P m then (l,m) else (Suc m,h))
      else s)"

definition mahler_cf_search_invariant ::
  "(nat \<Rightarrow> bool) \<Rightarrow> nat \<times> nat \<Rightarrow> bool" where
  "mahler_cf_search_invariant P s =
    (fst s \<le> snd s \<and> P (snd s) \<and> (\<forall>i<fst s. \<not> P i))"

lemma mahler_cf_midpoint_step_correct:
  assumes inv: "mahler_cf_search_invariant P s"
      and mono: "\<And>i j. i \<le> j \<Longrightarrow> P i \<Longrightarrow> P j"
  shows "mahler_cf_search_invariant P (mahler_cf_midpoint_step P s)"
    "snd (mahler_cf_midpoint_step P s) - fst (mahler_cf_midpoint_step P s) \<le>
      snd s - fst s - 1"
proof -
  obtain l h where s: "s = (l,h)" by (cases s) simp
  let ?m = "(l+h) div 2"
  have bounds: "l \<le> ?m" "?m < h" if "l < h"
    using that by arith+
  have excluded: "\<forall>i<Suc ?m. \<not> P i" if "\<not> P ?m"
    using mono that by (metis less_Suc_eq_le)
  show "mahler_cf_search_invariant P (mahler_cf_midpoint_step P s)"
    using inv bounds excluded
    by (auto simp: s mahler_cf_midpoint_step_def mahler_cf_search_invariant_def Let_def)
  show "snd (mahler_cf_midpoint_step P s) - fst (mahler_cf_midpoint_step P s) \<le>
      snd s - fst s - 1"
    using bounds
    by (auto simp: s mahler_cf_midpoint_step_def Let_def; arith)
qed

fun mahler_cf_midpoint_steps ::
  "(nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> nat \<times> nat \<Rightarrow> nat \<times> nat" where
  "mahler_cf_midpoint_steps P 0 s = s" |
  "mahler_cf_midpoint_steps P (Suc n) s =
    mahler_cf_midpoint_step P (mahler_cf_midpoint_steps P n s)"

definition mahler_cf_binary_decisive ::
  "(nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "mahler_cf_binary_decisive P l h = fst (mahler_cf_midpoint_steps P (h-l) (l,h))"

theorem mahler_cf_binary_decisive_exact:
  fixes P :: "nat \<Rightarrow> bool"
  assumes order: "l \<le> h"
      and present: "P h"
      and previous: "\<And>i. i < l \<Longrightarrow> \<not> P i"
      and mono: "\<And>i j. i \<le> j \<Longrightarrow> P i \<Longrightarrow> P j"
  defines "index \<equiv> mahler_cf_binary_decisive P l h"
  shows "l \<le> index" "index \<le> h" "P index" "\<forall>i<index. \<not> P i"
proof -
  let ?s = "\<lambda>n. mahler_cf_midpoint_steps P n (l,h)"
  have base: "mahler_cf_search_invariant P (l,h)"
    using order present previous by (auto simp: mahler_cf_search_invariant_def)
  have maintained: "mahler_cf_search_invariant P (?s n) \<and>
      snd (?s n) - fst (?s n) \<le> h-l-n" for n
  proof (induction n)
    case 0
    show ?case using base by simp
  next
    case (Suc n)
    have inv: "mahler_cf_search_invariant P (?s n)"
      using Suc.IH by blast
    have step_inv: "mahler_cf_search_invariant P (mahler_cf_midpoint_step P (?s n))"
      by (rule mahler_cf_midpoint_step_correct(1)[OF inv]) (rule mono)
    have contraction: "snd (mahler_cf_midpoint_step P (?s n)) -
        fst (mahler_cf_midpoint_step P (?s n)) \<le> snd (?s n) - fst (?s n) - 1"
      by (rule mahler_cf_midpoint_step_correct(2)[OF inv]) (rule mono)
    have advance: "mahler_cf_search_invariant P (?s (Suc n))"
      using step_inv by simp
    have bound: "snd (?s (Suc n)) - fst (?s (Suc n)) \<le> h-l-Suc n"
      using contraction Suc.IH by (simp; arith)
    show ?case using advance bound by blast
  qed
  have singleton: "snd (?s (h-l)) = fst (?s (h-l))"
    using maintained[of "h-l"] by (auto simp: mahler_cf_search_invariant_def)
  show at: "P index" and before: "\<forall>i<index. \<not> P i"
    using maintained[of "h-l"] singleton
    by (simp_all add: index_def mahler_cf_binary_decisive_def mahler_cf_search_invariant_def)
  show "l \<le> index" using at previous by (meson not_le)
  show "index \<le> h" using before present by (meson not_le)
qed


theorem mahler_cf_source_consumer_first_decisive:
  fixes gain innovation denominator :: real and prefix source :: "nat list"
    and is_complete :: bool and available :: nat
    and decides :: "nat \<Rightarrow> bool" and index :: nat
  defines "decides \<equiv>
    (\<lambda>i. mahler_cf_prefix_decides (prefix @ take i source)
      gain innovation denominator is_complete)"
    and "index \<equiv> mahler_cf_binary_decisive decides 1 available"
  assumes gain: "0 < gain" and denominator: "0 < denominator"
      and nonempty: "1 \<le> available"
      and source_bound: "available \<le> length source"
      and first: "\<not> decides 0" and last: "decides available"
  shows "1 \<le> index" "index \<le> available"
    "decides index" "\<forall>i<index. \<not> decides i"
    "index \<le> length source"
proof -
  have previous: "\<And>i. i < 1 \<Longrightarrow> \<not> decides i"
    using first by simp
  have monotone: "\<And>i j. i \<le> j \<Longrightarrow>
      decides i \<Longrightarrow> decides j"
    using mahler_cf_physical_take_monotone[OF gain denominator]
    unfolding decides_def by blast
  have selected: "1 \<le> index" "index \<le> available" "decides index"
    "\<forall>i<index. \<not> decides i"
    using mahler_cf_binary_decisive_exact[where P=decides and l=1 and h=available, OF nonempty last previous monotone]
    by (simp_all add: index_def)
  show "1 \<le> index" "index \<le> available" "decides index"
    "\<forall>i<index. \<not> decides i" "index \<le> length source"
    using selected source_bound by auto
qed

definition mahler_cf_pow5_physical_stream :: "nat \<Rightarrow> nat list" where
  "mahler_cf_pow5_physical_stream rows =
    concat (map (\<lambda>n. rev (mahler_cf_pow5_word n)) [1..<Suc rows])"

context
  fixes rows consumed :: nat
begin

lemmas mahler_cf_pow5_stream_consumer_first_decisive =
  mahler_cf_source_consumer_first_decisive[
    where prefix="take consumed (mahler_cf_pow5_physical_stream rows)"
      and source="drop consumed (mahler_cf_pow5_physical_stream rows)"]

end

theorem mahler_cf_source_consumer_skip:
  fixes gain innovation denominator :: real and prefix source :: "nat list"
  assumes "0 < gain" "0 < denominator"
    and "\<not> mahler_cf_prefix_decides (prefix @ take available source)
      gain innovation denominator is_complete"
  shows "\<forall>i\<le>available.
      \<not> mahler_cf_prefix_decides (prefix @ take i source)
        gain innovation denominator is_complete"
  using assms mahler_cf_physical_take_monotone by blast


theorem mahler_cf_budget_unknown:
  "mahler_cf_first_decisive decided limit = None \<longleftrightarrow>
    (\<forall>i\<le>limit. \<not> decided i)"
  by (auto simp: mahler_cf_first_decisive_def)

lemma mahler_cf_fractional_endpoint_mono:
  fixes lower upper :: real
  assumes "lower \<le> upper"
  shows "fractional_endpoint source time lower \<le>
    fractional_endpoint source time upper"
proof -
  have "(of_nat source + lower)*(3/2)^time \<le>
      (of_nat source + upper)*(3/2)^time"
    by (intro mult_right_mono) (use assms in auto)
  then show ?thesis by (simp add: fractional_endpoint_def)
qed

lemma mahler_cf_fractional_endpoint_strict:
  fixes lower upper :: real
  assumes "lower < upper"
  shows "fractional_endpoint source time lower <
    fractional_endpoint source time upper"
proof -
  have "(of_nat source + lower)*(3/2)^time <
      (of_nat source + upper)*(3/2)^time"
    by (intro mult_strict_right_mono) (use assms in auto)
  then show ?thesis by (simp add: fractional_endpoint_def)
qed

theorem mahler_cf_complete_source_guard:
  fixes lower upper original :: real
  assumes source_interval: "0 \<le> lower" "upper \<le> 1/2"
    and member: "lower \<le> original" "original < upper"
    and endpoint_low:
      "\<And>j. j \<le> extent \<Longrightarrow> 0 \<le> fractional_endpoint D j lower"
    and endpoint_high:
      "\<And>j. j \<le> extent \<Longrightarrow> fractional_endpoint D j upper \<le> 1/2"
  shows "cylinder_guard D extent original"
proof -
  have admissible: "0 \<le> original" "original < 1/2"
    using source_interval member by linarith+
  have all:
    "\<forall>j\<le>extent. 0 \<le> fractional_endpoint D j original \<and>
      fractional_endpoint D j original < 1/2"
  proof (intro allI impI conjI)
    fix j assume bound: "j \<le> extent"
    have "fractional_endpoint D j lower \<le> fractional_endpoint D j original"
      by (rule mahler_cf_fractional_endpoint_mono[OF member(1)])
    then show "0 \<le> fractional_endpoint D j original"
      using endpoint_low[OF bound] by simp
    have "fractional_endpoint D j original < fractional_endpoint D j upper"
      by (rule mahler_cf_fractional_endpoint_strict[OF member(2)])
    then show "fractional_endpoint D j original < 1/2"
      using endpoint_high[OF bound] by linarith
  qed
  show ?thesis using guard_iff_endpoint_bounds[OF admissible, of D extent] all by blast
qed


ML \<open>
  val checked = @{thms mahler_cf_prefix_is_ordered_continuant
    mahler_cf_digit_cylinder_nested mahler_cf_source_prefix_nested
    mahler_cf_physical_prefix_decision_monotone
    mahler_cf_source_consumer_first_decisive mahler_cf_pow5_stream_consumer_first_decisive
    mahler_cf_source_consumer_skip
    mahler_cf_complete_source_guard mahler_cf_budget_unknown};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Mahler CF prefix refinement depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked
    then error "Skipped Mahler CF prefix refinement" else ();
\<close>

end
