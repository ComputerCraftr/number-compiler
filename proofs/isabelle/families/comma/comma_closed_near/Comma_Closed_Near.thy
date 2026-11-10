theory Comma_Closed_Near
  imports Comma_Near_Period.Comma_Near_Period
begin

text \<open>The executable Near germ skips complete phase cycles by division
and inspects at most nine residual positions. Its displacement and maximality proof
refines the existing well-founded Near specification.\<close>

fun comma_near_residual_count :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<times> nat" where
  "comma_near_residual_count 0 f d b = (0,b)"
| "comma_near_residual_count (Suc k) f d b =
    (let a=10*d+f in
      if a\<le>b then
        (case comma_near_residual_count k f ((d+f) mod 10) (b-a) of
          (j,u) \<Rightarrow> (Suc j,u))
      else (0,b))"

definition comma_near_closed_germ :: "nat \<Rightarrow> nat \<Rightarrow> nat \<times> nat" where
  "comma_near_closed_germ f h =
    (let e=if f<9 then 1 else 0 in
      if f<1 \<or> 9<f \<or> h=0 \<or> 540<h \<or> h\<le>e then (0,h)
      else (let d=(10-h mod 10) mod 10;
        L=comma_cycle_length_fast f;
        P=comma_finite_period_fast f d;
        B=h-e-1;
        q=B div P;
        b=B mod P
      in case comma_near_residual_count (L-1) f d b of
        (j,u) \<Rightarrow> (q*L+j,h-q*P-(b-u))))"

lemma comma_near_residual_certificate:
  assumes digit: "d<10" and result: "comma_near_residual_count k f d b=(j,u)"
  shows "j\<le>k \<and> comma_period_displacement f d j+u=b \<and>
    (j<k \<longrightarrow> b<comma_period_displacement f d (Suc j))"
  using digit result
proof (induction k arbitrary: d b j u)
  case 0
  then show ?case by (simp add: comma_period_displacement_def)
next
  case (Suc k)
  let ?a = "10*d+f"
  let ?d = "(d+f) mod 10"
  show ?case
  proof (cases "?a\<le>b")
    case True
    obtain i v where tail: "comma_near_residual_count k f ?d (b-?a)=(i,v)"
      by (cases "comma_near_residual_count k f ?d (b-?a)") auto
    have fields: "j=Suc i" "u=v"
      using Suc.prems(2) True tail by (simp_all add: Let_def)
    have facts: "i\<le>k" "comma_period_displacement f ?d i+v=b-?a"
      "i<k \<longrightarrow> b-?a<comma_period_displacement f ?d (Suc i)"
      using Suc.IH[of ?d "b-?a" i v] tail by auto
    have current: "comma_period_displacement f d (Suc i)=
      ?a+comma_period_displacement f ?d i"
      by (rule comma_near_displacement_tail[OF Suc.prems(1)])
    have next_displacement: "comma_period_displacement f d (Suc (Suc i))=
      ?a+comma_period_displacement f ?d (Suc i)"
      by (rule comma_near_displacement_tail[OF Suc.prems(1)])
    show ?thesis using facts True
      by (simp only: fields  current next_displacement; arith)
  next
    case False
    have fields: "j=0" "u=b"
      using Suc.prems(2) False by (simp_all add: Let_def)
    have next_displacement: "comma_period_displacement f d (Suc 0)=?a"
      using comma_near_displacement_tail[OF Suc.prems(1), of f 0]
      by (simp add: comma_period_displacement_def)
    show ?thesis using False Suc.prems(1)
      by (simp add: fields next_displacement comma_period_displacement_def)
  qed
qed

lemma comma_near_residual_prefix_bound:
  assumes "d<10" "comma_near_residual_count k f d b=(j,u)" "i\<le>j"
  shows "comma_period_displacement f d i\<le>b"
  using comma_near_residual_certificate[OF assms(1,2)]
    comma_period_displacement_mono[OF assms(3), of f d] by arith

lemma comma_near_residual_maximal:
  assumes digit: "d<10" and positive: "0<L"
    and bound: "b<comma_period_displacement f d L"
    and result: "comma_near_residual_count (L-1) f d b=(j,u)"
  shows "comma_period_displacement f d j+u=b"
    "b<comma_period_displacement f d (Suc j)"
proof -
  have cert: "j\<le>L-1" "comma_period_displacement f d j+u=b"
    "j<L-1 \<longrightarrow> b<comma_period_displacement f d (Suc j)"
    using comma_near_residual_certificate[OF digit result] by auto
  show "comma_period_displacement f d j+u=b" by (rule cert(2))
  show "b<comma_period_displacement f d (Suc j)"
  proof (cases "j<L-1")
    case True
    then show ?thesis using cert(3) by blast
  next
    case False
    have "Suc j=L" using cert(1) positive False by arith
    then show ?thesis using bound by simp
  qed
qed

theorem comma_near_closed_germ_correct:
  assumes sector: "1\<le>f" "f\<le>9" and initial: "1\<le>h" "h\<le>540"
  shows "comma_near_closed_germ f h = comma_near_germ f h"
proof (cases "h\<le>(if f<9 then 1 else 0)")
  case True
  have decisive: "comma_near_decisive f h"
    using True by (simp only: comma_near_decisive_iff[OF sector initial]; arith)
  have germ: "comma_near_germ f h=(0,h)"
    by (rule comma_near_prefix_decisive_germ[OF _ decisive]) simp
  show ?thesis using True
    by (simp add: comma_near_closed_germ_def Let_def germ)
next
  case False
  let ?e = "if f<9 then 1 else 0"
  let ?d = "(10-h mod 10) mod 10"
  let ?L = "comma_cycle_length f"
  let ?P = "comma_finite_period f ?d"
  let ?B = "h-?e-1"
  let ?q = "?B div ?P"
  let ?b = "?B mod ?P"
  have digit: "?d<10" by simp
  have length: "0<?L" by (rule comma_cycle_length_admitted(1)[OF sector])
  have closes: "10 dvd ?L*f" by (rule comma_cycle_length_admitted(2)[OF sector])
  have period: "?P=comma_period_displacement f ?d ?L"
    by (rule comma_finite_period_refines[OF sector digit])
  have catalog: "?P\<in>comma_cycle_displacements"
    using comma_finite_period_in_catalog[rule_format, of f ?d] sector digit by auto
  have positive: "0<?P" using catalog
    by (auto simp: comma_cycle_displacements_def)
  have bound: "?b<comma_period_displacement f ?d ?L"
    using positive period by simp
  obtain j u where residual: "comma_near_residual_count (?L-1) f ?d ?b=(j,u)"
    by (cases "comma_near_residual_count (?L-1) f ?d ?b") auto
  have balance: "comma_period_displacement f ?d j+u=?b"
    and next_displacement: "?b<comma_period_displacement f ?d (Suc j)"
    by (rule comma_near_residual_maximal[OF digit length bound residual])+
  have decomposition: "?q*?P+?b=?B" by (rule div_mult_mod_eq)
  have headroom: "h=?B+?e+1" using False by arith
  have safe: "?q*comma_period_displacement f ?d ?L+
      comma_period_displacement f ?d j+?e<h"
    using balance decomposition headroom by (simp only: period[symmetric]; arith)
  have maximal: "h\<le>?q*comma_period_displacement f ?d ?L+
      comma_period_displacement f ?d (Suc j)+?e"
    using next_displacement decomposition headroom by (simp only: period[symmetric]; arith)
  have germ: "comma_near_germ f h=(?q*?L+j,
      h-(?q*?P+comma_period_displacement f ?d j))"
    using comma_near_germ_from_period_residual[OF sector initial(2) digit
      comma_near_initial_digit_aligned closes safe maximal]
    by (simp only: period)
  have displacement: "?b-u=comma_period_displacement f ?d j" using balance by arith
  have fast_length: "comma_cycle_length_fast f=?L"
    by (rule comma_cycle_length_fast_correct[OF sector])
  have fast_period: "comma_finite_period_fast f ?d=?P"
    by (rule comma_finite_period_fast_correct[OF sector digit])
  have guard: "\<not>(f<1 \<or> 9<f \<or> h=0 \<or> 540<h \<or> h\<le>?e)"
    using sector initial False by arith
  have closed: "comma_near_closed_germ f h=(?q*?L+j,h-?q*?P-(?b-u))"
    by (simp only: comma_near_closed_germ_def Let_def guard if_False
      fast_length fast_period residual prod.case)
  have endpoint: "h-?q*?P-(?b-u)=h-(?q*?P+comma_period_displacement f ?d j)"
    by (subst displacement; simp only: diff_diff_left)
  show ?thesis by (simp only: closed endpoint germ)
qed

lemma comma_near_fast_period_positive_decimal:
  assumes sector: "1\<le>f" "f\<le>9" and digit: "d<10"
  shows "0<comma_finite_period_fast f d"
    "comma_finite_period_fast f d mod 10=0"
proof -
  have period: "comma_finite_period f d\<in>comma_cycle_displacements"
    using comma_finite_period_in_catalog[rule_format, of f d] sector digit
    by auto
  have fast: "comma_finite_period_fast f d=comma_finite_period f d"
    by (rule comma_finite_period_fast_correct[OF sector digit])
  have catalog: "comma_finite_period_fast f d\<in>comma_cycle_displacements"
    using period fast by simp
  show "0<comma_finite_period_fast f d"
    using catalog by (auto simp: comma_cycle_displacements_def)
  show "comma_finite_period_fast f d mod 10=0"
    using catalog by (auto simp: comma_cycle_displacements_def)
qed

text \<open>
The finite Near control depends on the residual port, not on the number of
complete displacement cycles already consumed.  The quotient contributes
only the additive elapsed-time cocycle.  The endpoint below is still the
exact decisive headroom, so terminal labels and subsequent sector actions
remain source-correct.
\<close>
theorem comma_near_closed_germ_residual_factorization_with_data:
  fixes f h e g d P L B q b h0 :: nat
  assumes sector: "1\<le>f" "f\<le>9"
    and initial: "1\<le>h" "h\<le>540"
    and headroom: "(if f<9 then 1 else 0)<h"
  defines e_def: "e\<equiv>(if f<9 then 1 else 0)"
    and g_def: "g\<equiv>e+1"
    and d_def: "d\<equiv>(10-h mod 10) mod 10"
    and P_def: "P\<equiv>comma_finite_period_fast f d"
    and L_def: "L\<equiv>comma_cycle_length_fast f"
    and B_def: "B\<equiv>h-g"
    and q_def: "q\<equiv>B div P"
    and b_def: "b\<equiv>B mod P"
    and h0_def: "h0\<equiv>g+b"
  shows "1\<le>h0"
    and "h0\<le>540"
    and "e<h0"
    and "comma_near_closed_germ f h =
      (q*L+fst (comma_near_closed_germ f h0),
       snd (comma_near_closed_germ f h0))"
proof -
  have e_headroom: "e<h" using headroom e_def by simp
  have digit: "d<10" using d_def by simp
  have period_facts:
      "0<comma_finite_period_fast f d"
      "comma_finite_period_fast f d mod 10=0"
    by (rule comma_near_fast_period_positive_decimal[OF sector digit])+
  have period_positive: "0<P"
    using period_facts(1) P_def by simp
  have period_decimal: "P mod 10=0"
    using period_facts(2) P_def by simp
  have period_dvd: "10 dvd P"
    using period_decimal by (simp add: dvd_eq_mod_eq_0)
  have period_product_mod: "(q*P) mod 10=0"
    using dvd_mult[OF period_dvd, of q]
    by (simp add: dvd_eq_mod_eq_0 mult.commute)
  have g_bound: "g\<le>h"
    using e_headroom g_def by arith
  have boundary: "B+g=h"
    using B_def g_bound by arith
  have quotient_remainder: "q*P+b=B"
  proof -
    have "(B div P)*P+B mod P=B"
      by (rule div_mult_mod_eq)
    then show ?thesis using q_def b_def by simp
  qed
  have remainder_bound: "b<P"
    using period_positive b_def by simp
  have h_decomposition: "h=h0+q*P"
    using boundary quotient_remainder h0_def
    by (simp add: add.assoc add.commute add.left_commute)
  have h0_le_h: "h0\<le>h"
    using h_decomposition by arith
  have h0_positive: "1\<le>h0"
    using e_def g_def h0_def by arith
  have h0_within: "h0\<le>540"
    using h0_le_h initial(2) by arith
  have h0_headroom: "e<h0"
    using e_def g_def h0_def by arith
  show "1\<le>h0" by (rule h0_positive)
  show "h0\<le>540" by (rule h0_within)
  show "e<h0" by (rule h0_headroom)

  have h_mod_h0: "h mod 10=h0 mod 10"
  proof -
    have reduce_right:
        "(h0+q*P) mod 10=(h0+(q*P mod 10)) mod 10"
      by (rule mod_add_right_eq[symmetric])
    show ?thesis
      using h_decomposition period_product_mod reduce_right by simp
  qed
  have d_h0: "(10-h0 mod 10) mod 10=d"
    using h_mod_h0 d_def by simp
  have fast_period_h: "comma_finite_period_fast f d=P"
    using P_def by simp
  have fast_period_h0:
      "comma_finite_period_fast f ((10-h0 mod 10) mod 10)=P"
    using d_h0 fast_period_h by simp
  have fast_length_h: "comma_cycle_length_fast f=L"
    using L_def by simp
  obtain j u where residual:
      "comma_near_residual_count (L-1) f d b=(j,u)"
    by (cases "comma_near_residual_count (L-1) f d b") auto
  have guard_h:
      "\<not>(f<1 \<or> 9<f \<or> h=0 \<or> 540<h \<or> h\<le>e)"
    using sector initial e_headroom by arith
  have base_headroom: "h0-e-1=b"
    using g_def h0_def by arith
  have base_quotient: "(h0-e-1) div P=0"
    using base_headroom remainder_bound by simp
  have base_remainder: "(h0-e-1) mod P=b"
    using base_headroom remainder_bound by simp
  have guard_h0:
      "\<not>(f<1 \<or> 9<f \<or> h0=0 \<or> 540<h0 \<or> h0\<le>e)"
    using sector h0_positive h0_within h0_headroom by arith
  have closed_h:
      "comma_near_closed_germ f h=(q*L+j,h-q*P-(b-u))"
  proof -
    have exact_headroom: "h-e-1=B"
      using B_def g_def by arith
    have quotient: "(h-e-1) div P=q"
      using exact_headroom q_def by simp
    have remainder: "(h-e-1) mod P=b"
      using exact_headroom b_def by simp
    show ?thesis
      by (simp only: comma_near_closed_germ_def Let_def guard_h if_False
        e_def[symmetric] d_def[symmetric] fast_length_h fast_period_h exact_headroom
        quotient remainder q_def[symmetric] b_def[symmetric] residual prod.case)
  qed
  have closed_h0:
      "comma_near_closed_germ f h0=(j,h0-(b-u))"
  proof -
    have exact_headroom: "h0-e-1=b" by (rule base_headroom)
    have quotient: "(h0-e-1) div P=0" by (rule base_quotient)
    have remainder: "(h0-e-1) mod P=b" by (rule base_remainder)
    have base_div: "b div P=0" using remainder_bound by simp
    have base_mod: "b mod P=b" using remainder_bound by simp
    show ?thesis
      by (simp only: comma_near_closed_germ_def Let_def guard_h0 if_False
        e_def[symmetric] d_h0 fast_length_h fast_period_h fast_period_h0 exact_headroom
        quotient remainder base_div base_mod residual prod.case; simp)
  qed
  have endpoint: "h-q*P=h0"
    using h_decomposition by arith
  show "comma_near_closed_germ f h =
      (q*L+fst (comma_near_closed_germ f h0),
       snd (comma_near_closed_germ f h0))"
    using closed_h closed_h0 endpoint by simp
qed

theorem comma_near_closed_germ_residual_factorization:
  fixes f H :: nat
  assumes sector: "1\<le>f" "f\<le>9"
    and admitted: "1\<le>H" "H\<le>540"
    and interior: "(if f<9 then 1 else 0)<H"
  shows "(let e=if f<9 then 1 else 0;
             g=e+1;
             d=(10-H mod 10) mod 10;
             P=comma_finite_period_fast f d;
             L=comma_cycle_length_fast f;
             B=H-g;
             q=B div P;
             b=B mod P;
             h0=g+b
         in 1\<le>h0 \<and> h0\<le>540 \<and> e<h0 \<and>
           comma_near_closed_germ f H =
             (q*L+fst (comma_near_closed_germ f h0),
              snd (comma_near_closed_germ f h0)))"
proof -
  let ?e = "if f<9 then 1 else 0"
  let ?g = "?e+1"
  let ?d = "(10-H mod 10) mod 10"
  let ?P = "comma_finite_period_fast f ?d"
  let ?L = "comma_cycle_length_fast f"
  let ?B = "H-?g"
  let ?q = "?B div ?P"
  let ?b = "?B mod ?P"
  let ?h0 = "?g+?b"
  have h0_positive: "1\<le>?h0"
    using comma_near_closed_germ_residual_factorization_with_data(1)
      [OF sector admitted interior]
    by (simp only: Let_def)
  have h0_within: "?h0\<le>540"
    using comma_near_closed_germ_residual_factorization_with_data(2)
      [OF sector admitted interior]
    by (simp only: Let_def)
  have h0_headroom: "?e<?h0"
    using comma_near_closed_germ_residual_factorization_with_data(3)
      [OF sector admitted interior]
    by (simp only: Let_def)
  have factor:
      "comma_near_closed_germ f H =
        (?q*?L+fst (comma_near_closed_germ f ?h0),
         snd (comma_near_closed_germ f ?h0))"
    using comma_near_closed_germ_residual_factorization_with_data(4)
      [OF sector admitted interior]
    by (simp only: Let_def)
  show ?thesis
    unfolding Let_def
    by (intro conjI;
        (rule h0_positive | rule h0_within | rule h0_headroom | rule factor))
qed

corollary comma_near_germ_residual_factorization:
  fixes f H :: nat
  assumes sector: "1\<le>f" "f\<le>9"
    and admitted: "1\<le>H" "H\<le>540"
    and interior: "(if f<9 then 1 else 0)<H"
  shows "(let e=if f<9 then 1 else 0;
             g=e+1;
             d=(10-H mod 10) mod 10;
             P=comma_finite_period_fast f d;
             L=comma_cycle_length_fast f;
             B=H-g;
             q=B div P;
             b=B mod P;
             h0=g+b
         in comma_near_germ f H =
             (q*L+fst (comma_near_germ f h0),
              snd (comma_near_germ f h0)))"
proof -
  let ?e = "if f<9 then 1 else 0"
  let ?g = "?e+1"
  let ?d = "(10-H mod 10) mod 10"
  let ?P = "comma_finite_period_fast f ?d"
  let ?L = "comma_cycle_length_fast f"
  let ?B = "H-?g"
  let ?q = "?B div ?P"
  let ?b = "?B mod ?P"
  let ?h0 = "?g+?b"
  have package:
      "1\<le>?h0 \<and> ?h0\<le>540 \<and> ?e<?h0 \<and>
       comma_near_closed_germ f H =
         (?q*?L+fst (comma_near_closed_germ f ?h0),
          snd (comma_near_closed_germ f ?h0))"
    using comma_near_closed_germ_residual_factorization[OF sector admitted interior]
    by (simp only: Let_def)
  have h0_positive: "1\<le>?h0" using package by blast
  have h0_within: "?h0\<le>540" using package by blast
  have closed_factor:
      "comma_near_closed_germ f H =
        (?q*?L+fst (comma_near_closed_germ f ?h0),
         snd (comma_near_closed_germ f ?h0))"
    using package by blast
  have source_correct:
      "comma_near_closed_germ f H=comma_near_germ f H"
    by (rule comma_near_closed_germ_correct[OF sector admitted])
  have base_correct:
      "comma_near_closed_germ f ?h0=comma_near_germ f ?h0"
    by (rule comma_near_closed_germ_correct[OF sector h0_positive h0_within])
  show ?thesis
    unfolding Let_def
    using closed_factor source_correct base_correct
    by (simp only: source_correct[symmetric] closed_factor base_correct)
qed

corollary comma_near_closed_germ_correct_all:
  "comma_near_closed_germ f h = comma_near_germ f h"
proof (cases "1\<le>f \<and> f\<le>9 \<and> 1\<le>h \<and> h\<le>540")
  case True
  then show ?thesis using comma_near_closed_germ_correct by blast
next
  case False
  have invalid: "f<1 \<or> 9<f \<or> h=0 \<or> 540<h" using False by arith
  have step: "comma_finite_step 0 (Comma_Near f 0 h) = Comma_Invalid"
    using invalid by (simp add: comma_near_control_formula Let_def)
  have closed: "comma_near_closed_germ f h = (0,h)"
    using invalid by (auto simp: comma_near_closed_germ_def Let_def)
  show ?thesis
    using comma_near_germ.simps[of f h]
    by (simp only: closed step comma_finite_move.case)
qed

theorem comma_near_closed_refines:
  assumes sector: "1\<le>f" "f\<le>9" and initial: "1\<le>h" "h\<le>540"
    and result: "comma_near_closed_germ f h=(n,t)"
  shows "comma_near_prefix n f h t" "comma_near_decisive f t"
proof -
  have germ: "comma_near_germ f h=(n,t)"
    using result by (simp only: comma_near_closed_germ_correct[OF sector initial])
  have facts: "comma_near_prefix n f h t \<and> comma_near_decisive f t"
    by (rule comma_near_germ_refines[OF germ])
  show "comma_near_prefix n f h t" using facts by blast
  show "comma_near_decisive f t" using facts by blast
qed


ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_near_residual_certificate comma_near_residual_maximal
      comma_near_closed_germ_correct comma_near_closed_germ_correct_all
      comma_near_closed_refines}) then ()
    else error "Closed Near germ depends on an oracle";
\<close>
end
