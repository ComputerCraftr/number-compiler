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
