theory Reverse_Conditioned_Port_Period
  imports Reverse_Native_Slab_Clock
begin

text \<open>The control word contains the physical birth and both port values at each step. On a birth the high port is the shifted emitted digit. The return applies only for an authenticated continuation of that complete word.\<close>
definition reverse_guarded_digit_pair :: "bool => nat => nat => nat => nat" where
  "reverse_guarded_digit_pair birth a v s =
    (s+a) mod 10 + (if birth then v else (s+v) mod 10)"

lemma reverse_guarded_raw_residue:
  "reverse_guarded_digit_pair birth a v s mod 10 =
      (((if birth then 1 else 2)*s)+a+v) mod 10"
proof -
  have quiet: "((s+a) mod 10 + (s+v) mod 10) mod 10 = ((s+a)+(s+v)) mod 10" by (simp add: mod_simps)
  have twice: "(s+a)+(s+v)=2*s+a+v" by arith
  show ?thesis
  proof (cases birth)
    case True then show ?thesis by (simp add: reverse_guarded_digit_pair_def mod_simps)
  next
    case False then show ?thesis by (simp only: reverse_guarded_digit_pair_def if_False quiet twice)
  qed
qed

lemma reverse_guarded_last_port:
  "reverse_guarded_digit_pair birth a v (s mod 10) = reverse_guarded_digit_pair birth a v s"
  by (simp add: reverse_guarded_digit_pair_def mod_add_left_eq)

lemma reverse_guarded_slab_raw:
  "reverse_guarded_digit_pair False (carry_bit a) (carry_bit b) s = reverse_native_slab_quiet s a b"
  "reverse_guarded_digit_pair True (carry_bit a) (reverse_native_slab_digit u b) s = reverse_native_slab_birth u s a b"
  by (simp_all add: reverse_guarded_digit_pair_def reverse_native_slab_quiet_def
    reverse_native_slab_birth_def reverse_native_slab_digit_def)

lemma reverse_guarded_residue_compose:
  fixes g d h k r :: nat
  shows "(h*((g*r+d) mod 10)+k) mod 10 = ((h*g)*r + (h*d+k)) mod 10"
proof -
  have "(h*((g*r+d) mod 10)+k) mod 10 = (h*(g*r+d)+k) mod 10"
    by (rule mod_add_cong; simp add: mod_simps)
  then show ?thesis by (simp only: algebra_simps)
qed

fun reverse_guarded_coefficients :: "nat => nat => nat * nat" where
  "reverse_guarded_coefficients g 0 = (1,0)"
| "reverse_guarded_coefficients g (Suc n) =
     (let (a,b) = reverse_guarded_coefficients g n in ((g*a) mod 10,(g*b+1) mod 10))"

lemma reverse_guarded_coefficients_exact:
  fixes g d x :: nat
  shows "((\<lambda>r. (g*r+d) mod 10) ^^ n) (x mod 10) =
    (fst (reverse_guarded_coefficients g n)*x + snd (reverse_guarded_coefficients g n)*d) mod 10"
proof (induction n)
  case 0 then show ?case by simp
next
  case (Suc n)
  obtain a b where coeff: "reverse_guarded_coefficients g n=(a,b)" by (cases "reverse_guarded_coefficients g n")
  have step: "(g*((a*x+b*d) mod 10)+d) mod 10 = (g*(a*x+b*d)+d) mod 10"
    by (rule mod_add_cong; simp add: mod_simps)
  have norm: "(g*a*x+(g*b+1)*d) mod 10 = ((g*a mod 10)*x+((g*b+1) mod 10)*d) mod 10"
    by (rule mod_add_cong; simp add: mod_simps)
  have result: "(g*(a*x+b*d)+d) mod 10 = ((g*a mod 10)*x+((g*b+1) mod 10)*d) mod 10"
    using norm by (simp only: algebra_simps mult_1)
  show ?case by (simp only: funpow.simps o_apply Suc.IH coeff fst_conv snd_conv
      reverse_guarded_coefficients.simps Let_def case_prod_conv step result)
qed

definition reverse_guarded_multiple :: "nat => nat" where
  "reverse_guarded_multiple g = (if g=1 then 10 else if g=6 then 5 else if g=4 then 2 else 4)"

theorem reverse_guarded_affine_return:
  fixes g d r :: nat
  assumes slopes: "g=1 \<or> g=2 \<or> g=4 \<or> g=6 \<or> g=8"
  shows "((\<lambda>x. (g*x+d) mod 10) ^^ reverse_guarded_multiple g) ((g*r+d) mod 10) =
    (g*r+d) mod 10"
proof -
  let ?f = "\<lambda>x. (g*x+d) mod 10"
  have coeff: "reverse_guarded_coefficients g (Suc (reverse_guarded_multiple g))=(g,1)"
    using slopes by (elim disjE; hypsubst_thin; code_simp)
  have exact: "(?f ^^ Suc (reverse_guarded_multiple g)) (r mod 10)=(g*r+d) mod 10"
    using reverse_guarded_coefficients_exact[where g=g and d=d and n="Suc (reverse_guarded_multiple g)" and x=r]
    by (simp only: coeff fst_conv snd_conv; simp)
  have first: "?f (r mod 10)=?f r" by (rule mod_add_cong; simp add: mod_simps)
  show ?thesis using exact by (simp only: funpow_Suc_right o_apply first)
qed

fun reverse_guarded_row :: "(bool * nat * nat) list => nat * nat" where
  "reverse_guarded_row [] = (1,0)"
| "reverse_guarded_row ((birth,a,v)#ws) = (let (g,d)=reverse_guarded_row ws;
    h=(if birth then 1 else 2) in ((g*h) mod 10,(g*(a+v)+d) mod 10))"

lemma reverse_guarded_row_slopes:
  "fst (reverse_guarded_row ws) \<in> {1,2,4,6,8}"
proof (induction ws)
  case Nil then show ?case by simp
next
  case (Cons port ws)
  obtain birth a v where p: "port=(birth,a,v)" by (cases port) auto
  obtain g d where gd: "reverse_guarded_row ws=(g,d)" by (cases "reverse_guarded_row ws")
  from Cons.IH have "g=1 \<or> g=2 \<or> g=4 \<or> g=6 \<or> g=8" by (auto simp: gd)
  then show ?case by (elim disjE; cases birth; simp add: p gd)
qed

lemma reverse_guarded_row_exact:
  "fold (\<lambda>(birth,a,v). reverse_guarded_digit_pair birth a v) ws x mod 10 =
    (fst (reverse_guarded_row ws)*x + snd (reverse_guarded_row ws)) mod 10"
proof (induction ws arbitrary: x)
  case Nil then show ?case by simp
next
  case (Cons port ws)
  obtain birth a v where port: "port=(birth,a,v)" by (cases port) auto
  obtain g d where gd: "reverse_guarded_row ws=(g,d)" by (cases "reverse_guarded_row ws")
  let ?h = "if birth then 1 else 2::nat"
  let ?s = "reverse_guarded_digit_pair birth a v x"
  have residue: "?s mod 10 = (?h*x+(a+v)) mod 10" by (simp only: reverse_guarded_raw_residue add.assoc)
  have compose: "(g*?s+d) mod 10 = ((g*?h)*x+(g*(a+v)+d)) mod 10"
  proof -
    have "(g*?s+d) mod 10 = (g*(?h*x+(a+v))+d) mod 10"
      by (rule mod_add_cong, rule mod_mult_cong, rule refl, rule residue, rule refl)
    then show ?thesis by (simp only: algebra_simps)
  qed
  have norm: "((g*?h)*x+(g*(a+v)+d)) mod 10 =
      (((g*?h) mod 10)*x+((g*(a+v)+d) mod 10)) mod 10"
    by (rule mod_add_cong; simp add: mod_simps)
  show ?case by (simp only: port fold_Cons o_apply case_prod_conv Cons.IH gd fst_conv
    snd_conv reverse_guarded_row.simps Let_def compose norm)
qed

lemma reverse_guarded_word_raw_readout:
  assumes "x mod 10 = y mod 10"
  shows "fold (\<lambda>(birth,a,v). reverse_guarded_digit_pair birth a v) (port#ws) x =
    fold (\<lambda>(birth,a,v). reverse_guarded_digit_pair birth a v) (port#ws) y"
proof -
  obtain birth a v where p: "port=(birth,a,v)" by (cases port) auto
  have "reverse_guarded_digit_pair birth a v x = reverse_guarded_digit_pair birth a v y"
    using assms by (metis reverse_guarded_last_port)
  then show ?thesis by (simp only: p fold_Cons o_apply case_prod_conv)
qed

theorem reverse_guarded_word_return:
  fixes x :: nat and h :: "bool * nat * nat" and ws :: "(bool * nat * nat) list"
  defines "F \<equiv> fold (\<lambda>(birth,a,v). reverse_guarded_digit_pair birth a v) (h#ws)"
    and "g \<equiv> fst (reverse_guarded_row (h#ws))"
  shows "F ((F ^^ reverse_guarded_multiple g) (F x)) = F (F x)"
proof -
  let ?d = "snd (reverse_guarded_row (h#ws))"
  let ?f = "\<lambda>r. (g*r+?d) mod 10"
  have projection: "F y mod 10=?f y" for y unfolding F_def g_def by (rule reverse_guarded_row_exact)
  have lowered: "?f (y mod 10)=?f y" for y by (rule mod_add_cong; simp add: mod_simps)
  have iter: "(F ^^ n) y mod 10=(?f ^^ n) (y mod 10)" for n y
  proof (induction n)
    case 0 then show ?case by simp
  next
    case (Suc n)
    have step: "?f ((F^^n) y) = ?f ((?f^^n) (y mod 10))"
      using arg_cong[OF Suc.IH, where f="?f"] by (simp only: lowered)
    show ?case by (simp only: funpow.simps o_apply projection step)
  qed
  have slopes: "g=1 \<or> g=2 \<or> g=4 \<or> g=6 \<or> g=8" using reverse_guarded_row_slopes[of "h#ws"]
    by (auto simp: g_def)
  have same: "((F ^^ reverse_guarded_multiple g) (F x)) mod 10=F x mod 10"
    by (simp only: iter projection reverse_guarded_affine_return[OF slopes])
  show ?thesis unfolding F_def using reverse_guarded_word_raw_readout[OF same, of h ws]
    by (simp only: F_def)
qed

lemma reverse_guarded_equal_shells:
  "\<not> carry_out False (replicate k 9 @ [0,0] @ replicate k 9)"
  "carry_out False (replicate k 9 @ [10,10] @ replicate k 9)"
proof -
  have wire: "carry_out c (replicate n 9) = c" for c n
    by (induction n) (simp_all add: carry_out_def domain_def)
  have shell: "carry_out False (replicate k 9 @ middle @ replicate k 9) = carry_out False middle" for middle
    by (simp only: carry_out_append wire)
  show "\<not> carry_out False (replicate k 9 @ [0,0] @ replicate k 9)"
    by (subst shell; simp add: carry_out_def domain_def)
  show "carry_out False (replicate k 9 @ [10,10] @ replicate k 9)"
    by (subst shell; simp add: carry_out_def domain_def)
qed

ML \<open>
  val checked = @{thms reverse_guarded_slab_raw reverse_guarded_word_return reverse_guarded_equal_shells};
  val _ = if null (Thm_Deps.all_oracles checked) andalso not (Thm_Deps.has_skip_proof checked)
    then () else error "Unchecked conditioned decimal port period";
\<close>
end
