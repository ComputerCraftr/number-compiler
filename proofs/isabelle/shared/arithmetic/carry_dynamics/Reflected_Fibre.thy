theory Reflected_Fibre
  imports Reflected_Annulus_Return
begin

definition driven_digit where
  "driven_digit m moving ab x = (if moving then reflected_source_two_gate m x (fst ab) (snd ab)
    else reflected_source_two_gate m (fst ab) (snd ab) x)"

definition two_image :: "(nat => nat) => bool" where
  "two_image f = (\<exists>a b. \<forall>x<10. f x=a \<or> f x=b)"

lemma digit_gate_closed:
  fixes m a b :: nat
  assumes "m=2 \<or> m=5" "a<10" "b<10"
  shows "m*(a mod (10 div m)) + b div (10 div m) < 10"
  using assms by (elim disjE; simp; presburger)

lemma driven_closed:
  assumes "m=2 \<or> m=5" "a<10" "b<10" "x<10"
  shows "driven_digit m moving (a,b) x < 10"
  using assms by (cases moving; simp only: driven_digit_def reflected_source_two_gate_def
      fst_conv snd_conv if_True if_False Let_def; (intro digit_gate_closed assms))

lemma driven_two_image:
  assumes "m=2 \<or> m=5" "a<10" "b<10"
  shows "two_image (driven_digit m moving (a,b))"
proof -
  have halves: "z div 5 = 0 \<or> z div 5 = 1" if "z<10" for z::nat using that by presburger
  have bits: "z mod 2 = 0 \<or> z mod 2 = 1" for z::nat by presburger
  consider "m=2" "moving" | "m=2" "\<not>moving" | "m=5" "moving" | "m=5" "\<not>moving"
    using assms by auto
  then show ?thesis
  proof cases
    case 1
    let ?f = "\<lambda>k. 2*((2*(a mod 5)+k) mod 5) + (2*(b mod 5)+a div 5) div 5"
    show ?thesis unfolding two_image_def
    proof (rule exI[of _ "?f 0"], rule exI[of _ "?f 1"], intro allI impI)
      fix x::nat assume "x<10"
      from halves[OF this] show "driven_digit m moving (a,b) x = ?f 0 \<or> driven_digit m moving (a,b) x = ?f 1"
        by (elim disjE; simp add: driven_digit_def reflected_source_two_gate_def 1)
    qed
  next
    case 2
    let ?u = "2*((2*(b mod 5)+a div 5) mod 5)"
    show ?thesis unfolding two_image_def
    proof (rule exI[of _ ?u], rule exI[of _ "?u+1"], intro allI impI)
      fix x::nat assume x: "x<10"
      have h: "2*(x mod 5)+b div 5<10" using digit_gate_closed[of 2 x b] x assms by simp
      from halves[OF h] show "driven_digit m moving (a,b) x = ?u \<or> driven_digit m moving (a,b) x = ?u+1"
        by (elim disjE; simp add: driven_digit_def reflected_source_two_gate_def 2)
    qed
  next
    case 3
    let ?v = "(5*(b mod 2)+a div 2) div 2"
    show ?thesis unfolding two_image_def
    proof (rule exI[of _ ?v], rule exI[of _ "5+?v"], intro allI impI)
      fix x::nat assume "x<10"
      from bits[of "5*(a mod 2)+x div 2"] show "driven_digit m moving (a,b) x = ?v \<or> driven_digit m moving (a,b) x = 5+?v"
        by (elim disjE; simp add: driven_digit_def reflected_source_two_gate_def 3)
    qed
  next
    case 4
    let ?f = "\<lambda>k. 5*((5*(b mod 2)+a div 2) mod 2) + (5*k+b div 2) div 2"
    show ?thesis unfolding two_image_def
    proof (rule exI[of _ "?f 0"], rule exI[of _ "?f 1"], intro allI impI)
      fix x::nat assume "x<10"
      from bits[of x] show "driven_digit m moving (a,b) x = ?f 0 \<or> driven_digit m moving (a,b) x = ?f 1"
        by (elim disjE; simp add: driven_digit_def reflected_source_two_gate_def 4)
    qed
  qed
qed

lemma two_image_composition:
  "two_image f \<Longrightarrow> two_image (g o f)"
proof -
  assume "two_image f"
  then obtain a b where image: "\<And>x. x<10 \<Longrightarrow> f x=a \<or> f x=b" unfolding two_image_def by blast
  show ?thesis unfolding two_image_def by (intro exI[of _ "g a"] exI[of _ "g b"]) (auto dest!: image)
qed

lemma driven_block_rank:
  assumes "two_image (driven_digit m side h)"
  shows "two_image (fold (driven_digit m side) (h#tail))"
  using two_image_composition[OF assms, of "fold (driven_digit m side) tail"]
  by (simp add: fold_Cons)

lemma two_image_eventual_square:
  assumes rank: "two_image f" and closed: "\<And>x. x<10 \<Longrightarrow> f x<10" and x: "x<10"
  shows "f (f (f (f x))) = f (f x)"
proof -
  obtain a b where two: "\<And>x. x<10 \<Longrightarrow> f x=a \<or> f x=b"
    using rank unfolding two_image_def by blast
  have "f x=f(f x) \<or> f x=f(f(f x)) \<or> f(f x)=f(f(f x))"
    using two[OF x] two[OF closed[OF x]] two[OF closed[OF closed[OF x]]] by (elim disjE; metis)
  then show ?thesis by metis
qed

lemma two_image_residual:
  assumes h: "f (f (f (f x))) = f (f x)"
  shows "(f ^^ (2 + k)) x = (f ^^ (2 + k mod 2)) x"
proof (induction k rule: less_induct)
  case (less k)
  show ?case
  proof (cases "k<2")
    case True then show ?thesis by simp
  next
    case False
    obtain j where k: "k=j+2" by (rule that[of "k-2"]; use False in presburger)
    have four: "(f^^4) x=(f^^2) x" using h by (simp add: numeral_eq_Suc)
    have lift: "(f ^^ (j+4)) x = (f ^^ (j+2)) x"
      by (simp only: funpow_add o_apply four)
    have a: "2+k=j+4" using k by arith
    have b: "j+2=2+j" by arith
    have c: "k mod 2=j mod 2" by (simp add: k)
    have ih: "(f^^(2+j)) x=(f^^(2+j mod 2)) x" by (rule less.IH; use k in arith)
    show ?thesis by (simp only: a lift b ih c)
  qed
qed
definition fibre_position :: "bool => int => nat => int" where
  "fibre_position moving i t = (if moving then i+2*int t else i)"

theorem reflected_extreme_fibre_step:
  fixes s :: "int => nat" and m t :: nat and moving :: bool and i :: int
  defines "row \<equiv> \<lambda>k. reflected_single_run (reflected_alternating_gate m) (2*k) s"
    and "j \<equiv> fibre_position moving i t"
  assumes ports: "ab = (if moving then (row t (j+1),row t (j+2)) else (row t (j-2),row t (j-1)))"
  shows "row (Suc t) (fibre_position moving i (Suc t)) = driven_digit m moving ab (row t j)"
  unfolding row_def ports driven_digit_def j_def reflected_single_run_even
  by (cases moving; simp add: fibre_position_def reflected_relative_two_def algebra_simps)


lemma driven_span_fold:
  assumes step: "\<And>t. response (Suc t) = driven_digit m moving (ports t) (response t)"
  shows "fold (driven_digit m moving) (map ports [start..<start+n]) (response start) = response (start+n)"
  by (induction n) (simp_all add: step)

lemma periodic_fibre_power:
  assumes closed: "\<And>y. y<10 \<Longrightarrow> f y<10" and rank: "two_image f"
    and inlet: "x<10" and boundary: "response 0=x" "\<And>n. response (Suc n)=f (response n)"
  shows "response blocks = (f ^^ (if blocks<2 then blocks else 2+(blocks mod 2))) x"
proof -
  have exact: "response n = (f ^^ n) x" for n by (induction n) (simp_all add: boundary)
  have sq: "f (f (f (f x))) = f (f x)" by (rule two_image_eventual_square[OF rank closed inlet])
  show ?thesis
  proof (cases "blocks<2")
    case True then show ?thesis by (simp add: exact)
  next
    case False obtain k where "blocks=2+k" by (rule that[of "blocks-2"]; use False in presburger)
    then show ?thesis using two_image_residual[OF sq, of k] by (simp add: exact)
  qed
qed

theorem driven_periodic_terminal:
  assumes radix: "m=2 \<or> m=5" and ports_valid: "\<And>a b. (a,b)\<in>set (h#tail) \<Longrightarrow> a<10 \<and> b<10"
    and start: "response 0<10"
    and step: "\<And>t. response (Suc t)=driven_digit m moving (ports t) (response t)"
    and drive: "\<And>k. k<blocks \<Longrightarrow> map ports [k*length (h#tail)..<(k+1)*length (h#tail)] = h#tail"
  defines "f \<equiv> fold (driven_digit m moving) (h#tail)"
  shows "response (blocks * length (h#tail)) = (f ^^ (if blocks<2 then blocks else 2+blocks mod 2)) (response 0)"
proof -
  have closed: "fold (driven_digit m moving) word y<10"
    if "set word \<subseteq> set (h#tail)" "y<10" for word y
    using that
  proof (induction word arbitrary: y)
    case Nil then show ?case by simp
  next
    case (Cons ab word)
    obtain a b where ab: "ab=(a,b)" by (cases ab) auto
    have valid: "a<10 \<and> b<10" by (rule ports_valid) (use Cons.prems ab in auto)
    have digit: "driven_digit m moving ab y<10" unfolding ab by (rule driven_closed[OF radix]; use valid Cons.prems in simp)
    show ?case using Cons.IH[of "driven_digit m moving ab y"] digit Cons.prems by simp
  qed
  have r: "two_image f" unfolding f_def
    by (rule driven_block_rank; cases h; simp; rule driven_two_image[OF radix]; use ports_valid in auto)
  let ?p = "length (h#tail)"
  have v: "response (k*?p)=(f^^k) (response 0)" if "k\<le>blocks" for k
    using that
  proof (induction k)
    case 0 then show ?case by simp
  next
    case (Suc k)
    have eq: "map ports [k*?p..<k*?p+?p]=h#tail" using drive[of k] Suc.prems by (simp only: add_mult_distrib mult_1; auto)
    have k: "k\<le>blocks" using Suc.prems by simp
    have end_at: "Suc k*?p=k*?p+?p" by (simp only: mult_Suc; arith)
    have span: "response (k*?p+?p) = f (response (k*?p))"
      using driven_span_fold[where response=response and m=m and moving=moving and ports=ports
        and start="k*?p" and n="?p", OF step, symmetric]
      by (simp only: eq f_def)
    show ?case by (simp only: end_at span Suc.IH[OF k] funpow.simps o_apply)
  qed
  show ?thesis using v[of blocks] periodic_fibre_power[where response="\<lambda>k. (f^^k) (response 0)" and blocks=blocks,
    OF _ r start] closed[of "h#tail"] by (simp add: f_def)
qed

text \<open>For a stationary column take the two preceding inlet positions.
For a column travelling at two cells per pair take the two following inlet
positions. Apply this law at each position with its own complete halo.\<close>
theorem reflected_extreme_source_inlet:
  fixes a b i :: int and moving :: bool
  defines "shift \<equiv> (if moving then 2 else 0::int)"
  assumes ret: "\<And>j. a+2\<le>j \<Longrightarrow> j<b \<Longrightarrow>
    reflected_relative_two (reflected_source_two_gate m) source j = source (j-shift)"
    and halo: "a+2*int t \<le> fibre_position moving i t" "fibre_position moving i t < b"
  shows "reflected_single_run (reflected_alternating_gate m) (2*t) source (fibre_position moving i t) = source i"
proof -
  have bounds: "0\<le>shift" "shift\<le>2" by (simp_all add: shift_def)
  show ?thesis using reflected_single_run_even_relative[OF bounds ret halo]
    by (cases moving; simp add: fibre_position_def shift_def)
qed

theorem reflected_uniform_source_inlet:
  assumes radix: "m\<in>{2,5}" "d<10"
    and halo: "\<And>j. i-2*int t\<le>j \<Longrightarrow> j\<le>i \<Longrightarrow> source j=d"
  shows "reflected_single_run (reflected_alternating_gate m) (2*t) source i =
    (uniform_reflected_digit m ^^ (2*(t mod 3))) d"
proof -
  have h: "\<And>j. i-int(2*t)\<le>j \<Longrightarrow> j\<le>i \<Longrightarrow> source j=d" by (simp add: halo)
  have clock: "(2*t) mod 6 = 2*(t mod 3)" by presburger
  show ?thesis using uniform_reflected_annulus[where n="2*t" and i=i and source=source, OF radix h]
    by (simp only: clock)
qed

ML \<open>
  val checked = @{thms driven_periodic_terminal reflected_extreme_fibre_step
    reflected_uniform_source_inlet reflected_extreme_source_inlet};
  val _ = if null (Thm_Deps.all_oracles checked) andalso not (Thm_Deps.has_skip_proof checked)
    then () else error "Unchecked reflected fibre transport";
\<close>
end
