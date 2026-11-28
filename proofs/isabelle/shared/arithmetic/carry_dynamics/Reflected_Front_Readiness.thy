theory Reflected_Front_Readiness
  imports Reflected_Joint_Seam
begin

text \<open>The front action is conditional on a receiving physical source.
The two input classes and the finite readiness chart establish only the
continuation after the four upstream ports and physical clock are issued.\<close>

definition front_port :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "front_port m d = (if m = 2 then d div 5 else (d div 2) mod 2)"

definition front_four_gate :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "front_four_gate m a b c d e =
    reflected_source_two_gate m (reflected_source_two_gate m e d c)
      (reflected_source_two_gate m d c b) (reflected_source_two_gate m c b a)"

definition front_value :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "front_value m p t = sync_digit m ((p + 20 - 4*(t mod 5)) mod 5)"

definition front_response :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "front_response m p t x = front_four_gate m
    (front_value m (p+1) t) (front_value m (p+2) t)
    (front_value m (p+3) t) (front_value m (p+4) t) x"

lemma front_response_two_classes:
  assumes radix: "m=2 \<or> m=5" and p: "p<5" and t: "t<5" and x: "x<10"
  shows "front_response m p t x =
    front_response m p t (if front_port m x = 0 then 0 else if m=2 then 5 else 2)"
proof -
  have p_cases: "p=0 \<or> p=1 \<or> p=2 \<or> p=3 \<or> p=4" using p by arith
  have t_cases: "t=0 \<or> t=1 \<or> t=2 \<or> t=3 \<or> t=4" using t by arith
  have x_cases: "x=0 \<or> x=1 \<or> x=2 \<or> x=3 \<or> x=4 \<or> x=5 \<or> x=6 \<or> x=7 \<or> x=8 \<or> x=9" using x by arith
  show ?thesis using radix p_cases t_cases x_cases
    by (elim disjE; hypsubst_thin; code_simp)
qed

lemma front_two_stage_port_collapse:
  fixes first second :: "nat \<Rightarrow> nat" and port :: "nat \<Rightarrow> nat"
  assumes inlets: "x<10" "y<10"
      and first_classes: "\<And>z. z<10 \<Longrightarrow> first z=lo \<or> first z=hi"
      and closed: "\<And>z. z<10 \<Longrightarrow> first z<10"
      and same_port: "port lo=port hi"
      and second_classes: "\<And>a b. a<10 \<Longrightarrow> b<10 \<Longrightarrow>
        port a=port b \<Longrightarrow> second a=second b"
  shows "second (first x) = second (first y)"
  by (rule second_classes[OF closed[OF inlets(1)] closed[OF inlets(2)]])
    (use first_classes[OF inlets(1)] first_classes[OF inlets(2)] same_port in auto)

definition front_ready_base :: "nat \<Rightarrow> nat list" where
  "front_ready_base m = (if m=2 then [0,0,1,0,0] else [2,0,1,0,0])"

definition front_ready_table :: "nat \<Rightarrow> nat list list" where
  "front_ready_table m = (if m=2 then
     [[2,4,5,7,8,10,11,13,14,16,17,19],
      [1,3,4,6,7,9,10,12,13,15,16,18],
      [1,2,3,5,6,8,9,11,12,14,15,17],
      [2,3,5,6,8,9,11,12,14,15,17,18],
      [1,2,4,5,7,8,10,11,13,14,16,17]]
   else
     [[1,2,3,4,6,7,9,10,12,13,15,16],
      [1,3,4,6,7,9,10,12,13,15,16,18],
      [1,2,3,5,6,8,9,11,12,14,15,17],
      [2,3,5,6,8,9,11,12,14,15,17,18],
      [1,2,4,5,7,8,10,11,13,14,16,17]])"

definition front_ready :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "front_ready m p i = (let base = front_ready_base m ! p;
      row = front_ready_table m ! p
    in if i < base then row ! i
       else row ! (base + ((i-base) mod 10)) + 15*((i-base) div 10))"

definition front_delay :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "front_delay m p t = (let lo = front_response m p t 0;
      hi = front_response m p t (if m=2 then 5 else 2)
    in if lo=hi then 1 else if front_port m lo = front_port m hi then 2 else 1000)"

definition front_min5 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "front_min5 a b c d e = min a (min b (min c (min d e)))"

definition front_next :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "front_next m p i earliest = earliest + front_min5
    (front_delay m ((p+i) mod 5) (earliest mod 5))
    (1 + front_delay m ((p+i) mod 5) ((earliest+1) mod 5))
    (2 + front_delay m ((p+i) mod 5) ((earliest+2) mod 5))
    (3 + front_delay m ((p+i) mod 5) ((earliest+3) mod 5))
    (4 + front_delay m ((p+i) mod 5) ((earliest+4) mod 5))"

lemma front_next_translation:
  "front_next m p (i+10) (earliest+15) = front_next m p i earliest+15"
proof -
  have column: "(i+(p+10)) mod (5::nat) = (i+p) mod 5" by presburger
  have time: "(earliest+15+k) mod (5::nat) = (earliest+k) mod 5" for k
    by presburger
  show ?thesis
    using time[of 0] time[of 1] time[of 2] time[of 3] time[of 4]
    by (simp add: front_next_def column algebra_simps)
qed

fun front_generated_state :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list" where
  "front_generated_state m p 0 = [0,0,0,0]"
| "front_generated_state m p (Suc i) =
    (case front_generated_state m p i of [a,b,c,d] \<Rightarrow>
      [b,c,d,front_next m p i (max a (max b (max c d)))] | _ \<Rightarrow> [])"

definition front_generated :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "front_generated m p i = last (front_generated_state m p (Suc i))"

definition front_prior :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "front_prior m p i k = (if i+k < 4 then 0 else front_ready m p (i+k-4))"

definition front_recurrence :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "front_recurrence m p i \<longleftrightarrow> front_ready m p i =
    front_next m p i (max (front_prior m p i 0) (max (front_prior m p i 1)
      (max (front_prior m p i 2) (front_prior m p i 3))))"

definition front_finite_certificate :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "front_finite_certificate m p =
    list_all (front_recurrence m p) [0..<16]"

lemma front_finite_certificates:
  "front_finite_certificate 2 0" "front_finite_certificate 2 1"
  "front_finite_certificate 2 2" "front_finite_certificate 2 3"
  "front_finite_certificate 2 4" "front_finite_certificate 5 0"
  "front_finite_certificate 5 1" "front_finite_certificate 5 2"
  "front_finite_certificate 5 3" "front_finite_certificate 5 4"
  by (code_simp)+

lemma front_ready_translation:
  assumes "front_ready_base m ! p \<le> i"
  shows "front_ready m p (i+10) = front_ready m p i+15"
proof -
  let ?base = "front_ready_base m ! p"
  have index: "i+10-?base = (i-?base)+10" using assms by arith
  have bounds: "\<not> i < ?base" "\<not> i+10 < ?base" using assms by arith+
  show ?thesis
    by (simp add: front_ready_def Let_def bounds index add.commute add.left_commute
      div_add_self1 div_add_self2 mod_add_self2)
qed

lemma front_ready_preperiods:
  assumes "p<5"
  shows "front_ready_base 2 ! p \<le> 1" "front_ready_base 5 ! p \<le> 2"
proof -
  have cases: "p=0 \<or> p=1 \<or> p=2 \<or> p=3 \<or> p=4" using assms by arith
  show "front_ready_base 2 ! p \<le> 1" "front_ready_base 5 ! p \<le> 2"
    using cases by (elim disjE; hypsubst_thin; simp add: front_ready_base_def)+
qed

lemma front_prior_translation:
  assumes admitted: "front_ready_base m ! p + 4 \<le> i"
  shows "front_prior m p (i+10) k = front_prior m p i k + 15"
proof -
  have bound: "front_ready_base m ! p \<le> i+k-4" using admitted by arith
  have positive: "\<not> i+k<4" "\<not> i+10+k<4" using admitted by arith+
  have index: "i+10+k-4 = (i+k-4)+10" using admitted by arith
  show ?thesis
    using front_ready_translation[OF bound] positive
    by (simp add: front_prior_def index)
qed

lemma front_recurrence_translation:
  assumes admitted: "front_ready_base m ! p + 4 \<le> i"
  shows "front_recurrence m p (i+10) \<longleftrightarrow> front_recurrence m p i"
proof -
  have ready: "front_ready m p (i+10) = front_ready m p i+15"
    by (rule front_ready_translation) (use admitted in arith)
  have max_shift: "max (a+15) (b+15) = max a b+15" for a b :: nat
    by (simp add: max_def)
  show ?thesis
    by (simp only: front_recurrence_def ready front_prior_translation[OF admitted]
        max_shift front_next_translation add_right_cancel)
qed

theorem front_recurrence_all_columns:
  assumes radix: "m=2 \<or> m=5" and phase: "p<5"
  shows "front_recurrence m p i"
proof -
  have cases: "p=0 \<or> p=1 \<or> p=2 \<or> p=3 \<or> p=4" using phase by arith
  have finite: "front_finite_certificate m p"
    using radix cases front_finite_certificates
    by blast
  have initial: "front_recurrence m p j" if "j<16" for j
    using finite that by (simp add: front_finite_certificate_def list_all_iff)
  have base: "front_ready_base m ! p \<le> 2"
    using radix front_ready_preperiods[OF phase] by auto
  show ?thesis
  proof (induction i rule: less_induct)
    case (less i)
    show ?case
    proof (cases "i<16")
      case True then show ?thesis by (rule initial)
    next
      case False
      let ?j = "i-10"
      have below: "?j<i" and admitted: "front_ready_base m ! p + 4 \<le> ?j"
        and index: "?j+10=i" using False base by arith+
      have "front_recurrence m p ?j" by (rule less.IH[OF below])
      with front_recurrence_translation[OF admitted] index show ?thesis by simp
    qed
  qed
qed

lemma front_prior_advance:
  "front_prior m p (Suc i) 0 = front_prior m p i 1"
  "front_prior m p (Suc i) 1 = front_prior m p i 2"
  "front_prior m p (Suc i) 2 = front_prior m p i 3"
  "front_prior m p (Suc i) 3 = front_ready m p i"
  by (simp_all add: front_prior_def)

theorem front_generated_state_refinement:
  assumes radix: "m=2 \<or> m=5" and phase: "p<5"
  shows "front_generated_state m p i =
    [front_prior m p i 0, front_prior m p i 1,
     front_prior m p i 2, front_prior m p i 3]"
proof (induction i)
  case 0
  then show ?case by (simp add: front_prior_def)
next
  case (Suc i)
  have recurrence: "front_ready m p i =
    front_next m p i (max (front_prior m p i 0) (max (front_prior m p i 1)
      (max (front_prior m p i 2) (front_prior m p i 3))))"
    using front_recurrence_all_columns[OF radix phase, of i]
    by (simp only: front_recurrence_def)
  have middle: "front_prior m p i 2 = front_prior m p (Suc i) (Suc 0)"
    using front_prior_advance(2)[of m p i] by simp
  show ?case
    using middle by (simp add: Suc.IH front_prior_advance recurrence)
qed

corollary front_generated_ready:
  assumes "m=2 \<or> m=5" "p<5"
  shows "front_generated m p i = front_ready m p i"
  using front_generated_state_refinement[OF assms, of "Suc i"]
  by (simp add: front_generated_def front_prior_advance)

ML \<open>
  val checked = @{thms front_response_two_classes front_two_stage_port_collapse
    front_ready_translation front_ready_preperiods
    front_next_translation front_finite_certificates front_recurrence_all_columns
    front_generated_state_refinement front_generated_ready};
  val _ = if null (Thm_Deps.all_oracles checked) then () else error "front readiness uses an oracle";
  val _ = if Thm_Deps.has_skip_proof checked then error "front readiness has skipped proofs" else ();
\<close>

end
