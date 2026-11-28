theory Reflected_Front_Physical
  imports Reflected_Front_Readiness
begin

text \<open>The four upstream columns are authenticated physical source
responses. Once they reach the five-phase trajectory, the incoming digit
collapses to that trajectory in one or two four-tick blocks.\<close>

lemma front_digit_range:
  "front_value m p t < 10"
proof -
  have length: "length (sync_word m) = 5" by (simp add: sync_word_def)
  have member: "sync_digit m q \<in> set (sync_word m)" for q
    unfolding sync_digit_def by (rule nth_mem) (simp add: length)
  have allowed: "\<forall>x\<in>set (sync_word m). x<10" by (simp add: sync_word_def)
  have selected: "sync_digit m ((p+20-4*(t mod 5)) mod 5) \<in> set (sync_word m)"
    by (rule member)
  show ?thesis using selected allowed by (auto simp: front_value_def)
qed

lemma front_response_time_mod:
  "front_response m p t x = front_response m p (t mod 5) x"
  by (simp add: front_response_def front_value_def)

lemma front_response_class_any_time:
  assumes radix: "m=2 \<or> m=5" and p: "p<5" and digit: "x<10"
  shows "front_response m p t x =
    front_response m p t (if front_port m x = 0 then 0 else if m=2 then 5 else 2)"
proof -
  have bound: "t mod 5 < 5" by simp
  note finite = front_response_two_classes[OF radix p bound digit]
  show ?thesis using finite by (simp add: front_response_def front_value_def)
qed

lemma front_response_digit:
  assumes radix: "m=2 \<or> m=5" and digit: "x<10"
  shows "front_response m p t x < 10"
proof -
  have gate: "reflected_source_two_gate m a b c < 10"
    if "a<10" "b<10" "c<10" for a b c
    using driven_closed[OF radix that, where moving=False]
    by (simp add: driven_digit_def)
  show ?thesis unfolding front_response_def front_four_gate_def
    using gate digit front_digit_range by meson
qed

lemma front_calibrated_response:
  assumes radix: "m=2 \<or> m=5" and p: "p<5"
  shows "front_response m p t (front_value m p t) = front_value m p (Suc t)"
proof -
  let ?q = "(p+20-4*(t mod 5)) mod 5"
  have qb: "?q<5" by simp
  have pc: "p=0 \<or> p=1 \<or> p=2 \<or> p=3 \<or> p=4" using p by arith
  have tc: "t mod 5=0 \<or> t mod 5=1 \<or> t mod 5=2 \<or> t mod 5=3 \<or> t mod 5=4" by presburger
  have align1: "front_value m (p+1) t = sync_digit m (?q+1)"
    using pc tc by (elim disjE; hypsubst_thin; simp add: front_value_def sync_digit_def numeral_2_eq_2)
  have align2: "front_value m (p+2) t = sync_digit m (?q+2)"
    using pc tc by (elim disjE; hypsubst_thin; simp add: front_value_def sync_digit_def numeral_2_eq_2)
  have align3: "front_value m (p+3) t = sync_digit m (?q+3)"
    using pc tc by (elim disjE; hypsubst_thin; simp add: front_value_def sync_digit_def numeral_2_eq_2)
  have align4: "front_value m (p+4) t = sync_digit m (?q+4)"
    using pc tc by (elim disjE; hypsubst_thin; simp add: front_value_def sync_digit_def numeral_2_eq_2)
  have tnext: "Suc t mod 5 = Suc (t mod 5) mod 5" by (rule mod_Suc_eq[symmetric])
  have align5: "front_value m p (Suc t) = sync_digit m (Suc ?q)"
    using pc tc tnext by (elim disjE; hypsubst_thin; simp add: front_value_def sync_digit_def numeral_2_eq_2)
  note align = align1 align2 align3 align4 align5
  note transition = sync_joint_transition[OF radix qb]
  have ordered: "front_response m p t (front_value m p t) =
      front_four_gate m (sync_digit m (?q+1)) (sync_digit m (?q+2))
        (sync_digit m (?q+3)) (sync_digit m (?q+4)) (sync_digit m ?q)"
    unfolding front_response_def
    apply (subst align(1))
    apply (subst align(2))
    apply (subst align(3))
    apply (subst align(4))
    by (simp only: front_value_def)
  have response: "front_response m p t (front_value m p t) =
      fst (seam_joint m (sync_port m ?q) (sync_digit m ?q))"
    by (simp only: ordered front_four_gate_def sync_port_def
        joint_seam_emits_ordered_four_tick_gate)
  show ?thesis using response transition align(5) by simp
qed

lemma front_class_equal_response:
  assumes radix: "m=2 \<or> m=5" and p: "p<5" and x: "x<10" and y: "y<10"
      and same: "front_port m x = front_port m y"
  shows "front_response m p t x = front_response m p t y"
  using front_response_class_any_time[OF radix p x, of t]
    front_response_class_any_time[OF radix p y, of t] same by simp

lemma front_constant_collapse:
  assumes radix: "m=2 \<or> m=5" and p: "p<5" and digit: "x<10"
    and collapse: "front_response m p t 0 = front_response m p t (if m=2 then 5 else 2)"
  shows "front_response m p t x = front_value m p (Suc t)"
proof -
  have first: "front_response m p t x = front_response m p t 0"
    using front_response_class_any_time[OF radix p digit, of t] collapse
    by (cases "front_port m x=0"; simp only: if_True if_False; metis)
  have reference: "front_response m p t (front_value m p t) = front_response m p t 0"
    using front_response_class_any_time[OF radix p front_digit_range, of t] collapse
    by (cases "front_port m (front_value m p t)=0"; simp only: if_True if_False; metis)
  show ?thesis using first reference front_calibrated_response[OF radix p, of t] by simp
qed

lemma front_two_tick_collapse:
  assumes radix: "m=2 \<or> m=5" and p: "p<5" and digit: "x<10"
    and collapse: "front_port m (front_response m p t 0) =
      front_port m (front_response m p t (if m=2 then 5 else 2))"
  shows "front_response m p (Suc t) (front_response m p t x) =
    front_value m p (Suc (Suc t))"
proof -
  have first_classes: "front_response m p t z = front_response m p t 0 \<or>
      front_response m p t z = front_response m p t (if m=2 then 5 else 2)" if "z<10" for z
    using front_response_class_any_time[OF radix p that, of t] by auto
  have equal:
    "front_response m p (Suc t) (front_response m p t x) =
      front_response m p (Suc t) (front_response m p t (front_value m p t))"
    by (rule front_two_stage_port_collapse[OF digit front_digit_range first_classes
          front_response_digit[OF radix] collapse front_class_equal_response[OF radix p]])
  show ?thesis using equal front_calibrated_response[OF radix p, of t]
    front_calibrated_response[OF radix p, of "Suc t"] by simp
qed


lemma front_upstream_step:
  fixes source :: "int \<Rightarrow> nat" and j :: int
  assumes upstream:
    "((joint_column m ^^ t) source) (j-4) = front_value m (p+1) t"
    "((joint_column m ^^ t) source) (j-3) = front_value m (p+2) t"
    "((joint_column m ^^ t) source) (j-2) = front_value m (p+3) t"
    "((joint_column m ^^ t) source) (j-1) = front_value m (p+4) t"
  shows "((joint_column m ^^ (Suc t)) source) j =
    front_response m p t (((joint_column m ^^ t) source) j)"
  using upstream
  by (simp only: funpow.simps comp_apply joint_column_def
      joint_seam_emits_ordered_four_tick_gate front_response_def front_four_gate_def)

lemma front_port_equal_step:
  assumes radix: "m=2 \<or> m=5" and phase: "p<5" and x: "x<10" and y: "y<10"
      and port: "front_port m x = front_port m y"
  shows "front_response m p t x = front_response m p t y"
  by (rule front_class_equal_response[OF radix phase x y port])

theorem front_physical_one_step_entry:
  fixes source :: "int \<Rightarrow> nat" and j :: int
  assumes radix: "m=2 \<or> m=5" and phase: "p<5"
      and digits: "\<And>i. source i<10"
      and upstream: "\<And>t. start \<le> t \<Longrightarrow>
        ((joint_column m ^^ t) source) (j-4) = front_value m (p+1) t"
        "\<And>t. start \<le> t \<Longrightarrow>
        ((joint_column m ^^ t) source) (j-3) = front_value m (p+2) t"
        "\<And>t. start \<le> t \<Longrightarrow>
        ((joint_column m ^^ t) source) (j-2) = front_value m (p+3) t"
        "\<And>t. start \<le> t \<Longrightarrow>
        ((joint_column m ^^ t) source) (j-1) = front_value m (p+4) t"
      and collapse: "front_response m p start 0 =
        front_response m p start (if m=2 then 5 else 2)"
  shows "((joint_column m ^^ (Suc start+n)) source) j = front_value m p (Suc start+n)"
proof (induction n)
  case 0
  have digit: "((joint_column m ^^ start) source) j < 10"
    by (rule joint_column_preserves_digits[OF radix digits])
  have local: "((joint_column m ^^ Suc start) source) j =
      front_response m p start (((joint_column m ^^ start) source) j)"
    apply (rule front_upstream_step)
       apply (rule upstream(1); simp)
      apply (rule upstream(2); simp)
     apply (rule upstream(3); simp)
    by (rule upstream(4); simp)
  show ?case using local front_constant_collapse[OF radix phase digit collapse] by simp
next
  case (Suc n)
  let ?t = "Suc start+n"
  have local: "((joint_column m ^^ Suc ?t) source) j =
      front_response m p ?t (((joint_column m ^^ ?t) source) j)"
    apply (rule front_upstream_step)
       apply (rule upstream(1); simp)
      apply (rule upstream(2); simp)
     apply (rule upstream(3); simp)
    by (rule upstream(4); simp)
  show ?case using local Suc.IH front_calibrated_response[OF radix phase, of ?t]
    by simp
qed

theorem front_physical_two_step_entry:
  fixes source :: "int \<Rightarrow> nat" and j :: int
  assumes radix: "m=2 \<or> m=5" and phase: "p<5"
      and digits: "\<And>i. source i<10"
      and upstream: "\<And>t. start \<le> t \<Longrightarrow>
        ((joint_column m ^^ t) source) (j-4) = front_value m (p+1) t"
        "\<And>t. start \<le> t \<Longrightarrow>
        ((joint_column m ^^ t) source) (j-3) = front_value m (p+2) t"
        "\<And>t. start \<le> t \<Longrightarrow>
        ((joint_column m ^^ t) source) (j-2) = front_value m (p+3) t"
        "\<And>t. start \<le> t \<Longrightarrow>
        ((joint_column m ^^ t) source) (j-1) = front_value m (p+4) t"
      and collapse: "front_port m (front_response m p start 0) =
        front_port m (front_response m p start (if m=2 then 5 else 2))"
  shows "((joint_column m ^^ (Suc (Suc start)+n)) source) j =
    front_value m p (Suc (Suc start)+n)"
proof (induction n)
  case 0
  have digit: "((joint_column m ^^ start) source) j < 10"
    by (rule joint_column_preserves_digits[OF radix digits])
  have first: "((joint_column m ^^ Suc start) source) j =
      front_response m p start (((joint_column m ^^ start) source) j)"
    apply (rule front_upstream_step)
       apply (rule upstream(1); simp)
      apply (rule upstream(2); simp)
     apply (rule upstream(3); simp)
    by (rule upstream(4); simp)
  have second: "((joint_column m ^^ Suc (Suc start)) source) j =
      front_response m p (Suc start) (((joint_column m ^^ Suc start) source) j)"
    apply (rule front_upstream_step)
       apply (rule upstream(1); simp)
      apply (rule upstream(2); simp)
     apply (rule upstream(3); simp)
    by (rule upstream(4); simp)
  show ?case using first second front_two_tick_collapse[OF radix phase digit collapse] by simp
next
  case (Suc n)
  let ?t = "Suc (Suc start)+n"
  have local: "((joint_column m ^^ Suc ?t) source) j =
      front_response m p ?t (((joint_column m ^^ ?t) source) j)"
    apply (rule front_upstream_step)
       apply (rule upstream(1); simp)
      apply (rule upstream(2); simp)
     apply (rule upstream(3); simp)
    by (rule upstream(4); simp)
  show ?case using local Suc.IH front_calibrated_response[OF radix phase, of ?t]
    by simp
qed



corollary front_one_step_physical_source:
  fixes source :: "int \<Rightarrow> nat" and k j :: int
  assumes radix: "m=2 \<or> m=5" and phase: "p<5"
      and digits: "\<And>i. source i<10"
      and upstream: "\<And>t. start \<le> t \<Longrightarrow>
        ((joint_column m ^^ t) (\<lambda>i. source (k-i))) (j-4) = front_value m (p+1) t"
        "\<And>t. start \<le> t \<Longrightarrow>
        ((joint_column m ^^ t) (\<lambda>i. source (k-i))) (j-3) = front_value m (p+2) t"
        "\<And>t. start \<le> t \<Longrightarrow>
        ((joint_column m ^^ t) (\<lambda>i. source (k-i))) (j-2) = front_value m (p+3) t"
        "\<And>t. start \<le> t \<Longrightarrow>
        ((joint_column m ^^ t) (\<lambda>i. source (k-i))) (j-1) = front_value m (p+4) t"
      and collapse: "front_response m p start 0 =
        front_response m p start (if m=2 then 5 else 2)"
  shows "reflected_single_run (reflected_alternating_gate m) (4*(Suc start+n)) source
      (k+4*int (Suc start+n)-j) = front_value m p (Suc start+n)"
proof -
  have initial_digits: "(\<lambda>i. source (k-i)) i<10" for i by (rule digits)
  note entry = front_physical_one_step_entry[OF radix phase initial_digits upstream collapse, of n]
  show ?thesis using entry by (simp only: joint_column_physical_four_tick_run)
qed

corollary front_two_step_physical_source:
  fixes source :: "int \<Rightarrow> nat" and k j :: int
  assumes radix: "m=2 \<or> m=5" and phase: "p<5"
      and digits: "\<And>i. source i<10"
      and upstream: "\<And>t. start \<le> t \<Longrightarrow>
        ((joint_column m ^^ t) (\<lambda>i. source (k-i))) (j-4) = front_value m (p+1) t"
        "\<And>t. start \<le> t \<Longrightarrow>
        ((joint_column m ^^ t) (\<lambda>i. source (k-i))) (j-3) = front_value m (p+2) t"
        "\<And>t. start \<le> t \<Longrightarrow>
        ((joint_column m ^^ t) (\<lambda>i. source (k-i))) (j-2) = front_value m (p+3) t"
        "\<And>t. start \<le> t \<Longrightarrow>
        ((joint_column m ^^ t) (\<lambda>i. source (k-i))) (j-1) = front_value m (p+4) t"
      and collapse: "front_port m (front_response m p start 0) =
        front_port m (front_response m p start (if m=2 then 5 else 2))"
  shows "reflected_single_run (reflected_alternating_gate m) (4*(Suc (Suc start)+n)) source
      (k+4*int (Suc (Suc start)+n)-j) = front_value m p (Suc (Suc start)+n)"
proof -
  have initial_digits: "(\<lambda>i. source (k-i)) i<10" for i by (rule digits)
  note entry = front_physical_two_step_entry[OF radix phase initial_digits upstream collapse, of n]
  show ?thesis using entry by (simp only: joint_column_physical_four_tick_run)
qed

ML \<open>
  val checked = @{thms front_calibrated_response front_constant_collapse front_two_tick_collapse
    front_physical_one_step_entry front_physical_two_step_entry
    front_one_step_physical_source front_two_step_physical_source};
  val _ = if null (Thm_Deps.all_oracles checked) then () else error "front physical collapse uses an oracle";
  val _ = if Thm_Deps.has_skip_proof checked then error "front physical collapse has skipped proofs" else ();
\<close>

end
