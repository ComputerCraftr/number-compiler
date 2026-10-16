theory Mahler_Joint_Quotient_Algebra
  imports Mahler_Source_Event_Safety
begin

text \<open>The branch address is an observer of an already selected source path.
Entries are one-based sibling indices. In particular, they are not the
source's even-run exponents. This definition is the list semantics of the
bounded base-three value stored by BranchChoiceSuffix.\<close>

definition branch_suffix :: "nat list \<Rightarrow> nat list" where
  "branch_suffix xs = rev (take 6 (rev xs))"

definition branch_then :: "nat list \<Rightarrow> nat list \<Rightarrow> nat list" where
  "branch_then xs ys = branch_suffix (xs @ ys)"

lemma branch_suffix_length: "length (branch_suffix xs) = min 6 (length xs)"
  by (simp add: branch_suffix_def)

lemma branch_suffix_valid:
  assumes "\<forall>x\<in>set xs. 1 \<le> x \<and> x \<le> 3"
  shows "\<forall>x\<in>set (branch_suffix xs). 1 \<le> x \<and> x \<le> 3"
proof -
  have parts: "take 6 (rev xs) @ drop 6 (rev xs) = rev xs" by simp
  have subset: "set (take 6 (rev xs)) \<subseteq> set (rev xs)"
  proof
    fix x assume member: "x \<in> set (take 6 (rev xs))"
    have "x \<in> set (take 6 (rev xs) @ drop 6 (rev xs))"
      using member by (simp only: set_append; blast)
    then show "x \<in> set (rev xs)" by (simp only: parts)
  qed
  have "set (branch_suffix xs) \<subseteq> set xs"
    using subset by (simp add: branch_suffix_def)
  then show ?thesis using assms by blast
qed

lemma take_six_right:
  "take 6 (ys @ xs) = take 6 (ys @ take 6 xs)"
  by (simp add: take_append)

lemma take_six_left:
  "take 6 (take 6 xs @ ys) = take 6 (xs @ ys)"
  by (cases "length xs \<le> 6"; simp add: take_append)

lemma branch_suffix_then:
  "branch_suffix (xs @ ys) = branch_suffix (branch_suffix xs @ ys)"
  by (simp add: branch_suffix_def take_six_right)

lemma branch_suffix_last:
  "branch_suffix (xs @ ys) = branch_suffix (xs @ branch_suffix ys)"
  by (cases "length ys \<le> 6"; simp add: branch_suffix_def take_six_left take_append)

lemma branch_then_assoc:
  "branch_then (branch_then xs ys) zs = branch_then xs (branch_then ys zs)"
  by (simp add: branch_then_def branch_suffix_then[symmetric]
    branch_suffix_last[symmetric] append_assoc)

lemma branch_suffix_idempotent: "branch_suffix (branch_suffix xs) = branch_suffix xs"
  by (simp add: branch_suffix_def)

definition branch_code :: "nat list \<Rightarrow> nat" where
  "branch_code xs = foldl (\<lambda>n x. 3*n + (x-1)) 0 xs"

definition encoded_branch_suffix :: "nat list \<Rightarrow> nat \<times> nat" where
  "encoded_branch_suffix xs =
    (length (branch_suffix xs), branch_code (branch_suffix xs))"

lemma branch_code_append_choice:
  "branch_code (xs @ [choice]) = 3 * branch_code xs + (choice-1)"
  by (simp add: branch_code_def)

lemma branch_code_bounded:
  assumes "\<forall>x\<in>set xs. 1 \<le> x \<and> x \<le> 3"
  shows "branch_code xs < 3 ^ length xs"
  using assms
proof (induct xs rule: rev_induct)
  case Nil
  then show ?case by (simp add: branch_code_def)
next
  case (snoc x xs)
  have old: "branch_code xs < 3 ^ length xs"
    using snoc.prems snoc.hyps by auto
  have digit: "1 \<le> x" "x \<le> 3" using snoc.prems by auto
  show ?case using old digit
    by (simp add: branch_code_append_choice power_Suc; arith)
qed

lemma branch_foldl:
  "foldl (\<lambda>n x. 3*n + (x-1)) a ys =
    3 ^ length ys * a + branch_code ys"
proof (induct ys rule: rev_induct)
  case Nil
  then show ?case by (simp add: branch_code_def)
next
  case (snoc x ys)
  then show ?case
    by (simp add: branch_code_append_choice power_Suc algebra_simps)
qed

lemma branch_code_append:
  "branch_code (xs @ ys) = 3 ^ length ys * branch_code xs + branch_code ys"
proof -
  have "branch_code (xs @ ys) =
      foldl (\<lambda>n x. 3*n + (x-1)) (branch_code xs) ys"
    by (simp add: branch_code_def foldl_append)
  also have "... = 3 ^ length ys * branch_code xs + branch_code ys"
    by (rule branch_foldl)
  finally show ?thesis .
qed

lemma branch_code_suffix_mod:
  assumes valid: "\<forall>x\<in>set xs. 1 \<le> x \<and> x \<le> 3"
  shows "branch_code (branch_suffix xs) = branch_code xs mod 729"
proof -
  have suffix: "branch_suffix xs = drop (length xs - 6) xs"
    by (simp add: branch_suffix_def rev_take)
  show ?thesis
  proof (cases "length xs \<le> 6")
    case True
    have short: "branch_suffix xs = xs" using suffix True by simp
    have bound: "branch_code xs < 3 ^ length xs"
      by (rule branch_code_bounded[OF valid])
    have "length xs = 0 \<or> length xs = 1 \<or> length xs = 2 \<or>
      length xs = 3 \<or> length xs = 4 \<or> length xs = 5 \<or> length xs = 6"
      using True by arith
    then have "branch_code xs < 729" using bound by auto
    then show ?thesis using short by simp
  next
    case False
    let ?k = "length xs - 6"
    have full: "take ?k xs @ drop ?k xs = xs" by simp
    have six: "length (drop ?k xs) = 6" using False by simp
    have six_diff: "length xs - (length xs - 6) = 6"
      using False by arith
    have tail_valid: "\<forall>x\<in>set (drop ?k xs). 1 \<le> x \<and> x \<le> 3"
      using branch_suffix_valid[OF valid] suffix by simp
    have tail_bound: "branch_code (drop ?k xs) < 729"
      using branch_code_bounded[OF tail_valid]
      by (simp add: six six_diff)
    have code: "branch_code xs =
      729 * branch_code (take ?k xs) + branch_code (drop ?k xs)"
      using branch_code_append[of "take ?k xs" "drop ?k xs"] full six by simp
    show ?thesis using code tail_bound suffix by simp
  qed
qed

theorem encoded_branch_then_python:
  assumes "\<forall>x\<in>set (xs @ ys). 1 \<le> x \<and> x \<le> 3"
  shows "encoded_branch_suffix (xs @ ys) =
    (min 6 (length xs + length ys),
      (branch_code xs * 3 ^ length ys + branch_code ys) mod 729)"
  using branch_code_suffix_mod[OF assms] branch_code_append[of xs ys]
  by (simp add: encoded_branch_suffix_def branch_suffix_length
    mult.commute)

lemma encoded_branch_suffix_python_bounds:
  assumes "\<forall>x\<in>set xs. 1 \<le> x \<and> x \<le> 3"
  shows "fst (encoded_branch_suffix xs) \<le> 6"
    "snd (encoded_branch_suffix xs) < 3 ^ fst (encoded_branch_suffix xs)"
  using branch_code_bounded[OF branch_suffix_valid[OF assms]]
  by (simp_all add: encoded_branch_suffix_def branch_suffix_length)

text \<open>A possibility partition may forget the phase, but one concrete
event has one exponent q in all its prime lanes. Mahler and accelerated
Collatz use different powers. Their events generally select different q and
different lane inputs; a joint observer must keep those two source bindings.\<close>

definition mahler_lane :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "mahler_lane p inv2 q u = (((3*inv2) mod p)^q * u + p - 1) mod p"

definition collatz_lane :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "collatz_lane p inv2 q u = ((3 * inv2^q) * u + p - 1) mod p"

definition joint_prime_lanes ::
  "(nat \<times> nat) list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    (nat \<times> nat \<times> nat) list" where
  "joint_prime_lanes bank mq mu cq cu =
    map (\<lambda>(p, inv2). (p, mahler_lane p inv2 mq mu,
      collatz_lane p inv2 cq cu)) bank"

definition source_event_exponent :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "source_event_exponent D q \<longleftrightarrow>
    (\<exists>k u. q = Suc k \<and> D = 2^k*u \<and> odd u)"

definition collatz_event_exponent :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "collatz_event_exponent H q \<longleftrightarrow>
    odd H \<and> (\<exists>u. 3*H+1 = 2^q*u \<and> odd u)"


text \<open>
  The odd-then-zero observation is not the source-safety selector. At source
  one their canonical exponents are respectively two and one. These finite
  witnesses use the existing source predicates and reject both crossed
  bindings; no convention bridge is inferred from a shared carry classifier.
\<close>

lemma source_one_source_event:
  "source_event_exponent 1 1"
  unfolding source_event_exponent_def
  by (intro exI[of _ 0] exI[of _ 1]) simp

lemma source_one_odd_zero_event:
  "collatz_event_exponent 1 2"
  unfolding collatz_event_exponent_def
  by (intro conjI; simp; intro exI[of _ 1]; simp)

lemma source_one_rejects_source_event_two:
  "\<not> source_event_exponent 1 2"
  unfolding source_event_exponent_def
  by (auto; arith)

lemma source_one_rejects_odd_zero_event_one:
  "\<not> collatz_event_exponent 1 1"
proof
  assume "collatz_event_exponent 1 1"
  then obtain u :: nat where factor: "4=2*u" and parity: "odd u"
    by (auto simp: collatz_event_exponent_def)
  have "u=2" using factor by arith
  then show False using parity by simp
qed

lemma source_event_exponent_from_odd_factor:
  assumes "D = 2^k*u" "odd u"
  shows "source_event_exponent D (Suc k)"
  using assms by (auto simp: source_event_exponent_def)

lemma joint_lanes_use_source_event:
  assumes "source_event_exponent D q"
  shows "\<exists>k u. D = 2^k*u \<and> odd u \<and> q = Suc k \<and>
    joint_prime_lanes bank q mahler_input collatz_q collatz_input =
      map (\<lambda>(p, inv2).
        (p, mahler_lane p inv2 (Suc k) mahler_input,
          collatz_lane p inv2 collatz_q collatz_input)) bank"
  using assms by (auto simp: source_event_exponent_def joint_prime_lanes_def)

lemma joint_lanes_bind_both_sources:
  assumes "source_event_exponent D mq" "collatz_event_exponent H cq"
  shows "\<exists>k u v. D = 2^k*u \<and> odd u \<and> mq = Suc k \<and>
    odd H \<and> 3*H+1 = 2^cq*v \<and> odd v \<and>
    joint_prime_lanes bank mq mu cq cu =
      map (\<lambda>(p, inv2). (p, mahler_lane p inv2 (Suc k) mu,
        collatz_lane p inv2 cq cu)) bank"
  using assms by (auto simp: source_event_exponent_def
    collatz_event_exponent_def joint_prime_lanes_def)

lemma lane_one_event_agreement:
  assumes "0 < p"
  shows "mahler_lane p inv2 1 u = collatz_lane p inv2 1 u"
proof -
  let ?a = "3 * inv2"
  have left: "(?a mod p * u + p - 1) = ?a mod p * u + (p - 1)"
    using assms by arith
  have right: "(?a * u + p - 1) = ?a * u + (p - 1)"
    using assms by arith
  have residue: "(?a mod p * u + (p - 1)) mod p =
      (?a * u + (p - 1)) mod p"
  proof -
    have "(?a mod p * u + (p - 1)) mod p =
        ((?a mod p * u) mod p + (p - 1)) mod p"
      by (rule mod_add_left_eq[symmetric])
    also have "... = ((?a * u) mod p + (p - 1)) mod p"
      by (simp only: mod_mult_left_eq)
    also have "... = (?a * u + (p - 1)) mod p"
      by (rule mod_add_left_eq)
    finally show ?thesis .
  qed
  have left_mod: "(?a mod p * u + p - 1) mod p =
      (?a mod p * u + (p - 1)) mod p"
    using arg_cong[OF left, of "\<lambda>x. x mod p"] .
  have right_mod: "(?a * u + p - 1) mod p =
      (?a * u + (p - 1)) mod p"
    using arg_cong[OF right, of "\<lambda>x. x mod p"] .
  have target: "(?a mod p * u + p - 1) mod p = (?a * u + p - 1) mod p"
    using left_mod residue right_mod by metis
  have mahler: "mahler_lane p inv2 1 u = (?a mod p * u + p - 1) mod p"
    by (simp add: mahler_lane_def)
  have collatz: "collatz_lane p inv2 1 u = (?a * u + p - 1) mod p"
    by (simp add: collatz_lane_def)
  show ?thesis using mahler collatz target by metis
qed

lemma lane_laws_distinct:
  "mahler_lane 5 3 2 1 = 0 \<and> collatz_lane 5 3 2 1 = 1"
  by (simp add: mahler_lane_def collatz_lane_def)

text \<open>These finite lane and address observations remain projections of
the source-bound cylinder. Its admitted guard and centered high-fiber chart
are kept by the existing transport theorems, not inferred from a bucket key.
The following theorem packages that exact precondition for a chronological
two-block observation. It does not claim a repeating source grammar.\<close>

theorem joint_observer_source_scope:
  assumes admitted: "cylinder_guard D (m+n) t"
  shows "cylinder_guard D m t"
    "cylinder_guard (mahler_orbit D m) n (fractional_endpoint D m t)"
    "fractional_endpoint D (m+n) t =
      fractional_endpoint (mahler_orbit D m) n (fractional_endpoint D m t)"
  using admitted source_guard_composition fractional_endpoint_composition
  by blast+

text \<open>The centered arithmetic source still has an exact successor after
the source-7 fractional guard has become empty.  The latter removes only the
fractional witness; it is not a claim that the physical Antihydra run
terminates or fails to terminate.\<close>

theorem source7_arithmetic_successor_without_safe_fraction:
  "mahler_orbit 7 2 = 17"
  "\<not> cylinder_guard 7 2 t"
proof -
  show "mahler_orbit 7 2 = 17"
    by (simp add: mahler_D_step_def)
  show "\<not> cylinder_guard 7 2 t"
    using root_shell_source7_empty_after_two[of 0 "2*t"]
    by (simp add: root_shell_guard_def)
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms branch_suffix_then branch_then_assoc encoded_branch_then_python
      lane_one_event_agreement
      lane_laws_distinct source_one_source_event source_one_odd_zero_event
      source_one_rejects_source_event_two source_one_rejects_odd_zero_event_one
      joint_lanes_use_source_event
      joint_lanes_bind_both_sources
      joint_observer_source_scope
      source7_arithmetic_successor_without_safe_fraction})
    then () else error "Joint quotient algebra depends on an oracle";
\<close>

end
