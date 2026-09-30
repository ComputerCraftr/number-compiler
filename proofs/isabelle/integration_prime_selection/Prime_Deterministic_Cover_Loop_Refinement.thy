theory Prime_Deterministic_Cover_Loop_Refinement
  imports Prime_Deterministic_Prefix_Extension_Refinement
begin

text \<open>This theory models the repeated factor-discovery loop in
\<open>PrimePrefixRank.cover\<close>.  The body invokes the checked inner
\<open>prefix_search_loop\<close> and appends the lower bound returned by that
loop; it does not replace the search result with an assumed next prime.\<close>

definition prefix_cover_guard :: "nat \<Rightarrow> nat list \<Rightarrow> bool" where
  "prefix_cover_guard cover_limit ps \<longleftrightarrow>
    numerical_Phi ps (length ps) cover_limit \<noteq> 1"

definition prefix_cover_initial_search ::
    "nat \<Rightarrow> nat list \<Rightarrow> prefix_search_state" where
  "prefix_cover_initial_search cover_limit ps =
    \<lparr>prefix_search_lo = Suc (last ps), prefix_search_hi = cover_limit\<rparr>"

definition prefix_cover_step :: "nat \<Rightarrow> nat list \<Rightarrow> nat list" where
  "prefix_cover_step cover_limit ps =
    (case prefix_search_loop ps (prefix_cover_initial_search cover_limit ps) of
       None \<Rightarrow> ps
     | Some final \<Rightarrow> ps @ [prefix_search_lo final])"

definition prefix_cover_loop ::
    "nat \<Rightarrow> nat list \<Rightarrow> nat list option" where
  "prefix_cover_loop cover_limit initial =
    while_option (prefix_cover_guard cover_limit) (prefix_cover_step cover_limit) initial"

definition prefix_cover_invariant :: "nat \<Rightarrow> nat list \<Rightarrow> bool" where
  "prefix_cover_invariant cover_limit ps \<longleftrightarrow>
    consecutive_prime_descriptor ps \<and> last ps \<le> cover_limit"

lemma consecutive_descriptor_phi_positive:
  fixes x :: nat
  assumes descriptor: "consecutive_prime_descriptor ps"
    and covered: "last ps \<le> x"
  shows "0 < numerical_Phi ps (length ps) x"
proof -
  have distinct: "distinct ps"
    by (rule consecutive_descriptor_distinct[OF descriptor])
  have prefix_set: "set ps = {p. prime p \<and> p \<le> last ps}"
    by (rule consecutive_descriptor_set[OF descriptor])
  have primes: "\<forall>p\<in>set ps. prime p"
    by (auto simp only: prefix_set mem_Collect_eq)
  have raw:
      "numerical_Phi ps (length ps) x =
        card (wheel_sift (rev (take (length ps) ps)) {1..x})"
    by (rule numerical_Phi_is_sift_card)
      (use distinct primes in auto)
  have one_member: "1 \<in> wheel_sift (rev ps) {1..x}"
    by (rule consecutive_descriptor_one_in_sift[OF descriptor])
      (use covered in arith)
  have finite: "finite (wheel_sift (rev ps) {1..x})"
    by (rule finite_wheel_sift) simp
  have nonempty: "wheel_sift (rev ps) {1..x} \<noteq> {}"
    using one_member by auto
  have positive: "0 < card (wheel_sift (rev ps) {1..x})"
    using finite nonempty by (simp add: card_gt_0_iff)
  show ?thesis using raw positive by simp
qed

theorem prefix_cover_step_executes_inner_search:
  fixes root :: nat
  assumes invariant: "prefix_cover_invariant root ps"
    and guard: "prefix_cover_guard root ps"
  defines "q \<equiv> next_prime_after (last ps)"
  shows "\<exists>final.
      prefix_search_loop ps (prefix_cover_initial_search root ps) = Some final \<and>
      prefix_search_lo final = q \<and>
      prefix_search_hi final = q \<and>
      prefix_cover_step root ps = ps @ [q]"
proof -
  from invariant have descriptor: "consecutive_prime_descriptor ps"
    and covered: "last ps \<le> root"
    by (auto simp: prefix_cover_invariant_def)
  from guard have root_count:
      "numerical_Phi ps (length ps) root \<noteq> 1"
    by (simp add: prefix_cover_guard_def)
  have positive: "0 < numerical_Phi ps (length ps) root"
    by (rule consecutive_descriptor_phi_positive[OF descriptor covered])
  have more: "1 < numerical_Phi ps (length ps) root"
    using positive root_count by arith
  have q_root: "q \<le> root"
    using consecutive_descriptor_phi_threshold[OF descriptor covered] more
    unfolding q_def by simp
  have last_q: "last ps < q"
    unfolding q_def by (rule next_prime_after_gt[of "last ps"])
  have root_above: "last ps < root" using last_q q_root by arith
  from deterministic_prefix_extension_step[OF descriptor root_count root_above,
      folded q_def prefix_cover_initial_search_def]
  obtain final where
      loop: "prefix_search_loop ps (prefix_cover_initial_search root ps) = Some final"
    and lo: "prefix_search_lo final = q"
    and hi: "prefix_search_hi final = q"
    by blast
  have step: "prefix_cover_step root ps = ps @ [q]"
    unfolding prefix_cover_step_def using loop lo by simp
  show ?thesis using loop lo hi step by blast
qed

theorem prefix_cover_step_preserves_invariant:
  fixes root :: nat
  assumes invariant: "prefix_cover_invariant root ps"
    and guard: "prefix_cover_guard root ps"
  shows "prefix_cover_invariant root (prefix_cover_step root ps)"
    "root - last (prefix_cover_step root ps) < root - last ps"
proof -
  from invariant have descriptor: "consecutive_prime_descriptor ps"
    and covered: "last ps \<le> root"
    by (auto simp: prefix_cover_invariant_def)
  let ?q = "next_prime_after (last ps)"
  from prefix_cover_step_executes_inner_search[OF invariant guard]
  obtain final where step: "prefix_cover_step root ps = ps @ [?q]" by blast
  have appended: "ps @ [?q] = primes_upto ?q"
    by (rule append_next_prime_preserves_consecutive_descriptor[OF descriptor])
  have new_descriptor: "consecutive_prime_descriptor (ps @ [?q])"
    unfolding consecutive_prime_descriptor_def
  proof
    show "ps @ [?q] \<noteq> []" by simp
    show "ps @ [?q] = primes_upto (last (ps @ [?q]))"
    proof -
      have "ps @ [?q] = primes_upto ?q" by (rule appended)
      also have "... = primes_upto (last (ps @ [?q]))" by simp
      finally show ?thesis .
    qed
  qed
  have positive: "0 < numerical_Phi ps (length ps) root"
    by (rule consecutive_descriptor_phi_positive[OF descriptor covered])
  from guard have count_not_one:
      "numerical_Phi ps (length ps) root \<noteq> 1"
    by (simp add: prefix_cover_guard_def)
  have count_more: "1 < numerical_Phi ps (length ps) root"
    using positive count_not_one by arith
  have q_root: "?q \<le> root"
    using consecutive_descriptor_phi_threshold[OF descriptor covered] count_more
    by simp
  have last_q: "last ps < ?q" by (rule next_prime_after_gt)
  show "prefix_cover_invariant root (prefix_cover_step root ps)"
    using step new_descriptor q_root
    by (simp add: prefix_cover_invariant_def)
  show "root - last (prefix_cover_step root ps) < root - last ps"
    using step q_root last_q covered by simp
qed

theorem prefix_cover_loop_terminates:
  fixes root :: nat
  assumes invariant: "prefix_cover_invariant root initial"
  shows "\<exists>final. prefix_cover_loop root initial = Some final"
  unfolding prefix_cover_loop_def
  by (rule measure_while_option_Some[
        where P="prefix_cover_invariant root"
          and f="\<lambda>ps. root - last ps"])
    (use prefix_cover_step_preserves_invariant invariant in blast)+

theorem prefix_cover_loop_constructs_complete_prefix:
  fixes root :: nat
  assumes invariant: "prefix_cover_invariant root initial"
    and loop: "prefix_cover_loop root initial = Some final"
  shows "final = primes_upto root"
proof -
  have raw_loop:
      "while_option (prefix_cover_guard root) (prefix_cover_step root) initial =
        Some final"
    using loop unfolding prefix_cover_loop_def .
  have preserved: "prefix_cover_invariant root final"
    by (rule while_option_rule[
          where P="prefix_cover_invariant root"
            and b="prefix_cover_guard root"
            and c="prefix_cover_step root"
            and s=initial and t=final,
          OF _ raw_loop invariant])
      (use prefix_cover_step_preserves_invariant in blast)
  have stopped: "\<not> prefix_cover_guard root final"
    by (rule while_option_stop[OF raw_loop])
  from preserved have descriptor: "consecutive_prime_descriptor final"
    and covered: "last final \<le> root"
    by (auto simp: prefix_cover_invariant_def)
  from stopped have count:
      "numerical_Phi final (length final) root = 1"
    by (simp add: prefix_cover_guard_def)
  show ?thesis
    by (rule deterministic_prefix_discovery_stop[OF descriptor covered count])
qed

theorem deterministic_cover_from_two:
  fixes root :: nat
  assumes root: "2 \<le> root"
  shows "\<exists>final.
      prefix_cover_loop root [2] = Some final \<and>
      final = primes_upto root"
proof -
  have candidates: "{m::nat. m \<le> 2 \<and> prime m} = {2}"
  proof (rule Set.set_eqI)
    fix m
    show "m \<in> {m::nat. m \<le> 2 \<and> prime m} \<longleftrightarrow> m \<in> {2}"
    proof
      assume member: "m \<in> {m::nat. m \<le> 2 \<and> prime m}"
      then have prime_m: "prime m" and upper: "m \<le> 2" by auto
      have "1 < m" by (rule prime_gt_1_nat[OF prime_m])
      with upper have "m = 2" by arith
      then show "m \<in> {2}" by simp
    next
      assume "m \<in> {2}"
      then show "m \<in> {m::nat. m \<le> 2 \<and> prime m}" by simp
    qed
  qed
  have seed: "primes_upto 2 = [2]"
    unfolding primes_upto_def using candidates by simp
  have descriptor: "consecutive_prime_descriptor [2]"
    using seed by (simp add: consecutive_prime_descriptor_def)
  have invariant: "prefix_cover_invariant root [2]"
    using descriptor root by (simp add: prefix_cover_invariant_def)
  from prefix_cover_loop_terminates[OF invariant]
  obtain final where loop: "prefix_cover_loop root [2] = Some final" by blast
  have result: "final = primes_upto root"
    by (rule prefix_cover_loop_constructs_complete_prefix[OF invariant loop])
  show ?thesis using loop result by blast
qed

text \<open>The exported theorem maps the repeated Python cover guard and body:
each body execution invokes the exact checked midpoint loop, appends that
loop's returned lower endpoint, and decreases \<open>root - last_factor\<close>.
Starting from the implementation's seed \<open>[2]\<close>, the loop terminates
with exactly \<open>primes_upto root\<close>.

This is an arithmetic trace theorem.  Its numerical-Phi calls are the pure
count specification already refined by the deterministic cache-pruned theory.
It does not model Python object authority, authenticated shared-cache hits,
work charging, exception cleanup, or publication of the committed covered
root.\<close>

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms consecutive_descriptor_phi_positive
      prefix_cover_step_executes_inner_search
      prefix_cover_step_preserves_invariant
      prefix_cover_loop_terminates
      prefix_cover_loop_constructs_complete_prefix
      deterministic_cover_from_two}) then ()
    else error "Deterministic prime cover loop depends on an oracle";
\<close>

end
