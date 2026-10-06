theory Mirror_Pair_Step
  imports Reverse_Threshold_Cocycle
begin

text \<open>The no-growth local mirror consumer after both carries have been
derived from exact domain geometry.  Both normalized operands have the same
decimal residue r.  These laws do not apply to growth interiors, where adjacent
residues are paired, and do not assert temporal closure of a recursive carrier.\<close>

definition mirror_pair_step :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "mirror_pair_step r c d = (r+c) mod 10 + (r+d) mod 10"

definition mirror_pair_formula :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "mirror_pair_formula r k = (if r = 9 then 18 - 9*k else 2*r+k)"

definition mirror_pair_channels ::
    "nat \<Rightarrow> nat \<Rightarrow> carry_domain \<times> nat \<times> nat" where
  "mirror_pair_channels r k =
    (domain (mirror_pair_formula r k), mirror_pair_formula r k mod 5,
      mirror_pair_formula r k mod 2)"

text \<open>One spatial reflection lemma serves the growth and publisher
branches. It depends only on palindrome admission, not on a carry port.\<close>

lemma palindrome_nth_reflect:
  assumes palindrome: "rev ss = ss" and bound: "i < length ss"
  shows "ss ! (length ss-Suc i) = ss!i"
proof -
  have "rev ss ! i = ss ! (length ss-Suc i)"
    using bound by (simp add: rev_nth)
  then show ?thesis using palindrome by simp
qed

lemma nat_less_three_cases:
  assumes "(k::nat) < 3"
  shows "k = 0 \<or> k = 1 \<or> k = 2"
  using assms by arith

theorem mirror_pair_step_closed_form:
  assumes residue: "r < 10"
      and left_port: "c < 2"
      and right_port: "d < 2"
  shows "mirror_pair_step r c d = mirror_pair_formula r (c+d)"
proof -
  have r_cases: "r = 0 \<or> r = 1 \<or> r = 2 \<or> r = 3 \<or> r = 4 \<or>
      r = 5 \<or> r = 6 \<or> r = 7 \<or> r = 8 \<or> r = 9"
    using residue by (rule nat_less_ten_cases)
  have c_cases: "c = 0 \<or> c = 1"
    using left_port by (rule nat_less_two_cases)
  have d_cases: "d = 0 \<or> d = 1"
    using right_port by (rule nat_less_two_cases)
  show ?thesis using r_cases c_cases d_cases
    by (elim disjE; simp add: mirror_pair_step_def mirror_pair_formula_def)
qed

theorem mirror_pair_formula_below_nine:
  assumes "r < 9"
  shows "mirror_pair_formula r k = 2*r+k"
  using assms by (simp add: mirror_pair_formula_def)

theorem mirror_pair_formula_at_nine:
  "mirror_pair_formula 9 k = 18 - 9*k"
  by (simp add: mirror_pair_formula_def)

theorem mirror_pair_f5_channel:
  assumes residue: "r < 10" and ports: "k < 3"
  shows "mirror_pair_formula r k mod 5 = (2*(r mod 5)+k) mod 5"
proof -
  have r_cases: "r = 0 \<or> r = 1 \<or> r = 2 \<or> r = 3 \<or> r = 4 \<or>
      r = 5 \<or> r = 6 \<or> r = 7 \<or> r = 8 \<or> r = 9"
    using residue by (rule nat_less_ten_cases)
  have k_cases: "k = 0 \<or> k = 1 \<or> k = 2"
    using ports by (rule nat_less_three_cases)
  show ?thesis using r_cases k_cases
    by (elim disjE; simp add: mirror_pair_formula_def)
qed

theorem mirror_pair_f2_channel:
  assumes residue: "r < 10" and ports: "k < 3"
  shows "mirror_pair_formula r k mod 2 = k mod 2"
proof -
  have r_cases: "r = 0 \<or> r = 1 \<or> r = 2 \<or> r = 3 \<or> r = 4 \<or>
      r = 5 \<or> r = 6 \<or> r = 7 \<or> r = 8 \<or> r = 9"
    using residue by (rule nat_less_ten_cases)
  have k_cases: "k = 0 \<or> k = 1 \<or> k = 2"
    using ports by (rule nat_less_three_cases)
  show ?thesis using r_cases k_cases
    by (elim disjE; simp add: mirror_pair_formula_def)
qed

corollary mirror_pair_ports_emit_channels:
  assumes "r < 10" "c < 2" "d < 2"
  shows "mirror_pair_step r c d mod 5 = (2*(r mod 5)+(c+d)) mod 5"
    and "mirror_pair_step r c d mod 2 = (c+d) mod 2"
proof -
  have port_sum: "c+d < 3" using assms(2,3) by arith
  have formula: "mirror_pair_step r c d = mirror_pair_formula r (c+d)"
    using assms by (rule mirror_pair_step_closed_form)
  show "mirror_pair_step r c d mod 5 = (2*(r mod 5)+(c+d)) mod 5"
    using mirror_pair_f5_channel[OF assms(1) port_sum] formula by simp
  show "mirror_pair_step r c d mod 2 = (c+d) mod 2"
    using mirror_pair_f2_channel[OF assms(1) port_sum] formula by simp
qed

theorem source_plus_ten_alias_after_ports:
  assumes "S \<le> 8"
  shows "mirror_pair_step (S mod 10) c d =
    mirror_pair_step ((S+10) mod 10) c d"
  by (simp add: mirror_pair_step_def)

corollary source_plus_ten_channel_alias_after_ports:
  assumes "S \<le> 8"
  shows "mirror_pair_channels (S mod 10) k =
    mirror_pair_channels ((S+10) mod 10) k"
  by (simp add: mirror_pair_channels_def)

text \<open>The aliases above are consumer aliases after the two port carries
are fixed.  They do not identify the current domains of S and S+10; those
domains remain responsible for carry propagation elsewhere.\<close>

section \<open>Branch-independent residue normalization and growth\<close>

definition normalized_pair_digit :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "normalized_pair_digit S c =
    S+c - 10*(if carry_apply (domain S) (c = 1) then 1 else 0)"

lemma nat_less_nineteen_cases:
  assumes "(S::nat) < 19"
  shows "S = 0 \<or> S = 1 \<or> S = 2 \<or> S = 3 \<or> S = 4 \<or>
    S = 5 \<or> S = 6 \<or> S = 7 \<or> S = 8 \<or> S = 9 \<or>
    S = 10 \<or> S = 11 \<or> S = 12 \<or> S = 13 \<or> S = 14 \<or>
    S = 15 \<or> S = 16 \<or> S = 17 \<or> S = 18"
  using assms by arith

theorem normalized_pair_digit_exact:
  assumes pair_value: "S < 19" and carry_bit: "c < 2"
  shows "normalized_pair_digit S c = (S mod 10+c) mod 10"
proof -
  have S_cases: "S = 0 \<or> S = 1 \<or> S = 2 \<or> S = 3 \<or> S = 4 \<or>
      S = 5 \<or> S = 6 \<or> S = 7 \<or> S = 8 \<or> S = 9 \<or>
      S = 10 \<or> S = 11 \<or> S = 12 \<or> S = 13 \<or> S = 14 \<or>
      S = 15 \<or> S = 16 \<or> S = 17 \<or> S = 18"
    using pair_value by (rule nat_less_nineteen_cases)
  have c_cases: "c = 0 \<or> c = 1"
    using carry_bit by (rule nat_less_two_cases)
  show ?thesis using S_cases c_cases
    by (elim disjE; simp add: normalized_pair_digit_def domain_def)
qed

corollary normalized_pair_digit_forgets_high_ten:
  assumes "S < 19" "c < 2"
  shows "normalized_pair_digit S c = (S+c) mod 10"
  using normalized_pair_digit_exact[OF assms]
  by (simp add: mod_add_left_eq)

definition growth_pair_step ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "growth_pair_step r s c d = (r+c) mod 10 + (s+d) mod 10"

lemma mod_ten_mod_five [simp]:
  "(x::nat) mod 10 mod 5 = x mod 5"
  by (rule mod_mod_cancel) simp

lemma mod_ten_mod_two [simp]:
  "(x::nat) mod 10 mod 2 = x mod 2"
  by (rule mod_mod_cancel) simp

theorem growth_pair_f5_channel:
  "growth_pair_step r s c d mod 5 = (r+s+c+d) mod 5"
proof -
  have left: "(r+c) mod 10 mod 5 = (r+c) mod 5" by simp
  have right: "(s+d) mod 10 mod 5 = (s+d) mod 5" by simp
  have "growth_pair_step r s c d mod 5 =
      ((r+c) mod 5 + (s+d) mod 5) mod 5"
    unfolding growth_pair_step_def using left right by (metis mod_add_eq)
  also have "... = ((r+c)+(s+d)) mod 5" by (metis mod_add_eq)
  also have "... = (r+s+c+d) mod 5" by (simp add: algebra_simps)
  finally show ?thesis .
qed

theorem growth_pair_f2_channel:
  "growth_pair_step r s c d mod 2 = (r+s+c+d) mod 2"
proof -
  have left: "(r+c) mod 10 mod 2 = (r+c) mod 2" by simp
  have right: "(s+d) mod 10 mod 2 = (s+d) mod 2" by simp
  have "growth_pair_step r s c d mod 2 =
      ((r+c) mod 2 + (s+d) mod 2) mod 2"
    unfolding growth_pair_step_def using left right by (metis mod_add_eq)
  also have "... = ((r+c)+(s+d)) mod 2" by (metis mod_add_eq)
  also have "... = (r+s+c+d) mod 2" by (simp add: algebra_simps)
  finally show ?thesis .
qed

definition growth_edge_step :: "nat \<Rightarrow> nat" where
  "growth_edge_step r = r+1"

theorem growth_edge_channels:
  "growth_edge_step r mod 5 = (r mod 5+1) mod 5"
  "growth_edge_step r mod 2 = (r mod 2+1) mod 2"
proof -
  show "growth_edge_step r mod 5 = (r mod 5+1) mod 5"
    unfolding growth_edge_step_def by (rule mod_add_left_eq[symmetric])
  show "growth_edge_step r mod 2 = (r mod 2+1) mod 2"
    unfolding growth_edge_step_def by (rule mod_add_left_eq[symmetric])
qed

text \<open>Growth keeps only normalized decimal residues, but its adjacent
stencil retains the linear old-value terms r+s in both residue channels.  The
new edge is the fixed affine injection r+1.\<close>

theorem growth_pair_parity_does_not_globally_die:
  "step [10,1,1,10] = [1,2,2,2,1]"
  "map (\<lambda>x. x mod 2) (step [10,1,1,10]) = [1,0,0,0,1]"
  by (simp_all add: step_def digits_def carry_out_def domain_def)

theorem growth_GT4_retains_old_parity_witness:
  "map domain [10,10,10,10] = [Above,Above,Above,Above]"
  "map domain [10,15,15,10] = [Above,Above,Above,Above]"
  "map (\<lambda>(x::nat). x mod 5) [10,10,10,10] = [0,0,0,0]"
  "map (\<lambda>(x::nat). x mod 5) [10,15,15,10] = [0,0,0,0]"
  "step [10,10,10,10] = [1,2,2,2,1]"
  "step [10,15,15,10] = [1,7,12,7,1]"
  by (simp_all add: step_def digits_def carry_out_def domain_def)

text \<open>This growth witness pairs adjacent normalized residues and retains
nonzero old-value parity at the new edges.  Therefore the F2 emission theorem
is deliberately restricted to the matched-residue no-growth consumer.\<close>

ML \<open>
  val checked = @{thms mirror_pair_step_closed_form
    palindrome_nth_reflect
    mirror_pair_formula_below_nine mirror_pair_formula_at_nine
    mirror_pair_f5_channel mirror_pair_f2_channel
    mirror_pair_ports_emit_channels source_plus_ten_alias_after_ports
    source_plus_ten_channel_alias_after_ports
    normalized_pair_digit_exact normalized_pair_digit_forgets_high_ten
    growth_pair_f5_channel growth_pair_f2_channel growth_edge_channels
    growth_pair_parity_does_not_globally_die
    growth_GT4_retains_old_parity_witness};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Mirror pair step proof depends on an oracle";
\<close>

end
