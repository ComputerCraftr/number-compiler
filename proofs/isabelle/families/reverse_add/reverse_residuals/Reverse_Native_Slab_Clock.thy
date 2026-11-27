theory Reverse_Native_Slab_Clock
  imports Reverse_Punctured_T2_Coefficients
begin

text \<open>These are the exact local decimal equations at the moving boundary.
The two incoming carry bits remain separate, including at an EQ-9 cell.\<close>

definition reverse_native_slab_digit :: "nat \<Rightarrow> bool \<Rightarrow> nat" where
  "reverse_native_slab_digit coefficient inlet =
    (coefficient + carry_bit inlet) mod 10"

definition reverse_native_slab_birth ::
    "nat \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> nat" where
  "reverse_native_slab_birth left right inward outward =
    reverse_native_slab_digit right inward + reverse_native_slab_digit left outward"

definition reverse_native_slab_quiet :: "nat \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> nat" where
  "reverse_native_slab_quiet coefficient forward backward =
    reverse_native_slab_digit coefficient forward + reverse_native_slab_digit coefficient backward"

text \<open>The three admitted source symbols are reset ports.  In particular,
the same complete source prefix supplies the same boundary carry regardless
of the remote incoming carry.  This statement concerns the source prefix,
not an independently asserted carry at the edge of a shortened window.\<close>

definition reverse_native_slab_source_symbol :: "nat \<Rightarrow> bool" where
  "reverse_native_slab_source_symbol s \<longleftrightarrow> s = 8 \<or> s = 17 \<or> s = 18"

lemma reverse_native_slab_source_reset:
  assumes "reverse_native_slab_source_symbol s"
  shows "carry_apply (domain s) a = (9 < s)"
  using assms unfolding reverse_native_slab_source_symbol_def domain_def
  by (cases a; auto)

lemma reverse_native_slab_source_prefix_transport:
  assumes "reverse_native_slab_source_symbol s"
  shows "radix19_final_carry (s # suffix) a =
    radix19_final_carry (s # suffix) b"
  using reverse_native_slab_source_reset[OF assms, of a]
    reverse_native_slab_source_reset[OF assms, of b] by simp

lemma reverse_native_slab_physical_prefix_transport:
  assumes "reverse_native_slab_source_symbol s"
  shows "carry_out False (left @ s # suffix) =
    carry_out False (other @ s # suffix)"
proof -
  have reset: "\<And>incoming. carry_apply (domain s) incoming = (9 < s)"
    by (rule reverse_native_slab_source_reset[OF assms])
  show ?thesis by (simp add: carry_out_append carry_out_def reset)
qed

lemma reverse_native_slab_source_local_pair:
  assumes "reverse_native_slab_source_symbol s"
  shows "reverse_native_slab_quiet s a b =
      (s + carry_bit a) mod 10 + (s + carry_bit b) mod 10"
    and "carry_apply (domain s) a = carry_apply (domain s) b"
  using assms reverse_native_slab_source_reset[OF assms, of a]
    reverse_native_slab_source_reset[OF assms, of b]
  by (simp_all add: reverse_native_slab_quiet_def reverse_native_slab_digit_def)

lemma reverse_native_slab_born_quiet_forces_next_birth:
  assumes coefficient: "coefficient < 19"
    and quiet: "\<not> carry_apply
      (domain (reverse_native_slab_birth 18 coefficient True
        (carry_apply (domain coefficient) inlet))) later_inlet"
  defines "second \<equiv> reverse_native_slab_quiet
      (reverse_native_slab_birth 18 coefficient True
        (carry_apply (domain coefficient) inlet)) False later_inlet"
  shows "16 \<le> second \<and> second \<le> 18 \<and>
    9 < reverse_native_slab_birth 18 second True
      (carry_apply (domain second) final_inlet)"
proof -
  have cases: "coefficient = 0 \<or> coefficient = 1 \<or> coefficient = 2 \<or>
      coefficient = 3 \<or> coefficient = 4 \<or> coefficient = 5 \<or>
      coefficient = 6 \<or> coefficient = 7 \<or> coefficient = 8 \<or>
      coefficient = 9 \<or> coefficient = 10 \<or> coefficient = 11 \<or>
      coefficient = 12 \<or> coefficient = 13 \<or> coefficient = 14 \<or>
      coefficient = 15 \<or> coefficient = 16 \<or> coefficient = 17 \<or>
      coefficient = 18"
    using coefficient by (rule nat_less_nineteen_cases)
  show ?thesis using cases quiet
    unfolding second_def reverse_native_slab_birth_def
      reverse_native_slab_quiet_def reverse_native_slab_digit_def
    by (elim disjE; cases inlet; cases later_inlet; cases final_inlet;
        simp add: domain_def carry_bit_def)
qed

ML \<open>
  val checked = @{thms reverse_native_slab_source_reset
    reverse_native_slab_source_prefix_transport reverse_native_slab_physical_prefix_transport
    reverse_native_slab_source_local_pair
    reverse_native_slab_born_quiet_forces_next_birth};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Reverse native slab clock depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked then
    error "Skipped reverse native slab clock proof" else ();
\<close>

end
