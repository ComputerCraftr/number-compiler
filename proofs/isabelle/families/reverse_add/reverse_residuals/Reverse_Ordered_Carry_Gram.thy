theory Reverse_Ordered_Carry_Gram
  imports Reverse_Residuals
begin

text \<open>At a selected position the left and right inlets see disjoint
prefix and suffix words. Splitting the word conditions each child on the
other child's exit. These signs and products are spatial observations.\<close>

definition gram_ports :: "bool \<Rightarrow> bool \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> bool \<times> bool" where
  "gram_ports a b s i = (carry_out a (take i s), carry_out b (rev (drop (Suc i) s)))"

lemma gram_ports_left:
  "i < length l \<Longrightarrow> gram_ports a b (l @ r) i =
    gram_ports a (carry_out b (rev r)) l i"
  by (simp add: gram_ports_def take_append drop_append carry_out_append)

lemma gram_ports_right:
  "gram_ports a b (l @ r) (length l + j) =
    gram_ports (carry_out a l) b r j"
  by (simp add: gram_ports_def take_append drop_append carry_out_append)

primrec gram_sum :: "'a::comm_ring_1 \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> 'a" where
  "gram_sum z 0 f = 0"
| "gram_sum z (Suc n) f = gram_sum z n f + z^n * f n"

lemma gram_sum_split:
  "gram_sum z (n+m) f = gram_sum z n f + z^n * gram_sum z m (\<lambda>j. f(n+j))"
  by (induction m) (simp_all add: power_add algebra_simps)

lemma gram_sum_cong:
  "(\<And>i. i < n \<Longrightarrow> f i = g i) \<Longrightarrow> gram_sum z n f = gram_sum z n g"
  by (induction n) auto

theorem gram_aligned_ordered_join:
  "gram_sum z (length (l@r)) (\<lambda>i. h (gram_ports a b (l@r) i)) =
    gram_sum z (length l) (\<lambda>i. h (gram_ports a (carry_out b (rev r)) l i)) +
    z^length l * gram_sum z (length r) (\<lambda>i. h (gram_ports (carry_out a l) b r i))"
  by (simp only: length_append gram_sum_split)
     (simp cong: gram_sum_cong add: gram_ports_left gram_ports_right)


text \<open>The source issuer maps each Q19 symbol to its exact carry-domain
representative before building its four conditional response rows. This
normalization changes neither ordered inlet stream nor either boundary exit.\<close>

definition gram_domain_representative :: "nat \<Rightarrow> nat" where
  "gram_domain_representative s = (if s < 9 then 0 else if s = 9 then 9 else 10)"

lemma gram_domain_representative_domain [simp]:
  "domain (gram_domain_representative s) = domain s"
  by (auto simp: gram_domain_representative_def domain_def)

lemma gram_normalized_carry [simp]:
  "carry_out c (map gram_domain_representative ss) = carry_out c ss"
  by (rule carry_depends_only_on_domains) (simp add: map_map)

lemma gram_normalized_ports [simp]:
  "gram_ports a b (map gram_domain_representative ss) i = gram_ports a b ss i"
  by (simp add: gram_ports_def take_map drop_map rev_map)

text \<open>For an LSD-first normalized decimal source, the selected pair field
is the physical source for the next reverse/add step. Its normalization applies
to the selected field, with no claim that domain-only keys advance the physical
recurrence. Both lag orders are retained independently.\<close>

theorem physical_q19_ordered_gram_domain_refinement:
  fixes z :: "'a::comm_ring_1" and ds :: "nat list" and n :: nat
  assumes source: "ds \<noteq> []" "\<forall>d \<in> set ds. d < 10"
    "last ds \<noteq> 0 \<or> ds = [0]"
  defines "ss \<equiv> run step n (map (\<lambda>(x,y). x+y) (zip ds (rev ds)))"
  shows
    "carry_out a (map gram_domain_representative ss) = carry_out a ss"
    "carry_out b (rev (map gram_domain_representative ss)) = carry_out b (rev ss)"
    "gram_sum z (length ss) (\<lambda>i. f (gram_ports a b (map gram_domain_representative ss) i)) =
     gram_sum z (length ss) (\<lambda>i. f (gram_ports a b ss i))"
    "gram_sum z (length ss - 1)
       (\<lambda>i. h (gram_ports a b (map gram_domain_representative ss) i)
                   (gram_ports a b (map gram_domain_representative ss) (Suc i))) =
     gram_sum z (length ss - 1)
       (\<lambda>i. h (gram_ports a b ss i) (gram_ports a b ss (Suc i)))"
    "gram_sum z (length ss - 1)
       (\<lambda>i. h (gram_ports a b (map gram_domain_representative ss) (Suc i))
                   (gram_ports a b (map gram_domain_representative ss) i)) =
     gram_sum z (length ss - 1)
       (\<lambda>i. h (gram_ports a b ss (Suc i)) (gram_ports a b ss i))"
  by (simp_all add: rev_map)

text \<open>The two lagged products use different ordered projections of the
same adjacent port pair. Each seam sits at the final position of the left
child, and the right interior starts at the following power of z.\<close>

theorem gram_adjacent_ordered_join:
  fixes a b :: bool
  assumes lengths: "length l = Suc n" "length r = Suc m"
  defines "p \<equiv> gram_ports a b (l@r)"
      and "u \<equiv> gram_ports a (carry_out b (rev r)) l"
      and "v \<equiv> gram_ports (carry_out a l) b r"
  shows "gram_sum z (length(l@r)-1) (\<lambda>i. h (p i) (p (Suc i))) =
    gram_sum z n (\<lambda>i. h (u i) (u (Suc i))) + z^n * h (u n) (v 0) +
    z^(Suc n) * gram_sum z m (\<lambda>i. h (v i) (v (Suc i)))"
proof -
  have L: "p i = u i" if "i < Suc n" for i
    using gram_ports_left[of i l a b r] lengths that by (simp add: p_def u_def)
  have R: "p (Suc n + j) = v j" for j
    using gram_ports_right[of a b l r j] lengths by (simp add: p_def v_def)
  have left: "gram_sum z n (\<lambda>i. h (p i) (p (Suc i))) =
      gram_sum z n (\<lambda>i. h (u i) (u (Suc i)))"
    by (rule gram_sum_cong) (simp add: L)
  have right: "gram_sum z m (\<lambda>i. h (p (Suc n+i)) (p (Suc (Suc n+i)))) =
      gram_sum z m (\<lambda>i. h (v i) (v (Suc i)))"
    by (rule gram_sum_cong) (metis R add_Suc_right)
  have seam: "p (Suc n) = v 0" using R[of 0] by simp
  have size: "length(l@r)-1 = Suc n + m" using lengths by simp
  show ?thesis unfolding size
    by (subst gram_sum_split) (simp only: gram_sum.simps left L[of n] lessI seam right)
qed

ML \<open>
  val checked = @{thms gram_aligned_ordered_join gram_adjacent_ordered_join
    physical_q19_ordered_gram_domain_refinement};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Ordered carry Gram depends on an oracle";
  val _ = if not (Thm_Deps.has_skip_proof checked) then ()
    else error "Ordered carry Gram has skipped proofs";
\<close>

end
