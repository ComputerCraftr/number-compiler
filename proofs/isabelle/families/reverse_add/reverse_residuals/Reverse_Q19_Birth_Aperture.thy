theory Reverse_Q19_Birth_Aperture
  imports Reverse_Q19_Birth_Ingress
begin

text \<open>The ordered reference is connected to an admitted physical pair word
at every positive cut. Both unresolved carries are the exact carries of the
unread physical suffixes; no future width or return is assumed.\<close>

lemma q19_bi_reverse_drop_carry:
  assumes "i < length xs"
  shows "carry_out False (rev (drop i xs)) =
    carry_apply (domain (xs!i)) (carry_out False (rev (drop (Suc i) xs)))"
proof -
  have "drop i xs = xs!i # drop (Suc i) xs"
    using Cons_nth_drop_Suc[OF assms] by simp
  then show ?thesis by (simp add: carry_out_append carry_out_def)
qed

lemma q19_bi_left_carry_step:
  assumes "i < length xs"
  shows "carry_out False (take (Suc i) xs) =
    carry_apply (domain (xs!i)) (carry_out False (take i xs))"
  using take_Suc_conv_app_nth[OF assms]
  by (simp add: carry_out_append carry_out_def)

theorem q19_bi_aperture_reference:
  assumes valid: "valid_pair source" and growth: "carry_out False source"
      and positive: "0 < k" and bound: "k + n \<le> length source"
  shows "q19_bi_reference (carry_out False (take k source)) (source!(k-1) mod 10)
      (take n (drop k source))
      (carry_out False (rev (drop (k+n) source)))
      (carry_out False (rev (drop (k+n) (step source)))) =
    (carry_out False (rev (drop k source)), carry_out False (rev (drop k (step source))))"
  using positive bound
proof (induction n arbitrary: k)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have ix: "k < length source" using Suc.prems by arith
  have ix_step: "k < length (step source)" using ix by (simp add: length_digits_exact)
  have drop: "drop k source = source!k # drop (Suc k) source"
    using Cons_nth_drop_Suc[OF ix] by simp
  have seg: "take (Suc n) (drop k source) = source!k # take n (drop (Suc k) source)"
    by (simp add: drop)
  have prefix: "carry_out False (take (Suc k) source) =
      carry_apply (domain (source!k)) (carry_out False (take k source))"
    by (rule q19_bi_left_carry_step[OF ix])
  have source_tail: "carry_out False (rev (drop k source)) =
      carry_apply (domain (source!k)) (carry_out False (rev (drop (Suc k) source)))"
    by (rule q19_bi_reverse_drop_carry[OF ix])
  have born_tail: "carry_out False (rev (drop k (step source))) =
      carry_apply (domain (step source!k)) (carry_out False (rev (drop (Suc k) (step source))))"
    by (rule q19_bi_reverse_drop_carry[OF ix_step])
  have born_digit: "step source!k =
      (source!k + q19_bi_bit (carry_out False (take k source))) mod 10 +
      ((source!(k-1) mod 10) + q19_bi_bit
        (carry_apply (domain (source!k)) (carry_out False (rev (drop (Suc k) source))))) mod 10"
    using q19_bi_physical_source_cell[OF valid Suc.prems(1) ix growth]
    by (simp add: mod_add_left_eq)
  have IH: "q19_bi_reference (carry_apply (domain (source!k)) (carry_out False (take k source)))
      (source!k mod 10) (take n (drop (Suc k) source))
      (carry_out False (rev (drop (k + Suc n) source)))
      (carry_out False (rev (drop (k + Suc n) (step source)))) =
    (carry_out False (rev (drop (Suc k) source)), carry_out False (rev (drop (Suc k) (step source))))"
    using Suc.IH[of "Suc k"] Suc.prems prefix by simp
  show ?case
    using IH source_tail born_tail born_digit
    by (simp only: seg q19_bi_reference.simps Let_def IH prod.case source_tail born_tail born_digit)
qed


theorem q19_bi_physical_aperture_singleton:
  assumes valid: "valid_pair source" and growth: "carry_out False source"
      and prefix: "take 2 source = [17,q]" and bound: "2+n \<le> length source"
      and left: "bi_zero (foldl q19_bi_step (q19_bi_initial q) (take n (drop 2 source))) = r"
      and right: "bi_one (foldl q19_bi_step (q19_bi_initial q) (take n (drop 2 source))) = r"
      and singleton: "r = BI_Zero \<or> r = BI_One"
  shows "carry_out False (rev (drop 2 (step source))) = (r = BI_One)"
proof -
  have take_q: "(take 2 source)!1 = q" using prefix by simp
  have q: "source!1 = q" using take_q by simp
  have c: "carry_out False (take 2 source) = carry_apply (domain q) True"
    using prefix by (simp add: carry_out_def domain_def)
  let ?inside = "carry_out False (rev (drop (2+n) source))"
  let ?born = "carry_out False (rev (drop (2+n) (step source)))"
  have physical: "q19_bi_reference (carry_apply (domain q) True) (q mod 10)
      (take n (drop 2 source)) ?inside ?born =
    (carry_out False (rev (drop 2 source)), carry_out False (rev (drop 2 (step source))))"
    using q19_bi_aperture_reference[OF valid growth, of 2 n] bound c q by simp
  have collapsed: "snd (q19_bi_reference (carry_apply (domain q) True) (q mod 10)
      (take n (drop 2 source)) ?inside ?born) = (r = BI_One)"
    by (rule q19_bi_singleton_all_inlets[OF left right singleton])
  show ?thesis using physical collapsed by simp
qed


ML \<open>
  val checked = @{thms q19_bi_reverse_drop_carry q19_bi_left_carry_step
    q19_bi_aperture_reference q19_bi_physical_aperture_singleton};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Q19 physical aperture depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked then
    error "Q19 physical aperture has skipped proofs" else ();
\<close>

end
