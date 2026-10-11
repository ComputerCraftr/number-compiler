theory Comma_Semantic_Producer_Affine_Algebra
  imports Comma_Semantic_Producer_Coefficients
begin

text \<open>Reusable laws for positive-denominator normalized affine triples.  This
owner is consumed by the actual pending-fragment writer refinement; it does
not postulate producer correctness.\<close>

lemma comma_python_affine_add_positive:
  assumes a: "0 < comma_python_affine_denominator a"
    and b: "0 < comma_python_affine_denominator b"
  shows "0 < comma_python_affine_denominator
    (comma_python_affine_add a b)"
  using a b by (simp add: comma_python_affine_add_def
    comma_python_affine_normalize_positive_denominator)

lemma comma_python_affine_fold_positive:
  assumes initial: "0 < comma_python_affine_denominator z"
    and entries: "\<forall>x\<in>set xs. 0 < comma_python_affine_denominator x"
  shows "0 < comma_python_affine_denominator
    (foldl comma_python_affine_add z xs)"
  using initial entries
proof (induction xs arbitrary: z)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  have x: "0 < comma_python_affine_denominator x"
    using Cons.prems(2) by simp
  have head: "0 < comma_python_affine_denominator
      (comma_python_affine_add z x)"
    by (rule comma_python_affine_add_positive[OF Cons.prems(1) x])
  show ?case
    using Cons.IH[OF head] Cons.prems(2) by simp
qed

lemma comma_python_affine_add_assoc_equivalent:
  assumes a: "0 < comma_python_affine_denominator a"
    and b: "0 < comma_python_affine_denominator b"
    and c: "0 < comma_python_affine_denominator c"
  shows "comma_python_affine_equivalent
    (comma_python_affine_add (comma_python_affine_add a b) c)
    (comma_python_affine_add a (comma_python_affine_add b c))"
proof -
  have ab: "0 < comma_python_affine_denominator
      (comma_python_affine_add a b)"
    by (rule comma_python_affine_add_positive[OF a b])
  have bc: "0 < comma_python_affine_denominator
      (comma_python_affine_add b c)"
    by (rule comma_python_affine_add_positive[OF b c])
  let ?rab = "comma_python_affine_raw
    (comma_python_affine_scale a * int (comma_python_affine_denominator b) +
     comma_python_affine_scale b * int (comma_python_affine_denominator a))
    (comma_python_affine_offset a * int (comma_python_affine_denominator b) +
     comma_python_affine_offset b * int (comma_python_affine_denominator a))
    (comma_python_affine_denominator a * comma_python_affine_denominator b)"
  let ?raw =
    "comma_python_affine_raw
      (comma_python_affine_scale a *
         int (comma_python_affine_denominator b) *
         int (comma_python_affine_denominator c) +
       comma_python_affine_scale b *
         int (comma_python_affine_denominator a) *
         int (comma_python_affine_denominator c) +
       comma_python_affine_scale c *
         int (comma_python_affine_denominator a) *
         int (comma_python_affine_denominator b))
      (comma_python_affine_offset a *
         int (comma_python_affine_denominator b) *
         int (comma_python_affine_denominator c) +
       comma_python_affine_offset b *
         int (comma_python_affine_denominator a) *
         int (comma_python_affine_denominator c) +
       comma_python_affine_offset c *
         int (comma_python_affine_denominator a) *
         int (comma_python_affine_denominator b))
      (comma_python_affine_denominator a *
         comma_python_affine_denominator b *
         comma_python_affine_denominator c)"
  have rab_pos: "0 < comma_python_affine_denominator ?rab"
    using a b by (simp add: comma_python_affine_raw_def)
  have rab: "comma_python_affine_equivalent
      (comma_python_affine_add a b) ?rab"
    by (rule comma_python_affine_add_raw[OF a b])
  have c_refl: "comma_python_affine_equivalent c c"
    by (rule comma_python_affine_equivalent_refl[OF c])
  have left_cong: "comma_python_affine_equivalent
      (comma_python_affine_add (comma_python_affine_add a b) c)
      (comma_python_affine_add ?rab c)"
    by (rule comma_python_affine_add_cong[OF rab c_refl])
  have left_raw: "comma_python_affine_equivalent
      (comma_python_affine_add ?rab c) ?raw"
    using comma_python_affine_add_raw[OF rab_pos c]
    by (simp add: comma_python_affine_raw_def algebra_simps)
  have left_middle: "0 < comma_python_affine_denominator
      (comma_python_affine_add ?rab c)"
    by (rule comma_python_affine_add_positive[OF rab_pos c])
  have left: "comma_python_affine_equivalent
      (comma_python_affine_add (comma_python_affine_add a b) c) ?raw"
    by (rule comma_python_affine_equivalent_trans
      [OF left_cong left_raw left_middle])
  let ?rbc = "comma_python_affine_raw
      (comma_python_affine_scale b *
         int (comma_python_affine_denominator c) +
       comma_python_affine_scale c *
         int (comma_python_affine_denominator b))
      (comma_python_affine_offset b *
         int (comma_python_affine_denominator c) +
       comma_python_affine_offset c *
         int (comma_python_affine_denominator b))
      (comma_python_affine_denominator b *
         comma_python_affine_denominator c)"
  have rbc_pos: "0 < comma_python_affine_denominator ?rbc"
    using b c by (simp add: comma_python_affine_raw_def)
  have rbc: "comma_python_affine_equivalent
      (comma_python_affine_add b c) ?rbc"
    by (rule comma_python_affine_add_raw[OF b c])
  have a_refl: "comma_python_affine_equivalent a a"
    by (rule comma_python_affine_equivalent_refl[OF a])
  have right_cong: "comma_python_affine_equivalent
      (comma_python_affine_add a (comma_python_affine_add b c))
      (comma_python_affine_add a ?rbc)"
    by (rule comma_python_affine_add_cong[OF a_refl rbc])
  have right_raw: "comma_python_affine_equivalent
      (comma_python_affine_add a ?rbc) ?raw"
    using comma_python_affine_add_raw[OF a rbc_pos]
    by (simp add: comma_python_affine_raw_def algebra_simps)
  have right_middle: "0 < comma_python_affine_denominator
      (comma_python_affine_add a ?rbc)"
    by (rule comma_python_affine_add_positive[OF a rbc_pos])
  have right: "comma_python_affine_equivalent
      (comma_python_affine_add a (comma_python_affine_add b c)) ?raw"
    by (rule comma_python_affine_equivalent_trans
      [OF right_cong right_raw right_middle])
  have raw_pos: "0 < comma_python_affine_denominator ?raw"
    using a b c by (simp add: comma_python_affine_raw_def)
  have raw_sym: "comma_python_affine_equivalent ?raw
      (comma_python_affine_add a (comma_python_affine_add b c))"
    by (rule comma_python_affine_equivalent_sym[OF right])
  show ?thesis
    by (rule comma_python_affine_equivalent_trans[OF left raw_sym raw_pos])
qed

lemma comma_python_affine_fold_equivalent_starts:
  assumes starts: "comma_python_affine_equivalent a b"
    and positive: "\<forall>x\<in>set xs. 0 < comma_python_affine_denominator x"
  shows "comma_python_affine_equivalent
    (foldl comma_python_affine_add a xs)
    (foldl comma_python_affine_add b xs)"
  using starts positive
proof (induction xs arbitrary: a b)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  have x_refl: "comma_python_affine_equivalent x x"
    using Cons.prems(2) by (simp add: comma_python_affine_equivalent_def)
  have first: "comma_python_affine_equivalent
      (comma_python_affine_add a x) (comma_python_affine_add b x)"
    by (rule comma_python_affine_add_cong[OF Cons.prems(1) x_refl])
  show ?case using Cons.IH[OF first] Cons.prems(2) by simp
qed

lemma comma_python_affine_fold_replace_last:
  assumes initial: "0 < comma_python_affine_denominator z"
    and prefix: "\<forall>x\<in>set xs.
      0 < comma_python_affine_denominator x"
    and x: "0 < comma_python_affine_denominator a"
    and y: "0 < comma_python_affine_denominator b"
    and equivalent: "comma_python_affine_equivalent a b"
  shows "comma_python_affine_equivalent
    (foldl comma_python_affine_add z (xs @ [a]))
    (foldl comma_python_affine_add z (xs @ [b]))"
proof -
  let ?prefix = "foldl comma_python_affine_add z xs"
  have prefix_positive:
    "0 < comma_python_affine_denominator ?prefix"
    by (rule comma_python_affine_fold_positive[OF initial prefix])
  have prefix_refl:
    "comma_python_affine_equivalent ?prefix ?prefix"
    by (rule comma_python_affine_equivalent_refl[OF prefix_positive])
  have result:
    "comma_python_affine_equivalent
      (comma_python_affine_add ?prefix a)
      (comma_python_affine_add ?prefix b)"
    by (rule comma_python_affine_add_cong[OF prefix_refl equivalent])
  show ?thesis using result by (simp add: foldl_append)
qed

lemmas comma_python_producer_affine_algebra_oracle_audit_bundle =
  comma_python_affine_add_positive
  comma_python_affine_fold_positive
  comma_python_affine_add_assoc_equivalent
  comma_python_affine_fold_equivalent_starts
  comma_python_affine_fold_replace_last
ML \<open>val _ = if null (Thm_Deps.all_oracles
  @{thms comma_python_producer_affine_algebra_oracle_audit_bundle}) then ()
  else error "Comma_Semantic_Producer_Affine_Algebra local oracle audit failed"\<close>

end
