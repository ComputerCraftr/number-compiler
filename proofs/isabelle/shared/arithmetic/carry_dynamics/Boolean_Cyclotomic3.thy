theory Boolean_Cyclotomic3
  imports Main
begin

text \<open>
Lossless three-phase Boolean coordinates for a cyclic order-three action.
The values are arbitrary Boolean bitplanes (functions on an arbitrary
position type), so the identities apply pointwise to any packed width.  This
is a change of basis only: it does not assert a quotient of any guarded
comma action or a physical carry period.
\<close>

type_synonym 'i boolean_bitplane = "'i \<Rightarrow> bool"
type_synonym 'i boolean_phase_triple =
  "'i boolean_bitplane \<times> 'i boolean_bitplane \<times> 'i boolean_bitplane"

definition boolean_bitplane_xor ::
    "'i boolean_bitplane \<Rightarrow> 'i boolean_bitplane \<Rightarrow> 'i boolean_bitplane" where
  "boolean_bitplane_xor a b = (\<lambda>i. a i \<noteq> b i)"

definition boolean_bitplane_and ::
    "'i boolean_bitplane \<Rightarrow> 'i boolean_bitplane \<Rightarrow> 'i boolean_bitplane" where
  "boolean_bitplane_and a b = (\<lambda>i. a i \<and> b i)"

definition boolean_cyclotomic3_encode ::
    "'i boolean_phase_triple \<Rightarrow> 'i boolean_phase_triple" where
  "boolean_cyclotomic3_encode triple =
    (case triple of (x0,x1,x2) \<Rightarrow>
      (boolean_bitplane_xor (boolean_bitplane_xor x0 x1) x2,
       boolean_bitplane_xor x0 x1,
       boolean_bitplane_xor x1 x2))"

definition boolean_cyclotomic3_decode ::
    "'i boolean_phase_triple \<Rightarrow> 'i boolean_phase_triple" where
  "boolean_cyclotomic3_decode triple =
    (case triple of (c,u,v) \<Rightarrow>
      (boolean_bitplane_xor c v,
       boolean_bitplane_xor (boolean_bitplane_xor c u) v,
       boolean_bitplane_xor c u))"

lemma boolean_bitplane_xor_assoc:
  "boolean_bitplane_xor (boolean_bitplane_xor a b) c =
    boolean_bitplane_xor a (boolean_bitplane_xor b c)"
  by (rule ext) (auto simp: boolean_bitplane_xor_def)

lemma boolean_bitplane_xor_commute:
  "boolean_bitplane_xor a b = boolean_bitplane_xor b a"
  by (rule ext) (auto simp: boolean_bitplane_xor_def)

lemma boolean_bitplane_xor_self:
  "boolean_bitplane_xor a a = (\<lambda>_. False)"
  by (rule ext) (simp add: boolean_bitplane_xor_def)

lemma boolean_cyclotomic3_decode_encode:
  "boolean_cyclotomic3_decode (boolean_cyclotomic3_encode (x0,x1,x2)) =
    (x0,x1,x2)"
  by (auto simp: boolean_cyclotomic3_encode_def boolean_cyclotomic3_decode_def
      boolean_bitplane_xor_def fun_eq_iff)

lemma boolean_cyclotomic3_encode_decode:
  "boolean_cyclotomic3_encode (boolean_cyclotomic3_decode (c,u,v)) =
    (c,u,v)"
  by (auto simp: boolean_cyclotomic3_encode_def boolean_cyclotomic3_decode_def
      boolean_bitplane_xor_def fun_eq_iff)

definition boolean_cyclotomic3_shift ::
    "'i boolean_phase_triple \<Rightarrow> 'i boolean_phase_triple" where
  "boolean_cyclotomic3_shift triple =
    (case triple of (c,u,v) \<Rightarrow> (c,v,boolean_bitplane_xor u v))"

lemma boolean_cyclotomic3_encode_rotate:
  "boolean_cyclotomic3_encode (x1,x2,x0) =
    boolean_cyclotomic3_shift (boolean_cyclotomic3_encode (x0,x1,x2))"
  by (auto simp: boolean_cyclotomic3_encode_def boolean_cyclotomic3_shift_def
      boolean_bitplane_xor_def fun_eq_iff)

lemma boolean_cyclotomic3_shift_cubic:
  "boolean_cyclotomic3_shift (boolean_cyclotomic3_shift
    (boolean_cyclotomic3_shift (c,u,v))) = (c,u,v)"
  by (auto simp: boolean_cyclotomic3_shift_def boolean_bitplane_xor_def fun_eq_iff)

definition boolean_cyclotomic3_pointwise_and ::
    "'i boolean_phase_triple \<Rightarrow> 'i boolean_phase_triple \<Rightarrow>
      'i boolean_phase_triple" where
  "boolean_cyclotomic3_pointwise_and x y =
    boolean_cyclotomic3_encode
      (case boolean_cyclotomic3_decode x of (x0,x1,x2) \<Rightarrow>
       case boolean_cyclotomic3_decode y of (y0,y1,y2) \<Rightarrow>
         (boolean_bitplane_and x0 y0,
          boolean_bitplane_and x1 y1,
          boolean_bitplane_and x2 y2))"

lemma boolean_cyclotomic3_and_cross_terms:
  "boolean_cyclotomic3_pointwise_and (c,u,v) (d,s,t) =
    (boolean_bitplane_xor (boolean_bitplane_xor
       (boolean_bitplane_and c d) (boolean_bitplane_and u t))
       (boolean_bitplane_and v s),
     boolean_bitplane_xor (boolean_bitplane_xor
       (boolean_bitplane_xor (boolean_bitplane_xor
         (boolean_bitplane_and c s) (boolean_bitplane_and u d))
         (boolean_bitplane_and u s))
       (boolean_bitplane_and u t)) (boolean_bitplane_and v s),
     boolean_bitplane_xor (boolean_bitplane_xor
       (boolean_bitplane_xor (boolean_bitplane_xor
         (boolean_bitplane_and c t) (boolean_bitplane_and u t))
         (boolean_bitplane_and v d))
       (boolean_bitplane_and v s)) (boolean_bitplane_and v t))"
  by (auto simp: boolean_cyclotomic3_pointwise_and_def boolean_cyclotomic3_decode_def
      boolean_cyclotomic3_encode_def boolean_bitplane_xor_def boolean_bitplane_and_def
      fun_eq_iff)

definition boolean_cyclotomic3_drop_constant ::
    "'i boolean_phase_triple \<Rightarrow> 'i boolean_bitplane \<times> 'i boolean_bitplane" where
  "boolean_cyclotomic3_drop_constant triple =
    (case triple of (c,u,v) \<Rightarrow> (u,v))"

lemma boolean_cyclotomic3_constant_channel_counterexample:
  "boolean_cyclotomic3_drop_constant
      (boolean_cyclotomic3_encode ((\<lambda>_. False), (\<lambda>_. False), (\<lambda>_. False))) =
    boolean_cyclotomic3_drop_constant
      (boolean_cyclotomic3_encode ((\<lambda>_. True), (\<lambda>_. True), (\<lambda>_. True))) \<and>
   fst (boolean_cyclotomic3_drop_constant
      (boolean_cyclotomic3_pointwise_and
        (boolean_cyclotomic3_encode ((\<lambda>_. False), (\<lambda>_. False), (\<lambda>_. False)))
        (boolean_cyclotomic3_encode ((\<lambda>_. True), (\<lambda>_. False), (\<lambda>_. False))))) 0 \<noteq>
   fst (boolean_cyclotomic3_drop_constant
      (boolean_cyclotomic3_pointwise_and
        (boolean_cyclotomic3_encode ((\<lambda>_. True), (\<lambda>_. True), (\<lambda>_. True)))
        (boolean_cyclotomic3_encode ((\<lambda>_. True), (\<lambda>_. False), (\<lambda>_. False))))) 0"
  by (simp add: boolean_cyclotomic3_drop_constant_def
      boolean_cyclotomic3_encode_def boolean_cyclotomic3_pointwise_and_def
      boolean_cyclotomic3_decode_def boolean_bitplane_xor_def boolean_bitplane_and_def
      fun_eq_iff)

definition boolean_six_phase_harmonic ::
    "'i boolean_bitplane \<Rightarrow> 'i boolean_bitplane \<Rightarrow>
      'i boolean_bitplane \<Rightarrow> 'i boolean_bitplane \<Rightarrow>
      'i boolean_bitplane \<Rightarrow> 'i boolean_bitplane \<Rightarrow>
      'i boolean_phase_triple" where
  "boolean_six_phase_harmonic a b c d e f =
    boolean_cyclotomic3_encode
      (boolean_bitplane_xor a d, boolean_bitplane_xor b e,
       boolean_bitplane_xor c f)"

lemma boolean_six_phase_harmonic_rotate:
  "boolean_six_phase_harmonic b c d e f a =
    boolean_cyclotomic3_shift (boolean_six_phase_harmonic a b c d e f)"
  unfolding boolean_six_phase_harmonic_def
  by (simp only: boolean_bitplane_xor_commute[of d a];
      rule boolean_cyclotomic3_encode_rotate)

lemma boolean_six_phase_harmonic_output:
  "boolean_cyclotomic3_drop_constant (boolean_six_phase_harmonic a b c d e f) =
    (boolean_bitplane_xor (boolean_bitplane_xor a d) (boolean_bitplane_xor b e),
     boolean_bitplane_xor (boolean_bitplane_xor b e) (boolean_bitplane_xor c f))"
  by (simp add: boolean_six_phase_harmonic_def boolean_cyclotomic3_encode_def
      boolean_cyclotomic3_drop_constant_def)

lemma boolean_cyclotomic3_output_shift:
  "boolean_cyclotomic3_drop_constant (boolean_cyclotomic3_shift state) =
    (snd (boolean_cyclotomic3_drop_constant state),
     boolean_bitplane_xor (fst (boolean_cyclotomic3_drop_constant state))
       (snd (boolean_cyclotomic3_drop_constant state)))"
  by (simp add: boolean_cyclotomic3_drop_constant_def
      boolean_cyclotomic3_shift_def case_prod_unfold)

ML \<open>
  val checked = @{thms boolean_cyclotomic3_decode_encode
    boolean_cyclotomic3_encode_decode boolean_cyclotomic3_encode_rotate
    boolean_cyclotomic3_shift_cubic boolean_cyclotomic3_and_cross_terms
    boolean_cyclotomic3_constant_channel_counterexample
    boolean_six_phase_harmonic_rotate boolean_six_phase_harmonic_output
    boolean_cyclotomic3_output_shift}
  val _ = if null (Thm_Deps.all_oracles checked)
    then () else error "Boolean cyclotomic-three algebra depends on an oracle"
\<close>

end
