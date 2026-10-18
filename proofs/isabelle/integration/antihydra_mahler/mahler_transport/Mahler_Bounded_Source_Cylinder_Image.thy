theory Mahler_Bounded_Source_Cylinder_Image
  imports Mahler_Odd_Source_Scheduler_Refinement
    "Shared_S_Arithmetic.Integer_Cylinder_Transport"
begin

text \<open>A bounded, complete source progression follows one admitted odd
word whenever its stride preserves the word and the terminal odd seam.  The
image theorem uses the shared integer-progression affine law; its family
premises establish that the arithmetic orbit is exactly that affine action.
Fractional safety and the Antihydra ledger remain separate observations, as
in the scheduler refinement imported above.\<close>

lemma mahler_odd_word_endpoint_odd:
  assumes admitted: "mahler_odd_word_admitted D as"
      and nonempty: "as \<noteq> []"
  shows "odd (mahler_odd_word_endpoint as D)"
  using admitted nonempty
proof (induction as arbitrary: D)
  case Nil
  then show ?case by simp
next
  case (Cons a as)
  obtain k u where a: "a = Suc k"
      and split: "3*D+1 = 2^(Suc k)*u"
      and odd_u: "odd u"
      and tail: "mahler_odd_word_admitted (3^k*u) as"
    using Cons.prems(1) by auto
  have odd_D: "odd D"
    by (rule mahler_positive_two_power_split_source_odd[OF split])
  have block:
    "mahler_orbit D (Suc k) = 3^k*u"
    "odd (mahler_orbit D (Suc k))"
    using mahler_odd_event_block_refines_endpoint_and_ledger[
      OF odd_D split odd_u] by blast+
  have endpoint_block:
    "mahler_odd_word_endpoint (a#as) D =
      mahler_odd_word_endpoint as (3^k*u)"
    using block(1) a by simp
  have tail_odd:
    "as \<noteq> [] \<Longrightarrow> odd (mahler_odd_word_endpoint as (3^k*u))"
    using Cons.IH[OF tail] .
  show ?case
  proof (cases as)
    case Nil
    show ?thesis using Nil a block(2) by simp
  next
    case (Cons b bs)
    have tail_nonempty: "as \<noteq> []" using Cons by simp
    have "odd (mahler_odd_word_endpoint as (3^k*u))"
      using tail_odd tail_nonempty by blast
    then show ?thesis using endpoint_block by simp
  qed
qed

theorem mahler_odd_word_bounded_cylinder_image:
  fixes D L stride count :: nat and as :: "nat list" and t :: real
  assumes admitted: "mahler_odd_word_admitted D as"
      and extent: "L = mahler_odd_word_span as"
      and positive_extent: "0 < L"
      and positive_stride: "0 < stride"
      and seam_stride: "2^(Suc L) dvd stride"
  defines "target_stride \<equiv> 3^L * (stride div 2^L)"
  shows
    "(\<lambda>x. int (mahler_orbit (nat x) L)) `
        integer_progression (int D) (int stride) count =
      integer_progression (int (mahler_orbit D L))
        (int target_stride) count"
    and "\<forall>i<count. odd (mahler_orbit (D + stride*i) L)"
    and "\<forall>i<count. cylinder_guard (D + stride*i) L t =
        cylinder_guard D L t"
    and "\<forall>i<count. mahler_odd_word_admitted (D + stride*i) as"
    and "card ((\<lambda>x. int (mahler_orbit (nat x) L)) `
        integer_progression (int D) (int stride) count) = count"
proof -
  obtain q where stride_eq: "stride = 2^(Suc L) * q"
    using seam_stride unfolding dvd_def by blast
  have stride_factor: "stride = 2^L * (2*q)"
    using stride_eq by (simp add: power_Suc mult.assoc)
  have target_stride_eq:
    "target_stride = 3^L * (2*q)"
    using stride_factor positive_extent
    unfolding target_stride_def
    by (simp add: power_Suc mult.assoc)
  have q_positive: "0 < q"
    using positive_stride stride_eq by (cases q) auto
  have target_stride_positive: "0 < int target_stride"
    using target_stride_eq q_positive by simp
  have nonempty: "as \<noteq> []"
    using extent positive_extent unfolding mahler_odd_word_span_def
    by (cases as) auto
  have source_admitted:
    "mahler_odd_word_admitted (D + stride*i) as" if "i<count" for i
  proof -
    have lifted_source:
      "D + stride*i = D + (q*i) * 2^(Suc (mahler_odd_word_span as))"
      using stride_eq extent by (simp add: algebra_simps)
    have lifted_admitted:
      "mahler_odd_word_admitted
        (D + (q*i) * 2^(Suc (mahler_odd_word_span as))) as"
      by (rule mahler_odd_word_admitted_high_fiber[OF admitted])
    show ?thesis
      using lifted_admitted lifted_source
      by (simp only: lifted_source lifted_admitted)
  qed
  have endpoint_odd:
    "odd (mahler_orbit (D + stride*i) L)" if "i<count" for i
  proof -
    have "odd (mahler_odd_word_endpoint as (D + stride*i))"
      by (rule mahler_odd_word_endpoint_odd[OF source_admitted[OF that]
        nonempty])
    then have "odd (mahler_orbit (D + stride*i)
        (mahler_odd_word_span as))"
      using mahler_odd_word_refines_endpoint_events_and_ledger(1)[
        OF source_admitted[OF that]] by simp
    then show ?thesis using extent by simp
  qed
  have guard_same:
    "cylinder_guard (D + stride*i) L t = cylinder_guard D L t"
    if "i<count" for i
  proof -
    have source_form:
      "D + stride*i = D + 2^L * (2*q*i)"
      using stride_factor by (simp add: algebra_simps)
    show ?thesis
      unfolding source_form
      by (rule guard_high_fiber_translation[of D L "2*q*i" t])
  qed
  have affine_offset:
    "(3::int)^L * int D +
        (2^L * int (mahler_orbit D L) - 3^L * int D) =
      int (2^L) * int (mahler_orbit D L)"
    by (simp add: algebra_simps)
  have affine_stride:
    "(3::int)^L * int stride =
      int (2^L) * int target_stride"
    using stride_factor target_stride_eq
    by (simp add: algebra_simps)
  have generic_image:
    "(\<lambda>x. ((3::int)^L*x +
        (2^L * int (mahler_orbit D L) - 3^L * int D)) div
          int (2^L)) ` integer_progression (int D) (int stride) count =
      integer_progression (int (mahler_orbit D L))
        (int target_stride) count"
    by (rule integer_progression_affine_image[where target_stride=
        "int target_stride" and target="int (mahler_orbit D L)"];
        simp_all add: affine_offset affine_stride)
  have pointwise:
    "int (mahler_orbit (D + stride*i) L) =
      ((3::int)^L * int (D + stride*i) +
        (2^L * int (mahler_orbit D L) - 3^L * int D)) div
          int (2^L)" if "i<count" for i
  proof -
    have source_form:
      "D + stride*i = D + (2*q*i) * 2^L"
      using stride_factor by (simp add: algebra_simps)
    have lifted_orbit:
      "mahler_orbit (D + (2*q*i) * 2^L) L =
        mahler_orbit D L + (2*q*i) * 3^L"
      using moving_source_cylinder[of L L D "2*q*i"] by simp
    have orbit:
      "mahler_orbit (D + stride*i) L =
        mahler_orbit D L + (2*q*i) * 3^L"
      unfolding source_form
      by (rule lifted_orbit)
    show ?thesis
      using orbit stride_factor target_stride_eq
      by (simp add: algebra_simps; simp add: power_add)
  qed
  have actual_image:
    "(\<lambda>x. int (mahler_orbit (nat x) L)) `
        integer_progression (int D) (int stride) count =
      (\<lambda>x. ((3::int)^L*x +
        (2^L * int (mahler_orbit D L) - 3^L * int D)) div
          int (2^L)) ` integer_progression (int D) (int stride) count"
  proof (rule image_cong)
    show "integer_progression (int D) (int stride) count =
        integer_progression (int D) (int stride) count" by simp
    fix x
    assume member: "x \<in> integer_progression (int D) (int stride) count"
    then obtain i where i_lt: "i<count" and x_eq: "x = int D + int i * int stride"
      unfolding integer_progression_def by auto
    have x_as_int: "x = int (D + stride*i)"
      using x_eq by (simp add: algebra_simps)
    have nat_source: "nat x = D + stride*i"
      by (simp only: x_as_int nat_int)
    have
      "int (mahler_orbit (nat x) L) =
          int (mahler_orbit (D + stride*i) L)"
        by (simp only: nat_source)
      also have "... =
          ((3::int)^L * int (D + stride*i) +
            (2^L * int (mahler_orbit D L) - 3^L * int D)) div
              int (2^L)"
        by (rule pointwise[OF i_lt])
      also have "... =
          ((3::int)^L*x +
            (2^L * int (mahler_orbit D L) - 3^L * int D)) div
              int (2^L)"
        by (simp only: x_as_int)
      finally show
        "int (mahler_orbit (nat x) L) =
          ((3::int)^L*x +
            (2^L * int (mahler_orbit D L) - 3^L * int D)) div
              int (2^L)" .
  qed
  show image:
    "(\<lambda>x. int (mahler_orbit (nat x) L)) `
        integer_progression (int D) (int stride) count =
      integer_progression (int (mahler_orbit D L))
        (int target_stride) count"
    using actual_image generic_image by simp
  show "\<forall>i<count. odd (mahler_orbit (D + stride*i) L)"
    using endpoint_odd by blast
  show "\<forall>i<count. cylinder_guard (D + stride*i) L t =
      cylinder_guard D L t"
    using guard_same by blast
  show "\<forall>i<count. mahler_odd_word_admitted (D + stride*i) as"
    using source_admitted by blast
  show "card ((\<lambda>x. int (mahler_orbit (nat x) L)) `
      integer_progression (int D) (int stride) count) = count"
    using image integer_progression_card[OF target_stride_positive] by simp
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms mahler_odd_word_endpoint_odd
      mahler_odd_word_bounded_cylinder_image}) then ()
    else error "Mahler bounded cylinder transport depends on an oracle";
\<close>

end
