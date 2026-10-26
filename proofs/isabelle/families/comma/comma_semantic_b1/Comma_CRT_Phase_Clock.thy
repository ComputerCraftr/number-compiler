theory Comma_CRT_Phase_Clock
  imports Comma_Symbolic_Phase_Masks
begin

text \<open>
The four selector coordinates are the external CRT clock C4 x C3 x C7 x C11.
The weights below are CRT idempotents: each is one on its own coordinate and
zero on the other three. The rebase operation changes exactly one coordinate.
\<close>

definition comma_crt_axis_radix :: "nat \<Rightarrow> nat" where
  "comma_crt_axis_radix axis =
    (if axis=0 then 4 else if axis=1 then 3 else if axis=2 then 7 else
      if axis=3 then 11 else 1)"

definition comma_crt_axis_weight :: "nat \<Rightarrow> nat" where
  "comma_crt_axis_weight axis =
    (if axis=0 then 693 else if axis=1 then 616 else if axis=2 then 792 else
      if axis=3 then 672 else 0)"

lemma comma_crt_axis_cases:
  fixes axis :: nat
  assumes axis: "axis<4"
  shows "axis=0 \<or> axis=1 \<or> axis=2 \<or> axis=3"
  using axis by arith

definition comma_crt_clock :: "nat \<Rightarrow> nat" where
  "comma_crt_clock phase =
    (693*(phase mod 4)+616*(phase mod 3)+
      792*(phase mod 7)+672*(phase mod 11)) mod 924"

definition comma_crt_rebase :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_crt_rebase axis slot phase =
    (phase + comma_crt_axis_weight axis *
      ((slot + comma_crt_axis_radix axis -
        phase mod comma_crt_axis_radix axis) mod
          comma_crt_axis_radix axis)) mod 924"

definition comma_crt_suffix :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_crt_suffix axis phase =
    (if axis=0 then 693*(phase mod 4)+616*(phase mod 3)+
        792*(phase mod 7)+672*(phase mod 11)
     else if axis=1 then 616*(phase mod 3)+792*(phase mod 7)+672*(phase mod 11)
     else if axis=2 then 792*(phase mod 7)+672*(phase mod 11)
     else if axis=3 then 672*(phase mod 11)
     else 0)"

lemma comma_crt_suffix_step:
  assumes axis: "axis<4"
  shows "comma_crt_suffix axis phase=
    comma_crt_axis_weight axis*(phase mod comma_crt_axis_radix axis)+
      comma_crt_suffix (Suc axis) phase"
  using comma_crt_axis_cases[OF axis]
  by (auto simp: comma_crt_suffix_def comma_crt_axis_weight_def
    comma_crt_axis_radix_def)

lemma comma_crt_suffix_zero_is_clock:
  "comma_crt_suffix 0 phase mod 924=comma_crt_clock phase"
  by (simp add: comma_crt_suffix_def comma_crt_clock_def)

lemma comma_crt_axis_radices_divide_924:
  "comma_crt_axis_radix axis dvd 924" if "axis<4"
  using comma_crt_axis_cases[OF that] by (auto simp: comma_crt_axis_radix_def)

lemma comma_crt_mod_four_sum:
  fixes a b c d modulus :: nat
  shows "(a+b+c+d) mod modulus=
    ((((a mod modulus+b mod modulus) mod modulus+c mod modulus)
      mod modulus+d mod modulus) mod modulus)"
  by (simp only: mod_add_eq)

lemma comma_crt_weighted_term:
  fixes coefficient source_value modulus residue :: nat
  assumes coefficient: "coefficient mod modulus=residue"
  shows "(coefficient*source_value) mod modulus=
    (residue*(source_value mod modulus)) mod modulus"
proof -
  have "(coefficient*source_value) mod modulus=
      ((coefficient mod modulus)*(source_value mod modulus)) mod modulus"
    by (rule mod_mult_eq[symmetric])
  also have "...=(residue*(source_value mod modulus)) mod modulus"
    using coefficient by simp
  finally show ?thesis .
qed

lemma comma_crt_mod_zero_add:
  fixes left right modulus :: nat
  assumes left: "left mod modulus=0" and right: "right mod modulus=0"
  shows "(left+right) mod modulus=0"
proof -
  have "(left+right) mod modulus=
      ((left mod modulus)+(right mod modulus)) mod modulus"
    by (rule mod_add_eq[symmetric])
  also have "...=0" using left right by simp
  finally show ?thesis .
qed

lemma comma_crt_clock_mod4:
  "comma_crt_clock phase mod 4=phase mod 4"
proof -
  have divisor: "(4::nat) dvd 924" by simp
  have normalized:
    "comma_crt_clock phase mod 4=
      (693*(phase mod 4)+616*(phase mod 3)+
        792*(phase mod 7)+672*(phase mod 11)) mod 4"
    unfolding comma_crt_clock_def by (rule mod_mod_cancel[OF divisor])
  have c0: "(693::nat) mod 4=1" by simp
  have c1: "(616::nat) mod 4=0" by simp
  have c2: "(792::nat) mod 4=0" by simp
  have c3: "(672::nat) mod 4=0" by simp
  have t0: "(693*(phase mod 4)) mod 4=phase mod 4"
    using comma_crt_weighted_term[OF c0] by simp
  have t1: "(616*(phase mod 3)) mod 4=0"
    using comma_crt_weighted_term[OF c1] by simp
  have t2: "(792*(phase mod 7)) mod 4=0"
    using comma_crt_weighted_term[OF c2] by simp
  have t3: "(672*(phase mod 11)) mod 4=0"
    using comma_crt_weighted_term[OF c3] by simp
  have sum:
    "(693*(phase mod 4)+616*(phase mod 3)+
        792*(phase mod 7)+672*(phase mod 11)) mod 4=
      ((((693*(phase mod 4)) mod 4+(616*(phase mod 3)) mod 4) mod 4+
        (792*(phase mod 7)) mod 4) mod 4+(672*(phase mod 11)) mod 4) mod 4"
    by (rule comma_crt_mod_four_sum)
  show ?thesis using normalized sum t0 t1 t2 t3 by simp
qed

lemma comma_crt_clock_mod3:
  "comma_crt_clock phase mod 3=phase mod 3"
proof -
  have divisor: "(3::nat) dvd 924" by simp
  have normalized:
    "comma_crt_clock phase mod 3=
      (693*(phase mod 4)+616*(phase mod 3)+
        792*(phase mod 7)+672*(phase mod 11)) mod 3"
    unfolding comma_crt_clock_def by (rule mod_mod_cancel[OF divisor])
  have c0: "(693::nat) mod 3=0" by simp
  have c1: "(616::nat) mod 3=1" by simp
  have c2: "(792::nat) mod 3=0" by simp
  have c3: "(672::nat) mod 3=0" by simp
  have t0: "(693*(phase mod 4)) mod 3=0"
    using comma_crt_weighted_term[OF c0] by simp
  have t1: "(616*(phase mod 3)) mod 3=phase mod 3"
    using comma_crt_weighted_term[OF c1] by simp
  have t2: "(792*(phase mod 7)) mod 3=0"
    using comma_crt_weighted_term[OF c2] by simp
  have t3: "(672*(phase mod 11)) mod 3=0"
    using comma_crt_weighted_term[OF c3] by simp
  have sum:
    "(693*(phase mod 4)+616*(phase mod 3)+
        792*(phase mod 7)+672*(phase mod 11)) mod 3=
      ((((693*(phase mod 4)) mod 3+(616*(phase mod 3)) mod 3) mod 3+
        (792*(phase mod 7)) mod 3) mod 3+(672*(phase mod 11)) mod 3) mod 3"
    by (rule comma_crt_mod_four_sum)
  show ?thesis using normalized sum t0 t1 t2 t3 by simp
qed

lemma comma_crt_clock_mod7:
  "comma_crt_clock phase mod 7=phase mod 7"
proof -
  have divisor: "(7::nat) dvd 924" by simp
  have normalized:
    "comma_crt_clock phase mod 7=
      (693*(phase mod 4)+616*(phase mod 3)+
        792*(phase mod 7)+672*(phase mod 11)) mod 7"
    unfolding comma_crt_clock_def by (rule mod_mod_cancel[OF divisor])
  have c0: "(693::nat) mod 7=0" by simp
  have c1: "(616::nat) mod 7=0" by simp
  have c2: "(792::nat) mod 7=1" by simp
  have c3: "(672::nat) mod 7=0" by simp
  have t0: "(693*(phase mod 4)) mod 7=0"
    using comma_crt_weighted_term[OF c0] by simp
  have t1: "(616*(phase mod 3)) mod 7=0"
    using comma_crt_weighted_term[OF c1] by simp
  have t2: "(792*(phase mod 7)) mod 7=phase mod 7"
    using comma_crt_weighted_term[OF c2] by simp
  have t3: "(672*(phase mod 11)) mod 7=0"
    using comma_crt_weighted_term[OF c3] by simp
  have sum:
    "(693*(phase mod 4)+616*(phase mod 3)+
        792*(phase mod 7)+672*(phase mod 11)) mod 7=
      ((((693*(phase mod 4)) mod 7+(616*(phase mod 3)) mod 7) mod 7+
        (792*(phase mod 7)) mod 7) mod 7+(672*(phase mod 11)) mod 7) mod 7"
    by (rule comma_crt_mod_four_sum)
  show ?thesis using normalized sum t0 t1 t2 t3 by simp
qed

lemma comma_crt_clock_mod11:
  "comma_crt_clock phase mod 11=phase mod 11"
proof -
  have divisor: "(11::nat) dvd 924" by simp
  have normalized:
    "comma_crt_clock phase mod 11=
      (693*(phase mod 4)+616*(phase mod 3)+
        792*(phase mod 7)+672*(phase mod 11)) mod 11"
    unfolding comma_crt_clock_def by (rule mod_mod_cancel[OF divisor])
  have c0: "(693::nat) mod 11=0" by simp
  have c1: "(616::nat) mod 11=0" by simp
  have c2: "(792::nat) mod 11=0" by simp
  have c3: "(672::nat) mod 11=1" by simp
  have t0: "(693*(phase mod 4)) mod 11=0"
    using comma_crt_weighted_term[OF c0] by simp
  have t1: "(616*(phase mod 3)) mod 11=0"
    using comma_crt_weighted_term[OF c1] by simp
  have t2: "(792*(phase mod 7)) mod 11=0"
    using comma_crt_weighted_term[OF c2] by simp
  have t3: "(672*(phase mod 11)) mod 11=phase mod 11"
    using comma_crt_weighted_term[OF c3] by simp
  have sum:
    "(693*(phase mod 4)+616*(phase mod 3)+
        792*(phase mod 7)+672*(phase mod 11)) mod 11=
      ((((693*(phase mod 4)) mod 11+(616*(phase mod 3)) mod 11) mod 11+
        (792*(phase mod 7)) mod 11) mod 11+(672*(phase mod 11)) mod 11) mod 11"
    by (rule comma_crt_mod_four_sum)
  show ?thesis using normalized sum t0 t1 t2 t3 by simp
qed

lemma comma_crt_clock_axis_residue:
  assumes axis: "axis<4"
  shows "comma_crt_clock phase mod comma_crt_axis_radix axis=
    phase mod comma_crt_axis_radix axis"
  using comma_crt_axis_cases[OF axis]
  by (auto simp: comma_crt_axis_radix_def
      intro: comma_crt_clock_mod4 comma_crt_clock_mod3
        comma_crt_clock_mod7 comma_crt_clock_mod11)

lemma comma_crt_clock_reconstruct:
  "comma_crt_clock phase=phase mod 924"
proof -
  have c4: "comma_crt_clock phase mod 4=phase mod 4"
    using comma_crt_clock_axis_residue[where axis=0 and phase=phase]
    by (simp add: comma_crt_axis_radix_def)
  have c3: "comma_crt_clock phase mod 3=phase mod 3"
    using comma_crt_clock_axis_residue[where axis=1 and phase=phase]
    by (simp add: comma_crt_axis_radix_def)
  have c7: "comma_crt_clock phase mod 7=phase mod 7"
    using comma_crt_clock_axis_residue[where axis=2 and phase=phase]
    by (simp add: comma_crt_axis_radix_def)
  have c11: "comma_crt_clock phase mod 11=phase mod 11"
    using comma_crt_clock_axis_residue[where axis=3 and phase=phase]
    by (simp add: comma_crt_axis_radix_def)
  have d4: "(4::nat) dvd 12" by simp
  have d3: "(3::nat) dvd 12" by simp
  have phase12_mod4: "(phase mod 12) mod 4=phase mod 4"
    by (rule mod_mod_cancel[OF d4])
  have phase12_mod3: "(phase mod 12) mod 3=phase mod 3"
    by (rule mod_mod_cancel[OF d3])
  have target12: "phase mod 12<12" by simp
  have c12: "comma_crt_clock phase mod 12=phase mod 12"
    using comma_mod_coprime_product_target
      [where left="comma_crt_clock phase" and right="phase mod 12"
        and first=4 and second=3]
      c4 c3 phase12_mod4 phase12_mod3 target12
    by (simp add: coprime_iff_gcd_eq_1 gcd_nat.simps)
  have d12: "(12::nat) dvd 84" by simp
  have d7: "(7::nat) dvd 84" by simp
  have phase84_mod12: "(phase mod 84) mod 12=phase mod 12"
    by (rule mod_mod_cancel[OF d12])
  have phase84_mod7: "(phase mod 84) mod 7=phase mod 7"
    by (rule mod_mod_cancel[OF d7])
  have target84: "phase mod 84<84" by simp
  have c84: "comma_crt_clock phase mod 84=phase mod 84"
    using comma_mod_coprime_product_target
      [where left="comma_crt_clock phase" and right="phase mod 84"
        and first=12 and second=7]
      c12 c7 phase84_mod12 phase84_mod7 target84
    by (simp add: coprime_iff_gcd_eq_1 gcd_nat.simps)
  have d84: "(84::nat) dvd 924" by simp
  have d11: "(11::nat) dvd 924" by simp
  have phase924_mod84: "(phase mod 924) mod 84=phase mod 84"
    by (rule mod_mod_cancel[OF d84])
  have phase924_mod11: "(phase mod 924) mod 11=phase mod 11"
    by (rule mod_mod_cancel[OF d11])
  have target924: "phase mod 924<924" by simp
  have clock_bound: "comma_crt_clock phase<924"
    by (simp add: comma_crt_clock_def)
  show ?thesis
    using comma_mod_coprime_product_target
      [where left="comma_crt_clock phase" and right="phase mod 924"
        and first=84 and second=11]
      c84 c11 phase924_mod84 phase924_mod11 target924 clock_bound
    by (simp add: coprime_iff_gcd_eq_1 gcd_nat.simps)
qed

lemma comma_crt_clock_mod:
  assumes divides: "period dvd 924"
  shows "comma_crt_clock phase mod period=phase mod period"
  using comma_crt_clock_reconstruct divides
  by (metis mod_mod_cancel)

ML \<open>Comma_Fast_Kernel.report "CRT cofactor checkpoint=clock"\<close>

lemma comma_crt_weight_own_residue:
  assumes axis: "axis<4"
  shows "comma_crt_axis_weight axis mod comma_crt_axis_radix axis=1"
  using comma_crt_axis_cases[OF axis]
  by (auto simp: comma_crt_axis_weight_def comma_crt_axis_radix_def)

lemma comma_crt_weight_other_residue:
  assumes axis: "axis<4" and other: "other<4" and distinct: "axis\<noteq>other"
  shows "comma_crt_axis_weight axis mod comma_crt_axis_radix other=0"
proof -
  have axis_cases: "axis=0 \<or> axis=1 \<or> axis=2 \<or> axis=3"
    by (rule comma_crt_axis_cases[OF axis])
  have other_cases: "other=0 \<or> other=1 \<or> other=2 \<or> other=3"
    by (rule comma_crt_axis_cases[OF other])
  show ?thesis using axis_cases other_cases distinct
    by (elim disjE; simp_all add: comma_crt_axis_weight_def
      comma_crt_axis_radix_def)
qed

lemma comma_crt_mod_replacement:
  fixes phase q slot :: nat
  assumes q_positive: "0<q" and slot_bound: "slot<q"
  shows "(phase+((slot+q-phase mod q) mod q)) mod q=slot"
proof -
  let ?residue = "phase mod q"
  have residue_bound: "?residue<q" using q_positive by simp
  have cancellation: "?residue+(slot+q-?residue)=slot+q"
    using residue_bound by arith
  have distributed:
    "(phase+((slot+q-?residue) mod q)) mod q=
      (?residue+((slot+q-?residue) mod q)) mod q"
  proof -
    have "(phase+((slot+q-?residue) mod q)) mod q=
        ((phase mod q)+(((slot+q-?residue) mod q) mod q)) mod q"
      by (rule mod_add_eq[symmetric])
    also have "...=(?residue+((slot+q-?residue) mod q)) mod q"
      by simp
    finally show ?thesis .
  qed
  have reduce:
    "(?residue+((slot+q-?residue) mod q)) mod q=
      (?residue+(slot+q-?residue)) mod q"
    by (rule mod_add_right_eq)
  show ?thesis using distributed reduce cancellation slot_bound by simp
qed

lemma comma_crt_rebase_selected:
  assumes axis: "axis<4" and slot: "slot<comma_crt_axis_radix axis"
    and selected: "slot=phase mod comma_crt_axis_radix axis"
  shows "comma_crt_rebase axis slot phase=phase mod 924"
proof -
  have axis_cases: "axis=0 \<or> axis=1 \<or> axis=2 \<or> axis=3"
    by (rule comma_crt_axis_cases[OF axis])
  show ?thesis using axis_cases slot selected
    by (auto simp: comma_crt_rebase_def comma_crt_axis_weight_def
      comma_crt_axis_radix_def)
qed

lemma comma_crt_rebase_other_axis:
  assumes axis: "axis<4" and other: "other<4" and distinct: "axis\<noteq>other"
  shows "comma_crt_rebase axis slot phase mod comma_crt_axis_radix other=
    phase mod comma_crt_axis_radix other"
proof -
  let ?q = "comma_crt_axis_radix other"
  let ?correction = "(slot+comma_crt_axis_radix axis-
    phase mod comma_crt_axis_radix axis) mod comma_crt_axis_radix axis"
  have q_divides: "?q dvd 924"
    by (rule comma_crt_axis_radices_divide_924[OF other])
  have weight_zero:
    "comma_crt_axis_weight axis mod ?q=0"
    by (rule comma_crt_weight_other_residue[OF axis other distinct])
  have term_zero:
    "(comma_crt_axis_weight axis*?correction) mod ?q=0"
    using comma_crt_weighted_term[OF weight_zero] by simp
  have outer:
    "comma_crt_rebase axis slot phase mod ?q=
      (phase+comma_crt_axis_weight axis*?correction) mod ?q"
    unfolding comma_crt_rebase_def
    by (rule mod_mod_cancel[OF q_divides])
  have zero_shift:
    "(phase+comma_crt_axis_weight axis*?correction) mod ?q=
      (phase+0) mod ?q"
  proof (rule mod_add_cong)
    show "phase mod ?q=phase mod ?q" by simp
    show "(comma_crt_axis_weight axis*?correction) mod ?q=0 mod ?q"
      using term_zero by simp
  qed
  have "comma_crt_rebase axis slot phase mod ?q=
      (phase+comma_crt_axis_weight axis*?correction) mod ?q"
    by (rule outer)
  also have "...=(phase+0) mod ?q" by (rule zero_shift)
  also have "...=phase mod ?q" by simp
  finally show ?thesis .
qed

lemma comma_crt_rebase_selected_axis:
  assumes axis: "axis<4" and slot: "slot<comma_crt_axis_radix axis"
  shows "comma_crt_rebase axis slot phase mod comma_crt_axis_radix axis=slot"
proof -
  let ?q = "comma_crt_axis_radix axis"
  let ?correction = "(slot+?q-phase mod ?q) mod ?q"
  have q_positive: "0<?q"
    using comma_crt_axis_cases[OF axis]
    by (auto simp: comma_crt_axis_radix_def)
  have q_divides: "?q dvd 924"
    by (rule comma_crt_axis_radices_divide_924[OF axis])
  have weight_one: "comma_crt_axis_weight axis mod ?q=1"
    by (rule comma_crt_weight_own_residue[OF axis])
  have term_residue:
    "(comma_crt_axis_weight axis*?correction) mod ?q=?correction mod ?q"
    using comma_crt_weighted_term[OF weight_one] by simp
  have outer:
    "comma_crt_rebase axis slot phase mod ?q=
      (phase+comma_crt_axis_weight axis*?correction) mod ?q"
    unfolding comma_crt_rebase_def
    by (rule mod_mod_cancel[OF q_divides])
  have replacement: "(phase+?correction) mod ?q=slot"
    by (rule comma_crt_mod_replacement[OF q_positive slot])
  have weighted_sum:
    "(phase+comma_crt_axis_weight axis*?correction) mod ?q=
      (phase+?correction) mod ?q"
    by (rule mod_add_cong[OF refl term_residue])
  have "comma_crt_rebase axis slot phase mod ?q=
      (phase+comma_crt_axis_weight axis*?correction) mod ?q"
    by (rule outer)
  also have "...=(phase+?correction) mod ?q" by (rule weighted_sum)
  also have "...=slot" by (rule replacement)
  finally show ?thesis .
qed

lemma comma_crt_rebase_bounded:
  "comma_crt_rebase axis slot phase<924"
  by (simp add: comma_crt_rebase_def)

ML \<open>
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "External CRT selector clock and coordinate transport"
    @{thms comma_crt_clock_reconstruct comma_crt_clock_mod
      comma_crt_clock_axis_residue comma_crt_suffix_step
      comma_crt_suffix_zero_is_clock comma_crt_rebase_selected
      comma_crt_rebase_other_axis comma_crt_rebase_selected_axis
      comma_crt_rebase_bounded};
\<close>

end
