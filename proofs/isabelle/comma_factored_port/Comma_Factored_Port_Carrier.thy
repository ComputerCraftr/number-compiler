theory Comma_Factored_Port_Carrier
  imports Comma_Vieta_Root.Comma_Pair_Field
    Comma_Native19_Carry.Comma_Native19_Carry
begin

text \<open>The shared decimal domain/F5/parity carrier plus one orientation
bit reconstructs every zero-inclusive physical port. Neither the predecessor
nor the second pair coordinate is retained. This local bijection does not
supply a future-decade classifier or justify erasing weighted outputs.\<close>

record comma_port_carrier =
  carrier_sector :: nat
  carrier_sum :: native_cocycle
  carrier_orientation :: bool

definition comma_port_carrier_encode :: "nat \<Rightarrow> nat \<Rightarrow> comma_port_carrier" where
  "comma_port_carrier_encode f d =
    \<lparr>carrier_sector=f,
      carrier_sum=encode_cocycle (d+comma_port_previous f d),
      carrier_orientation=(f\<le>d)\<rparr>"

definition comma_port_carrier_difference :: "comma_port_carrier \<Rightarrow> nat" where
  "comma_port_carrier_difference X =
    carrier_sector X-1+(if carrier_orientation X then 10 else 0)"

definition comma_port_carrier_pair :: "comma_port_carrier \<Rightarrow> comma_pair_field" where
  "comma_port_carrier_pair X =
    Comma_Pair_Field (comma_native19_decode (carrier_sum X))
      (comma_port_carrier_difference X)"

definition comma_port_carrier_decode :: "comma_port_carrier \<Rightarrow> nat\<times>nat" where
  "comma_port_carrier_decode X =
    (carrier_sector X,comma_pair_left_digit (comma_port_carrier_pair X))"

lemma comma_port_carrier_pair_difference:
  assumes "1\<le>f" "f\<le>9" "d\<le>9"
  shows "comma_port_carrier_difference (comma_port_carrier_encode f d)=
    comma_pair_difference (comma_pair_encode f d)"
  using comma_pair_difference_factored[OF assms]
  by (auto simp: comma_port_carrier_difference_def comma_port_carrier_encode_def)

lemma comma_port_carrier_pair_refines:
  assumes "1\<le>f" "f\<le>9" "d\<le>9"
  shows "comma_port_carrier_pair (comma_port_carrier_encode f d)=comma_pair_encode f d"
proof -
  have bound: "d+comma_port_previous f d\<le>18"
    using comma_pair_encoded_arithmetic(8)[OF assms] assms(3) by arith
  have decode: "comma_native19_decode (encode_cocycle (d+comma_port_previous f d))=
      d+comma_port_previous f d"
    by (rule comma_native19_decode_encode[OF bound])
  have difference: "comma_port_carrier_difference (comma_port_carrier_encode f d)=
      d+9-comma_port_previous f d"
    using comma_port_carrier_pair_difference[OF assms]
      comma_pair_encoded_arithmetic(2)[OF assms] by simp
  have sum: "carrier_sum (comma_port_carrier_encode f d)=
      encode_cocycle (d+comma_port_previous f d)"
    by (simp add: comma_port_carrier_encode_def)
  show ?thesis
    unfolding comma_port_carrier_pair_def
    by (simp only: sum decode difference comma_pair_encode_def Let_def)
qed

lemma comma_port_carrier_roundtrip:
  assumes "1\<le>f" "f\<le>9" "d\<le>9"
  shows "comma_port_carrier_decode (comma_port_carrier_encode f d)=(f,d)"
  using comma_port_carrier_pair_refines[OF assms]
    comma_pair_encoded_arithmetic(6)[OF assms]
  by (simp add: comma_port_carrier_decode_def comma_port_carrier_encode_def)

lemma comma_port_carrier_injective:
  assumes "1\<le>f" "f\<le>9" "d\<le>9"
    "1\<le>g" "g\<le>9" "e\<le>9"
    "comma_port_carrier_encode f d=comma_port_carrier_encode g e"
  shows "f=g \<and> d=e"
proof -
  have "comma_port_carrier_decode (comma_port_carrier_encode f d)=
      comma_port_carrier_decode (comma_port_carrier_encode g e)"
    by (rule arg_cong[OF assms(7)])
  then show ?thesis
    by (simp only: comma_port_carrier_roundtrip[OF assms(1-3)]
      comma_port_carrier_roundtrip[OF assms(4-6)] prod.inject)
qed

definition comma_port_carrier_center :: "comma_port_carrier \<Rightarrow> nat" where
  "comma_port_carrier_center X=comma_native19_decode (carrier_sum X) div 2 mod 5"

lemma comma_port_carrier_center_refines:
  assumes "1\<le>f" "f\<le>9" "d\<le>9"
  shows "comma_port_carrier_center (comma_port_carrier_encode f d)=comma_pair_center f d"
proof -
  have bound: "d+comma_port_previous f d\<le>18"
    using comma_pair_encoded_arithmetic(8)[OF assms] assms(3) by arith
  show ?thesis
    by (simp add: comma_port_carrier_center_def comma_port_carrier_encode_def
      comma_native19_decode_encode[OF bound] comma_pair_center_def)
qed

lemma comma_port_carrier_previous_zero:
  assumes "1\<le>f" "f\<le>9" "d\<le>9"
  shows "(comma_pair_right_digit (comma_port_carrier_pair (comma_port_carrier_encode f d))=0)
    = (d=f)"
  using comma_port_carrier_pair_refines[OF assms]
    comma_pair_encoded_arithmetic(7,9)[OF assms] by simp

lemma comma_port_carrier_center_step:
  assumes "1\<le>f" "f\<le>9" "d\<le>9"
  shows "comma_pair_center f (comma_port_next f d)=
    (if comma_pair_right_digit (comma_port_carrier_pair (comma_port_carrier_encode f d))=0
      then (comma_port_carrier_center (comma_port_carrier_encode f d)+20-2*f) mod 5
      else (comma_port_carrier_center (comma_port_carrier_encode f d)+10-f) mod 5)"
  using comma_pair_center_next[OF assms]
    comma_port_carrier_pair_refines[OF assms]
    comma_pair_encoded_arithmetic(7)[OF assms]
    comma_port_carrier_center_refines[OF assms] by simp

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_port_carrier_pair_refines comma_port_carrier_roundtrip
      comma_port_carrier_injective comma_port_carrier_pair_difference
      comma_port_carrier_previous_zero comma_port_carrier_center_step})
    then () else error "Comma factored port depends on an oracle";
\<close>
end
