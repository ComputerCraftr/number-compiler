theory Comma_Temporal_Port_Cover
  imports Comma_Even_Port_Action
begin

text \<open>The even-block quotient forgets four sheet distinctions.  The
admitted cover retains only that orientation and reconstructs the physical
port on demand.  It is the image of the 90 physical ports, not the full
Cartesian product of 86 keys and two bits.  No decade closure is asserted.\<close>

definition comma_temporal_port_encode :: "nat \<Rightarrow> nat \<Rightarrow> nat\<times>nat\<times>bool" where
  "comma_temporal_port_encode f d = (f,comma_even_port_digit f d,f\<le>d)"

definition comma_temporal_port_decode :: "nat\<times>nat\<times>bool \<Rightarrow> nat\<times>nat" where
  "comma_temporal_port_decode X = (case X of (f,k,sheet) \<Rightarrow>
    (f,if f=5 \<and> 1\<le>k \<and> k\<le>4 then k+(if sheet then 5 else 0) else k))"

definition comma_temporal_port_admitted :: "nat\<times>nat\<times>bool \<Rightarrow> bool" where
  "comma_temporal_port_admitted X =
    (\<exists>f d. 1\<le>f \<and> f\<le>9 \<and> d\<le>9 \<and> X=comma_temporal_port_encode f d)"

lemma comma_temporal_port_roundtrip:
  assumes "d\<le>9"
  shows "comma_temporal_port_decode (comma_temporal_port_encode f d)=(f,d)"
  using assms
  by (auto simp: comma_temporal_port_decode_def comma_temporal_port_encode_def
    comma_even_port_digit_def split: if_splits; arith)

lemma comma_temporal_port_injective:
  assumes "d\<le>9" "e\<le>9"
    "comma_temporal_port_encode f d=comma_temporal_port_encode g e"
  shows "f=g \<and> d=e"
proof -
  have "comma_temporal_port_decode (comma_temporal_port_encode f d)=
    comma_temporal_port_decode (comma_temporal_port_encode g e)"
    by (rule arg_cong[OF assms(3)])
  then show ?thesis
    by (simp only: comma_temporal_port_roundtrip[OF assms(1)]
      comma_temporal_port_roundtrip[OF assms(2)] prod.inject)
qed

lemma comma_temporal_port_admitted_roundtrip:
  assumes "comma_temporal_port_admitted X"
  shows "case comma_temporal_port_decode X of (f,d) \<Rightarrow>
    1\<le>f \<and> f\<le>9 \<and> d\<le>9 \<and> comma_temporal_port_encode f d=X"
  using assms by (auto simp: comma_temporal_port_admitted_def comma_temporal_port_roundtrip)

lemma comma_temporal_port_card:
  "card {X. comma_temporal_port_admitted X}=90"
proof -
  let ?ports = "{1..9 :: nat} \<times> {0..9 :: nat}"
  let ?encode = "\<lambda>(f,d). comma_temporal_port_encode f d"
  have injective: "inj_on ?encode ?ports"
    using comma_temporal_port_injective
    by (auto simp: inj_on_def)
  have image: "{X. comma_temporal_port_admitted X}=?encode ` ?ports"
    by (force simp: comma_temporal_port_admitted_def image_iff)
  have "card (?encode ` ?ports)=card ?ports"
    by (rule card_image[OF injective])
  also have "...=90" by (simp add: card_cartesian_product)
  finally have size: "card (?encode ` ?ports)=90" .
  show ?thesis by (simp only: image size)
qed

lemma comma_temporal_doubleton_flip:
  assumes "1\<le>d" "d\<le>4"
  shows "comma_temporal_port_encode 5 (comma_port_next 5 d)=(5,d,True)"
    "comma_temporal_port_encode 5 (comma_port_next 5 (d+5))=(5,d,False)"
  using assms comma_sector_five_pair(1,2)[OF assms]
  by (simp_all add: comma_temporal_port_encode_def comma_even_port_digit_def)

lemma comma_temporal_doubleton_no_external_predecessor:
  assumes "d\<le>9"
    and target: "1\<le>comma_even_port_digit 5 (comma_port_next 5 d)"
      "comma_even_port_digit 5 (comma_port_next 5 d)\<le>4"
  shows "1\<le>comma_even_port_digit 5 d \<and> comma_even_port_digit 5 d\<le>4"
proof -
  have not_zero: "d\<noteq>0"
    using target by (intro notI; simp_all add: comma_even_port_digit_def comma_port_next_def
      comma_port_previous_def Let_def)
  have not_five: "d\<noteq>5"
    using target by (intro notI; simp_all add: comma_even_port_digit_def comma_port_next_def
      comma_port_previous_def Let_def)
  show ?thesis using assms(1) not_zero not_five
    by (auto simp: comma_even_port_digit_def; arith)
qed

lemma comma_temporal_even_sheet_preserved:
  assumes "1\<le>d" "d\<le>4"
  shows "comma_temporal_port_encode 5 (fst (comma_port_action_power 5 (2*n) (d,w)))=
      comma_temporal_port_encode 5 d"
    "comma_temporal_port_encode 5 (fst (comma_port_action_power 5 (2*n) (d+5,w)))=
      comma_temporal_port_encode 5 (d+5)"
  by (simp_all only: comma_sector_five_even_actions[OF assms] fst_conv)

text \<open>The decoder recovers exact intermediate observations from the
transported cover.  Equality of a reduced complete-even response alone is
not an authorization to erase its source sheet.\<close>

lemma comma_temporal_port_dwell_reconstruction:
  assumes "d\<le>9"
  shows "(case comma_temporal_port_decode (comma_temporal_port_encode f d)
      of (g,e) \<Rightarrow> comma_port_dwell g e)=comma_port_dwell f d"
  by (simp only: comma_temporal_port_roundtrip[OF assms] case_prod_conv)

text \<open>The centered pair coordinate is a derived view of the same
cover.  These signed numerators reconstruct both digits without retaining
an endpoint or predecessor field.\<close>

lemma comma_temporal_centered_numerators:
  assumes "1\<le>f" "f\<le>9" "d\<le>9"
  defines "delta \<equiv> int d+int (comma_port_previous f d)-9"
  shows "delta+int f-1+(if f\<le>d then 10 else 0)=2*int d"
    "delta+19-int f-(if f\<le>d then 10 else 0)=2*int (comma_port_previous f d)"
  using assms(1-3)
  by (auto simp: delta_def comma_pair_previous_split[OF assms(1-3)]
    of_nat_diff split: if_splits; arith)+

lemma comma_temporal_centered_decode:
  assumes "1\<le>f" "f\<le>9" "d\<le>9"
  defines "delta \<equiv> int d+int (comma_port_previous f d)-9"
  shows "nat ((delta+int f-1+(if f\<le>d then 10 else 0)) div 2)=d"
    "nat ((delta+19-int f-(if f\<le>d then 10 else 0)) div 2)=comma_port_previous f d"
  using comma_temporal_centered_numerators[OF assms(1-3)]
  by (simp_all add: delta_def)

ML \<open>
  val checked = @{thms comma_temporal_port_roundtrip comma_temporal_port_injective
    comma_temporal_port_admitted_roundtrip comma_temporal_port_card
    comma_temporal_doubleton_flip comma_temporal_doubleton_no_external_predecessor
    comma_temporal_even_sheet_preserved comma_temporal_port_dwell_reconstruction
    comma_temporal_centered_numerators comma_temporal_centered_decode};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Temporal port cover depends on an oracle";
\<close>
end
