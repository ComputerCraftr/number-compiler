theory Reverse_Joint_Output_Inverse
  imports Main
begin

text \<open>Both output bits are emitted from the same ordered source pair.
The state consists of the ordinary and XOR addition carries.\<close>

definition reverse_joint_output_bits ::
    "bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<times> bool" where
  "reverse_joint_output_bits source reflected plus_carry xor_carry =
    ((source \<noteq> reflected) \<noteq> plus_carry, reflected \<noteq> xor_carry)"

definition reverse_joint_inverse_bits ::
    "bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<times> bool" where
  "reverse_joint_inverse_bits ordinary xor_bit plus_carry xor_carry =
    (((ordinary \<noteq> plus_carry) \<noteq> (xor_bit \<noteq> xor_carry)),
      xor_bit \<noteq> xor_carry)"

definition reverse_joint_carries ::
    "bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<times> bool" where
  "reverse_joint_carries source reflected plus_carry xor_carry =
    ((source \<and> reflected) \<or> ((source \<noteq> reflected) \<and> plus_carry),
      (source \<and> (source \<noteq> reflected)) \<or> (reflected \<and> xor_carry))"

definition reverse_joint_inverse_carries ::
    "bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<times> bool" where
  "reverse_joint_inverse_carries ordinary xor_bit plus_carry xor_carry =
    (let p = (ordinary \<noteq> plus_carry); reflected = (xor_bit \<noteq> xor_carry);
         source = (p \<noteq> reflected)
     in ((source \<and> reflected) \<or> (p \<and> plus_carry),
         (source \<and> p) \<or> (reflected \<and> xor_carry)))"

theorem reverse_joint_inverse_same_source:
  "case reverse_joint_output_bits source reflected plus_carry xor_carry of (ordinary, xor_bit) \<Rightarrow>
    reverse_joint_inverse_bits ordinary xor_bit plus_carry xor_carry = (source, reflected)"
  by (cases source; cases reflected; cases plus_carry; cases xor_carry;
      simp add: reverse_joint_output_bits_def reverse_joint_inverse_bits_def)

theorem reverse_joint_inverse_carry_step:
  "case reverse_joint_output_bits source reflected plus_carry xor_carry of (ordinary, xor_bit) \<Rightarrow>
    reverse_joint_inverse_carries ordinary xor_bit plus_carry xor_carry =
      reverse_joint_carries source reflected plus_carry xor_carry"
  by (cases source; cases reflected; cases plus_carry; cases xor_carry;
      simp add: reverse_joint_output_bits_def reverse_joint_carries_def
        reverse_joint_inverse_carries_def Let_def)

fun reverse_joint_encode_word ::
    "(bool \<times> bool) list \<Rightarrow> (bool \<times> bool) \<Rightarrow> (bool \<times> bool) list \<times> (bool \<times> bool)" where
  "reverse_joint_encode_word [] carry = ([], carry)"
| "reverse_joint_encode_word ((source,reflected) # rest) (plus_carry,xor_carry) =
    (let output = reverse_joint_output_bits source reflected plus_carry xor_carry;
         next = reverse_joint_carries source reflected plus_carry xor_carry;
         result = reverse_joint_encode_word rest next
     in (output # fst result, snd result))"

fun reverse_joint_decode_word ::
    "(bool \<times> bool) list \<Rightarrow> (bool \<times> bool) \<Rightarrow> (bool \<times> bool) list \<times> (bool \<times> bool)" where
  "reverse_joint_decode_word [] carry = ([], carry)"
| "reverse_joint_decode_word ((ordinary,xor_bit) # rest) (plus_carry,xor_carry) =
    (let input = reverse_joint_inverse_bits ordinary xor_bit plus_carry xor_carry;
         next = reverse_joint_inverse_carries ordinary xor_bit plus_carry xor_carry;
         result = reverse_joint_decode_word rest next
     in (input # fst result, snd result))"

theorem reverse_joint_word_same_source:
  "reverse_joint_decode_word (fst (reverse_joint_encode_word inputs carry)) carry =
    (inputs, snd (reverse_joint_encode_word inputs carry))"
proof (induction inputs arbitrary: carry)
  case Nil
  then show ?case by simp
next
  case (Cons input inputs)
  obtain source reflected where input: "input = (source, reflected)" by (cases input) auto
  obtain plus_carry xor_carry where carry: "carry = (plus_carry, xor_carry)" by (cases carry) auto
  show ?case unfolding input carry
    using Cons.IH
    by (cases source; cases reflected; cases plus_carry; cases xor_carry;
        simp add: Let_def reverse_joint_output_bits_def reverse_joint_inverse_bits_def
          reverse_joint_carries_def reverse_joint_inverse_carries_def)
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles @{thms reverse_joint_inverse_same_source
    reverse_joint_inverse_carry_step reverse_joint_word_same_source}) then ()
    else error "Reverse joint output inverse depends on an oracle";
\<close>

end
