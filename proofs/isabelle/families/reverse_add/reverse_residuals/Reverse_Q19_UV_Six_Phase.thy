theory Reverse_Q19_UV_Six_Phase
  imports Reverse_Q19_UV_Piece
begin

text \<open>The central run and the two physical fringes carry separate
ordered receipts.  A one-column reset core can be repeated without opening
its copies, while the head, tail and moving center retain their exact ports.\<close>

lemma uv_piece_repeat:
  assumes one: "uv_piece grows p [s] p [t]"
  shows "uv_piece grows p (replicate n s) p (replicate n t)"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  from uv_piece_join[OF one Suc.IH] show ?case by simp
qed

lemma uv_piece_quiet_even_general:
  assumes cert: "uv_piece False (False,False,z) w (c,c,z) y"
  shows "step (w @ rev w) = y @ rev y"
proof -
  let ?H = "rev (emit c (rev w))"
  have lo: "carry_out False w = c"
    and hi: "\<not> carry_out c (rev w)"
    and out_eq: "y = map (\<lambda>(a,b). a+b) (zip (emit False w) ?H)"
    using uv_piece_whole[OF cert] by simp_all
  have quiet: "\<not> carry_out False (w @ rev w)"
    using lo hi by (simp add: carry_out_append)
  have low: "take (length w) (step (w @ rev w)) = y"
    using hinge_physical_list_half[of w "[]"]
      hinge_emit_general[of w c] lo hi out_eq
    by (simp add: carry_out_def)
  have width: "length (step (w @ rev w)) = 2 * length w"
    using quiet by (simp add: length_digits_exact)
  show ?thesis
    by (rule q19_symmetric_even_reconstruction[OF step_symmetric width low])
qed

lemma uv_piece_birth_even_general:
  assumes cert: "uv_piece True (False,True,1) w (c,c,z) y"
    and nonempty: "w \<noteq> []"
  shows "step (w @ rev w) = y @ [2*z] @ rev y"
proof -
  let ?H = "rev (emit c (rev w))"
  have lo: "carry_out False w = c"
    and hi: "carry_out c (rev w)"
    and out_eq: "y=map (\<lambda>(a,b).a+b) (zip (emit False w)
      (take (length w) (1#?H)))"
    and last: "last ?H=z"
    using uv_piece_whole[OF cert] nonempty by simp_all
  have birth: "carry_out False (w @ rev w)" using lo hi by (simp add: carry_out_append)
  have h: "?H=rev (emit (carry_out False w) (rev w))" using lo by simp
  from q19_half_birth_even(4)[OF nonempty birth refl h out_eq] last show ?thesis by simp
qed

lemma uv_piece_quiet_odd_general:
  assumes cert: "uv_piece False (False,False,z) w (c,carry_apply (domain m) c,z) y"
  shows "step (w @ [m] @ rev w) =
    y @ [2 * ((m + carry_bit c) mod 10)] @ rev y"
proof -
  let ?H = "rev (emit (carry_apply (domain m) c) (rev w))"
  have lo: "carry_out False w = c"
    and hi: "\<not> carry_out (carry_apply (domain m) c) (rev w)"
    and out_eq: "y=map (\<lambda>(a,b).a+b) (zip (emit False w) ?H)"
    using uv_piece_whole[OF cert] by simp_all
  have quiet: "\<not> carry_out False (w @ [m] @ rev w)"
    using lo hi by (simp add: carry_out_append carry_out_def)
  have c: "c=carry_out False w" using lo by simp
  have h: "?H=rev (emit (carry_apply (domain m) c) (rev w))" by simp
  from q19_half_quiet_odd(4)[OF quiet c refl refl h out_eq] show ?thesis
    by (simp add: carry_bit_def)
qed

lemma uv_piece_birth_odd_general:
  assumes cert: "uv_piece True (False,True,1) w (c,carry_apply (domain m) c,z) y"
    and nonempty: "w \<noteq> []"
  shows "step (w @ [m] @ rev w) =
    (y @ [(m + carry_bit c) mod 10 + z]) @ rev (y @ [(m + carry_bit c) mod 10 + z])"
proof -
  let ?H = "rev (emit (carry_apply (domain m) c) (rev w))"
  have lo: "carry_out False w = c"
    and hi: "carry_out (carry_apply (domain m) c) (rev w)"
    and out_eq: "y=map (\<lambda>(a,b).a+b) (zip (emit False w)
      (take (length w) (1#?H)))"
    and last: "last ?H=z"
    using uv_piece_whole[OF cert] nonempty by simp_all
  have birth: "carry_out False (w @ [m] @ rev w)"
    using lo hi by (simp add: carry_out_append carry_out_def)
  have c: "c=carry_out False w" using lo by simp
  have h: "?H=rev (emit (carry_apply (domain m) c) (rev w))" by simp
  from q19_half_birth_odd(4)[OF nonempty birth c refl refl h out_eq] last show ?thesis
    by (simp add: carry_bit_def)
qed


definition uv_protected_head3 :: "nat list" where
  "uv_protected_head3 = [8,7,11,2,2,2,2,2,2,2,2,2]"

definition uv_protected_tail3 :: "nat list" where
  "uv_protected_tail3 = [2,2,2,2,2,2,2,3,10]"

definition uv_protected_head4 :: "nat list" where
  "uv_protected_head4 = [16,15,2,5,4,4,4,4,4,4,4,4]"

definition uv_protected_tail4 :: "nat list" where
  "uv_protected_tail4 = [4,4,4,4,4,4,4,7,1]"

definition uv_protected_head5 :: "nat list" where
  "uv_protected_head5 = [7,13,8,7,9,8,8,8,8,8,8,8]"

definition uv_protected_tail5 :: "nat list" where
  "uv_protected_tail5 = [8,8,8,8,8,8,8,11,8]"

definition uv_protected_head6 :: "nat list" where
  "uv_protected_head6 = [15,6,17,14,18,16,16,16,16,16,16,16]"

definition uv_protected_tail6 :: "nat list" where
  "uv_protected_tail6 = [16,16,16,16,16,16,17,2,17]"

definition uv_protected_head7 :: "nat list" where
  "uv_protected_head7 = [6,12,14,13,14,16,14,14,14,14,14,14]"

definition uv_protected_tail7 :: "nat list" where
  "uv_protected_tail7 = [14,14,14,14,14,14,15,10,10,12]"

definition uv_protected_head8 :: "nat list" where
  "uv_protected_head8 = [13,5,10,8,10,14,10,10,10,10,10,10]"

definition uv_protected_tail8 :: "nat list" where
  "uv_protected_tail8 = [10,10,10,10,10,10,12,2,2,6]"

definition uv_protected_head9 :: "nat list" where
  "uv_protected_head9 = [4,9,6,9,9,6,6,2,2,2,2,2]"

definition uv_protected_tail9 :: "nat list" where
  "uv_protected_tail9 = [2,2,2,2,2,2,4,5,4,8]"

lemma uv_protected_receipt3:
  "uv_piece False (False,False,0) uv_protected_head3 (False,False,0) uv_protected_head4"
  "uv_piece False (False,False,0) [2] (False,False,0) [4]"
  "uv_piece False (False,False,0) uv_protected_tail3 (True,True,0) uv_protected_tail4"
  by (simp_all add: uv_piece_def uv_protected_head3_def uv_protected_head4_def
      uv_protected_tail3_def uv_protected_tail4_def uv_after_def carry_out_def domain_def Let_def)

lemma uv_protected_receipt4:
  "uv_piece True (False,True,1) uv_protected_head4 (False,False,4) uv_protected_head5"
  "uv_piece True (False,False,4) [4] (False,False,4) [8]"
  "uv_piece True (False,False,4) uv_protected_tail4 (False,False,1) uv_protected_tail5"
  by (simp_all add: uv_piece_def uv_protected_head4_def uv_protected_head5_def
      uv_protected_tail4_def uv_protected_tail5_def uv_after_def carry_out_def domain_def Let_def)

lemma uv_protected_receipt5:
  "uv_piece False (False,False,0) uv_protected_head5 (False,False,0) uv_protected_head6"
  "uv_piece False (False,False,0) [8] (False,False,0) [16]"
  "uv_piece False (False,False,0) uv_protected_tail5 (False,False,0) uv_protected_tail6"
  by (simp_all add: uv_piece_def uv_protected_head5_def uv_protected_head6_def
      uv_protected_tail5_def uv_protected_tail6_def uv_after_def carry_out_def domain_def Let_def)

lemma uv_protected_receipt6:
  "uv_piece True (False,True,1) uv_protected_head6 (True,True,7) uv_protected_head7"
  "uv_piece True (True,True,7) [16] (True,True,7) [14]"
  "uv_piece True (True,True,7) uv_protected_tail6 (True,False,7) (butlast uv_protected_tail7)"
  by (simp_all add: uv_piece_def uv_protected_head6_def uv_protected_head7_def
      uv_protected_tail6_def uv_protected_tail7_def uv_after_def carry_out_def domain_def Let_def)

lemma uv_protected_receipt7:
  "uv_piece False (False,False,0) uv_protected_head7 (True,True,0) uv_protected_head8"
  "uv_piece False (True,True,0) [14] (True,True,0) [10]"
  "uv_piece False (True,True,0) uv_protected_tail7 (True,True,0) uv_protected_tail8"
  by (simp_all add: uv_piece_def uv_protected_head7_def uv_protected_head8_def
      uv_protected_tail7_def uv_protected_tail8_def uv_after_def carry_out_def domain_def Let_def)

lemma uv_protected_receipt8:
  "uv_piece True (False,True,1) uv_protected_head8 (True,True,1) uv_protected_head9"
  "uv_piece True (True,True,1) [10] (True,True,1) [2]"
  "uv_piece True (True,True,1) uv_protected_tail8 (False,False,6) uv_protected_tail9"
  by (simp_all add: uv_piece_def uv_protected_head8_def uv_protected_head9_def
      uv_protected_tail8_def uv_protected_tail9_def uv_after_def carry_out_def domain_def Let_def)

definition uv_protected_half :: "nat \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat list" where
  "uv_protected_half k head cell tail = head @ replicate k cell @ tail"

lemma uv_protected_word_receipt3:
  "uv_piece False (False,False,0)
    (uv_protected_half k uv_protected_head3 2 uv_protected_tail3)
    (True,True,0) (uv_protected_half k uv_protected_head4 4 uv_protected_tail4)"
  unfolding uv_protected_half_def
  using uv_piece_join[OF uv_protected_receipt3(1)
    uv_piece_join[OF uv_piece_repeat[OF uv_protected_receipt3(2), of k]
      uv_protected_receipt3(3)]] by simp

lemma uv_protected_word_receipt4:
  "uv_piece True (False,True,1)
    (uv_protected_half k uv_protected_head4 4 uv_protected_tail4)
    (False,False,1) (uv_protected_half k uv_protected_head5 8 uv_protected_tail5)"
  unfolding uv_protected_half_def
  using uv_piece_join[OF uv_protected_receipt4(1)
    uv_piece_join[OF uv_piece_repeat[OF uv_protected_receipt4(2), of k]
      uv_protected_receipt4(3)]] by simp

lemma uv_protected_word_receipt5:
  "uv_piece False (False,False,0)
    (uv_protected_half k uv_protected_head5 8 uv_protected_tail5)
    (False,False,0) (uv_protected_half k uv_protected_head6 16 uv_protected_tail6)"
  unfolding uv_protected_half_def
  using uv_piece_join[OF uv_protected_receipt5(1)
    uv_piece_join[OF uv_piece_repeat[OF uv_protected_receipt5(2), of k]
      uv_protected_receipt5(3)]] by simp

lemma uv_protected_word_receipt6:
  "uv_piece True (False,True,1)
    (uv_protected_half k uv_protected_head6 16 uv_protected_tail6)
    (True,False,7) (uv_protected_head7 @ replicate k 14 @ butlast uv_protected_tail7)"
  unfolding uv_protected_half_def
  using uv_piece_join[OF uv_protected_receipt6(1)
    uv_piece_join[OF uv_piece_repeat[OF uv_protected_receipt6(2), of k]
      uv_protected_receipt6(3)]] by simp

lemma uv_protected_word_receipt7:
  "uv_piece False (False,False,0)
    (uv_protected_half k uv_protected_head7 14 uv_protected_tail7)
    (True,True,0) (uv_protected_half k uv_protected_head8 10 uv_protected_tail8)"
  unfolding uv_protected_half_def
  using uv_piece_join[OF uv_protected_receipt7(1)
    uv_piece_join[OF uv_piece_repeat[OF uv_protected_receipt7(2), of k]
      uv_protected_receipt7(3)]] by simp

lemma uv_protected_word_receipt8:
  "uv_piece True (False,True,1)
    (uv_protected_half k uv_protected_head8 10 uv_protected_tail8)
    (False,False,6) (uv_protected_half k uv_protected_head9 2 uv_protected_tail9)"
  unfolding uv_protected_half_def
  using uv_piece_join[OF uv_protected_receipt8(1)
    uv_piece_join[OF uv_piece_repeat[OF uv_protected_receipt8(2), of k]
      uv_protected_receipt8(3)]] by simp


definition uv_protected_field :: "nat list \<Rightarrow> nat list \<Rightarrow> nat list" where
  "uv_protected_field half center = half @ center @ rev half"

lemma uv_protected_steps:
  "step (uv_protected_field (uv_protected_half k uv_protected_head3 2 uv_protected_tail3) []) =
    uv_protected_field (uv_protected_half k uv_protected_head4 4 uv_protected_tail4) []"
  "step (uv_protected_field (uv_protected_half k uv_protected_head4 4 uv_protected_tail4) []) =
    uv_protected_field (uv_protected_half k uv_protected_head5 8 uv_protected_tail5) [2]"
  "step (uv_protected_field (uv_protected_half k uv_protected_head5 8 uv_protected_tail5) [2]) =
    uv_protected_field (uv_protected_half k uv_protected_head6 16 uv_protected_tail6) [4]"
  "step (uv_protected_field (uv_protected_half k uv_protected_head6 16 uv_protected_tail6) [4]) =
    uv_protected_field (uv_protected_half k uv_protected_head7 14 uv_protected_tail7) []"
  "step (uv_protected_field (uv_protected_half k uv_protected_head7 14 uv_protected_tail7) []) =
    uv_protected_field (uv_protected_half k uv_protected_head8 10 uv_protected_tail8) []"
  "step (uv_protected_field (uv_protected_half k uv_protected_head8 10 uv_protected_tail8) []) =
    uv_protected_field (uv_protected_half k uv_protected_head9 2 uv_protected_tail9) [12]"
proof -
  show "step (uv_protected_field (uv_protected_half k uv_protected_head3 2 uv_protected_tail3) []) =
    uv_protected_field (uv_protected_half k uv_protected_head4 4 uv_protected_tail4) []"
    using uv_piece_quiet_even_general[OF uv_protected_word_receipt3]
    by (simp add: uv_protected_field_def)
  have nonempty4: "uv_protected_half k uv_protected_head4 4 uv_protected_tail4 \<noteq> []"
    by (simp add: uv_protected_half_def uv_protected_head4_def)
  show "step (uv_protected_field (uv_protected_half k uv_protected_head4 4 uv_protected_tail4) []) =
    uv_protected_field (uv_protected_half k uv_protected_head5 8 uv_protected_tail5) [2]"
    using uv_piece_birth_even_general[OF uv_protected_word_receipt4 nonempty4]
    by (simp add: uv_protected_field_def)
  have cert5: "uv_piece False (False,False,0)
    (uv_protected_half k uv_protected_head5 8 uv_protected_tail5)
    (False,carry_apply (domain 2) False,0)
    (uv_protected_half k uv_protected_head6 16 uv_protected_tail6)"
    using uv_protected_word_receipt5 by (simp add: domain_def)
  show "step (uv_protected_field (uv_protected_half k uv_protected_head5 8 uv_protected_tail5) [2]) =
    uv_protected_field (uv_protected_half k uv_protected_head6 16 uv_protected_tail6) [4]"
    using uv_piece_quiet_odd_general[OF cert5]
    by (simp add: uv_protected_field_def carry_bit_def)
  have nonempty6: "uv_protected_half k uv_protected_head6 16 uv_protected_tail6 \<noteq> []"
    by (simp add: uv_protected_half_def uv_protected_head6_def)
  have cert6: "uv_piece True (False,True,1)
    (uv_protected_half k uv_protected_head6 16 uv_protected_tail6)
    (True,carry_apply (domain 4) True,7)
    (uv_protected_head7 @ replicate k 14 @ butlast uv_protected_tail7)"
    using uv_protected_word_receipt6 by (simp add: domain_def)
  show "step (uv_protected_field (uv_protected_half k uv_protected_head6 16 uv_protected_tail6) [4]) =
    uv_protected_field (uv_protected_half k uv_protected_head7 14 uv_protected_tail7) []"
    using uv_piece_birth_odd_general[OF cert6 nonempty6]
    by (simp add: uv_protected_field_def uv_protected_half_def uv_protected_tail7_def
        carry_bit_def append_assoc)
  show "step (uv_protected_field (uv_protected_half k uv_protected_head7 14 uv_protected_tail7) []) =
    uv_protected_field (uv_protected_half k uv_protected_head8 10 uv_protected_tail8) []"
    using uv_piece_quiet_even_general[OF uv_protected_word_receipt7]
    by (simp add: uv_protected_field_def)
  have nonempty8: "uv_protected_half k uv_protected_head8 10 uv_protected_tail8 \<noteq> []"
    by (simp add: uv_protected_half_def uv_protected_head8_def)
  show "step (uv_protected_field (uv_protected_half k uv_protected_head8 10 uv_protected_tail8) []) =
    uv_protected_field (uv_protected_half k uv_protected_head9 2 uv_protected_tail9) [12]"
    using uv_piece_birth_even_general[OF uv_protected_word_receipt8 nonempty8]
    by (simp add: uv_protected_field_def)
qed

theorem uv_protected_six_physical_ticks:
  "run step 6 (uv_protected_field (uv_protected_half k uv_protected_head3 2 uv_protected_tail3) []) =
    uv_protected_field (uv_protected_half k uv_protected_head9 2 uv_protected_tail9) [12]"
proof -
  have six: "(6::nat) = Suc (Suc (Suc (Suc (Suc (Suc 0)))))" by simp
  show ?thesis by (simp only: six run.simps uv_protected_steps)
qed

ML \<open>
  val checked = @{thms uv_protected_six_physical_ticks};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "U/V protected action depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked then
    error "U/V protected action has skipped proofs" else ();
\<close>

end
