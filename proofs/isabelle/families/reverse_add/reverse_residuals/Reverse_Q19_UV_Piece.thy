theory Reverse_Q19_UV_Piece
  imports Reverse_Q19_Half_Field_Step
begin

fun uv_lag :: "nat \<Rightarrow> nat list \<Rightarrow> nat list" where
  "uv_lag z [] = []"
| "uv_lag z (x#xs) = z # uv_lag x xs"

definition uv_after :: "nat \<Rightarrow> nat list \<Rightarrow> nat" where
  "uv_after z xs = (if xs=[] then z else last xs)"

lemma uv_lag_length [simp]: "length (uv_lag z xs) = length xs"
  by (induction xs arbitrary: z) auto

lemma uv_lag_take: "uv_lag z xs = take (length xs) (z#xs)"
  by (induction xs arbitrary: z) auto

lemma uv_lag_concat: "uv_lag z (a@b) = uv_lag z a @ uv_lag (uv_after z a) b"
  by (induction a arbitrary: z) (simp_all add: uv_after_def)

lemma uv_after_concat: "uv_after z (a@b) = uv_after (uv_after z a) b"
  by (simp add: uv_after_def)

type_synonym uv_port = "bool \<times> bool \<times> nat"

definition uv_piece :: "bool \<Rightarrow> uv_port \<Rightarrow> nat list \<Rightarrow> uv_port \<Rightarrow> nat list \<Rightarrow> bool" where
  "uv_piece grow from w to out \<longleftrightarrow>
    (case (from,to) of ((l,h,z),(l',h',z')) \<Rightarrow>
      let L=emit l w; H=rev (emit h' (rev w))
      in carry_out l w=l' \<and> carry_out h' (rev w)=h \<and>
         z'=(if grow then uv_after z H else z) \<and>
         out=map (\<lambda>(a,b). a+b) (zip L (if grow then uv_lag z H else H)))"

lemma uv_piece_empty [simp]: "uv_piece grow port [] port []"
  by (cases port; cases "snd port"; simp add: uv_piece_def carry_out_def uv_after_def)

lemma uv_piece_join:
  assumes left: "uv_piece grow p w q a" and right: "uv_piece grow q v r b"
  shows "uv_piece grow p (w@v) r (a@b)"
proof -
  obtain l h z where P: "p=(l,h,z)" by (cases p; auto)
  obtain l' h' z' where Q: "q=(l',h',z')" by (cases q; auto)
  obtain l'' h'' z'' where R: "r=(l'',h'',z'')" by (cases r; auto)
  show ?thesis
    using left right
    by (cases grow; simp add: uv_piece_def P Q R Let_def emit_append
       carry_out_append uv_lag_concat uv_after_concat rev_append zip_append)
qed

lemma uv_piece_whole:
  assumes "uv_piece grow (l,h,z) w (l',h',z') out"
  defines "H \<equiv> rev (emit h' (rev w))"
  shows "carry_out l w=l'" "carry_out h' (rev w)=h"
    "out=map (\<lambda>(a,b). a+b) (zip (emit l w) (if grow then take (length w) (z#H) else H))"
    "grow \<Longrightarrow> w\<noteq>[] \<Longrightarrow> z'=last H"
  using assms by (simp_all add: uv_piece_def Let_def uv_lag_take uv_after_def)

theorem uv_piece_birth_even:
  assumes cert: "uv_piece True (False,True,1) w (True,True,2) y" and w: "w\<noteq>[]"
  shows "step (w@rev w) = y@[4]@rev y"
proof -
  let ?H = "rev (emit True (rev w))"
  have lo: "carry_out False w" and hi: "carry_out True (rev w)"
    and y: "y=map (\<lambda>(a,b). a+b) (zip (emit False w) (take (length w) (1#?H)))"
    and last: "last ?H=2"
    using uv_piece_whole[OF cert] w by simp_all
  have B: "carry_out False (w@rev w)" using lo hi by (simp add: carry_out_append)
  have h: "?H=rev (emit (carry_out False w) (rev w))" using lo by simp
  from q19_half_birth_even(4)[OF w B refl h y] last show ?thesis by simp
qed

theorem uv_piece_quiet_odd:
  assumes cert: "uv_piece False (False,False,0) w (False,False,0) y"
  shows "step (w@[4]@rev w) = y@[8]@rev y"
proof -
  have lo: "\<not>carry_out False w" and hi: "\<not>carry_out False (rev w)"
    and y: "y=map (\<lambda>(a,b). a+b) (zip (emit False w) (rev (emit False (rev w))))"
    using uv_piece_whole[OF cert] by simp_all
  have Q: "\<not>carry_out False (w@[4]@rev w)"
    using lo hi by (simp only: append_Cons append_Nil carry_out_append reverse_native_carry_out_cons; simp add: domain_def)
  have c: "False=carry_out False w" using lo by simp
  have h: "rev (emit False (rev w))=rev (emit (carry_apply (domain 4) False) (rev w))"
    by (simp add: domain_def)
  from q19_half_quiet_odd(4)[OF Q c refl refl h y] show ?thesis by simp
qed

theorem uv_piece_birth_odd:
  assumes cert: "uv_piece True (False,True,1) w (True,False,1) y" and w: "w\<noteq>[]"
  shows "step (w@[8]@rev w) = (y@[10])@rev (y@[10])"
proof -
  let ?H = "rev (emit False (rev w))"
  have lo: "carry_out False w" and hi: "carry_out False (rev w)"
    and y: "y=map (\<lambda>(a,b). a+b) (zip (emit False w) (take (length w) (1#?H)))"
    and last: "last ?H=1"
    using uv_piece_whole[OF cert] w by simp_all
  have B: "carry_out False (w@[8]@rev w)"
    using lo hi by (simp only: append_Cons append_Nil carry_out_append reverse_native_carry_out_cons; simp add: domain_def)
  have c: "True=carry_out False w" using lo by simp
  have h: "?H=rev (emit (carry_apply (domain 8) True) (rev w))" by (simp add: domain_def)
  from q19_half_birth_odd(4)[OF w B c refl refl h y] last show ?thesis by simp
qed

ML \<open>
  val checked = @{thms uv_piece_join uv_piece_birth_even uv_piece_quiet_odd uv_piece_birth_odd};
  val _ = if null (Thm_Deps.all_oracles checked) then () else error "UV piece oracle";
  val _ = if Thm_Deps.has_skip_proof checked then error "UV piece skipped proof" else ();
\<close>
end
