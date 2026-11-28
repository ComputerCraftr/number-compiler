theory Reflected_Joint_Seam
  imports Reflected_Fibre
begin

text \<open>A column reads from the older four digits towards the newly
appended digit. Each stage carries a radix remainder and a quotient.
The physical source must supply the incoming seam until four input digits
have displaced it.\<close>

type_synonym sheet_port = "nat \<times> nat"
type_synonym joint_port = "sheet_port \<times> sheet_port"

definition seam_sheet :: "nat \<Rightarrow> nat \<Rightarrow> sheet_port \<Rightarrow> nat \<Rightarrow> nat \<times> sheet_port" where
  "seam_sheet m b s x = (let u = m * fst s + x div b
    in (m * (u mod b) + snd s, x mod b, u div b))"

definition seam_unstep :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> sheet_port \<Rightarrow> nat \<times> sheet_port" where
  "seam_unstep m b y t = (let u = b * snd t + y div m
    in (b * (u mod m) + fst t, u div m, y mod m))"

lemma seam_unstep_exact:
  assumes "0 < m" "0 < b" "snd s < m" "x div b < m"
  shows "seam_unstep m b (fst (seam_sheet m b s x)) (snd (seam_sheet m b s x)) = (x,s)"
  using assms by (cases s) (simp add: seam_unstep_def seam_sheet_def Let_def
    div_mult_mod_eq mult.commute)

definition seam_joint :: "nat \<Rightarrow> joint_port \<Rightarrow> nat \<Rightarrow> nat \<times> joint_port" where
  "seam_joint m s x = (let b = 10 div m;
    p = seam_sheet m b (fst s) x; q = seam_sheet m b (snd s) (fst p)
    in (fst q, snd p, snd q))"

definition seam_advance :: "nat \<Rightarrow> nat \<Rightarrow> joint_port \<Rightarrow> joint_port" where
  "seam_advance m x s = snd (seam_joint m s x)"

theorem joint_seam_four_inputs_flush:
  "fold (seam_advance m) [a,b,c,d] s = fold (seam_advance m) [a,b,c,d] t"
  by (simp only: fold.simps id_apply comp_apply seam_advance_def seam_joint_def
    seam_sheet_def Let_def fst_conv snd_conv)

theorem joint_seam_emits_ordered_four_tick_gate:
  "fst (seam_joint m (fold (seam_advance m) [a,b,c,d] s) e) =
    reflected_source_two_gate m (reflected_source_two_gate m e d c)
      (reflected_source_two_gate m d c b) (reflected_source_two_gate m c b a)"
  by (simp only: fold.simps id_apply comp_apply seam_advance_def seam_joint_def
    seam_sheet_def reflected_source_two_gate_def Let_def fst_conv snd_conv)

definition joint_column :: "nat \<Rightarrow> (int \<Rightarrow> nat) \<Rightarrow> int \<Rightarrow> nat" where
  "joint_column m w j = fst (seam_joint m (fold (seam_advance m)
    [w (j-4), w (j-3), w (j-2), w (j-1)] ((0,0),(0,0))) (w j))"

text \<open>For a core of length L, choose k=L-1 and use zero extension.
At block t the native raw row occupies L+4t positions. Reversal therefore
includes the entire new fringe before the remaining physical gates.\<close>

theorem joint_column_physical_four_tick_run:
  fixes k j :: int
  shows "((joint_column m ^^ t) (\<lambda>j. source (k-j))) j =
    reflected_single_run (reflected_alternating_gate m) (4*t) source (k + 4*int t - j)"
proof -
  let ?f = "reflected_relative_two (reflected_source_two_gate m)"
  have blocks: "((joint_column m ^^ t) (\<lambda>j. source (k-j))) j =
      ((?f ^^ (2*t)) source) (k + 4*int t - j)"
  proof (induction t arbitrary: j)
    case 0 then show ?case by simp
  next
    case (Suc t)
    have count: "2 * Suc t = Suc (Suc (2*t))" by simp
    have col: "joint_column m w i = reflected_source_two_gate m
          (reflected_source_two_gate m (w i) (w (i-1)) (w (i-2)))
          (reflected_source_two_gate m (w (i-1)) (w (i-2)) (w (i-3)))
          (reflected_source_two_gate m (w (i-2)) (w (i-3)) (w (i-4)))" for w i
      by (simp only: joint_column_def joint_seam_emits_ordered_four_tick_gate)
    have pair: "?f w i = reflected_source_two_gate m (w (i-2)) (w (i-1)) (w i)" for w i
      by (rule reflected_relative_two_def)
    have transported: "((joint_column m ^^ t) (\<lambda>j. source (k-j))) =
        (\<lambda>j. ((?f ^^ (2*t)) source) (k + 4*int t - j))"
      by (rule ext, rule Suc.IH)
    have outer: "((joint_column m ^^ Suc t) (\<lambda>j. source (k-j))) j =
        joint_column m (\<lambda>j. ((?f ^^ (2*t)) source) (k + 4*int t - j)) j"
      by (simp only: funpow.simps comp_apply transported)
    have inner: "((?f ^^ (2*Suc t)) source) (k + 4*int (Suc t) - j) =
        ?f (?f ((?f ^^ (2*t)) source)) (k + 4*int (Suc t) - j)"
      by (simp only: count funpow.simps comp_apply)
    have gate_identity: "joint_column m (\<lambda>j. h (center-j)) j =
        ?f (?f h) (center+4-j)" for h center j
      by (simp only: col pair; simp add: algebra_simps)
    have index: "k + 4*int (Suc t) - j = (k + 4*int t)+4-j"
      by (simp add: algebra_simps)
    show ?case using outer inner index
        gate_identity[of "(?f ^^ (2*t)) source" "k + 4*int t" j]
      by metis
  qed
  have clock: "4*t = 2*(2*t)" by presburger
  show ?thesis using blocks by (simp only: clock reflected_single_run_even)
qed

text \<open>A constant terminal response discards the preceding prefix.
A stationary inlet permits a constant tail only after checking the receiving
digit is fixed by the actual seam.\<close>

definition seam_digit where "seam_digit m s x = fst (seam_joint m s x)"

lemma joint_seam_exact_reset_suffix:
  assumes closed: "fold (seam_digit m) prefix x < 10"
    and reset: "\<And>d. d < 10 \<Longrightarrow> fold (seam_digit m) suffix d = y"
  shows "fold (seam_digit m) (prefix @ suffix) x = y"
  using reset[OF closed] by simp

lemma joint_seam_fixed_tail:
  assumes fixed: "seam_digit m s x = x"
  shows "fold (seam_digit m) (replicate k s) x = x"
  using fixed by (induction k) simp_all

lemma seam_five_calibrated:
  "fst (seam_sheet 5 2 s x) = fst (seam_sheet 5 2 s (2*((x div 2) mod 2)))"
  by (cases s; simp add: seam_sheet_def Let_def mod_add_right_eq)

lemma joint_seam_digit_rank:
  assumes radix: "m=2 \<or> m=5"
  shows "two_image (seam_digit m s)"
proof (cases "m=2")
  case True
  show ?thesis unfolding two_image_def
  proof (rule exI[of _ "seam_digit m s 0"], rule exI[of _ "seam_digit m s 5"], intro allI impI)
    fix x::nat assume "x<10"
    then have "x div 5=0 \<or> x div 5=1" by presburger
    then show "seam_digit m s x=seam_digit m s 0 \<or> seam_digit m s x=seam_digit m s 5"
      by (auto simp: seam_digit_def seam_joint_def seam_sheet_def Let_def True)
  qed
next
  case False
  then have m: "m=5" using radix by simp
  show ?thesis unfolding two_image_def
  proof (rule exI[of _ "seam_digit m s 0"], rule exI[of _ "seam_digit m s 2"], intro allI impI)
    fix x::nat assume "x<10"
    have bit: "(x div 2) mod 2 = 0 \<or> (x div 2) mod 2 = 1" by presburger
    from bit seam_five_calibrated[of "fst s" x]
    show "seam_digit m s x=seam_digit m s 0 \<or> seam_digit m s x=seam_digit m s 2"
      by (auto simp: seam_digit_def seam_joint_def Let_def m)
  qed
qed

theorem joint_seam_periodic_residual:
  assumes radix: "m=2 \<or> m=5" and digit: "x<10"
    and closed: "\<And>d. d<10 \<Longrightarrow> fold (seam_digit m) (s#ss) d < 10"
  shows "(fold (seam_digit m) (s#ss) ^^ (2+k)) x =
    (fold (seam_digit m) (s#ss) ^^ (2+k mod 2)) x"
proof -
  have rank: "two_image (fold (seam_digit m) (s#ss))"
    using two_image_composition[OF joint_seam_digit_rank[OF radix, of s],
      of "fold (seam_digit m) ss"] by (simp add: fold_Cons)
  show ?thesis by (rule two_image_residual[OF two_image_eventual_square[OF rank closed digit]])
qed

lemma joint_seam_zero_reset:
  assumes "m = 2 \<or> m = 5" "x < 10"
  shows "seam_digit m ((0,0),(0,0)) x = 0"
proof -
  have digits: "x=0 \<or> x=1 \<or> x=2 \<or> x=3 \<or> x=4 \<or> x=5 \<or>
      x=6 \<or> x=7 \<or> x=8 \<or> x=9" using assms(2) by arith
  show ?thesis using assms(1) digits
    by (elim disjE; hypsubst_thin; code_simp)
qed

lemma joint_column_preserves_digits:
  assumes radix: "m=2 \<or> m=5" and source: "\<And>j. w j < 10"
  shows "((joint_column m ^^ t) w) i < 10"
proof -
  have gate: "reflected_source_two_gate m a b c < 10" if "a<10" "b<10" "c<10" for a b c
    using driven_closed[OF radix that, where moving=False]
    by (simp add: driven_digit_def)
  have step: "joint_column m row j < 10" if "\<And>k. row k < 10" for row j
    by (simp only: joint_column_def joint_seam_emits_ordered_four_tick_gate; intro gate that)
  show ?thesis
  proof (induction t arbitrary: i)
    case 0 then show ?case by (simp add: source)
  next
    case (Suc t)
    show ?case
      by (simp only: funpow.simps o_apply; rule step; rule Suc.IH)
  qed
qed

theorem joint_column_zero_halo_entry:
  assumes halo: "\<And>i. i < 0 \<Longrightarrow> w i = 0"
    and digits: "\<And>i. w i < 10"
    and radix: "m=2 \<or> m=5" and covered: "j < int t"
  shows "((joint_column m ^^ t) w) j = 0"
  using covered
proof (induction t arbitrary: j)
  case 0 then show ?case using halo by simp
next
  case (Suc t)
  let ?w = "(joint_column m ^^ t) w"
  have zero: "?w (j - k) = 0" if "0 < k" for k
    by (rule Suc.IH; use Suc.prems that in linarith)
  have port: "seam_advance m 0 ((0,0),(0,0)) = ((0,0),(0,0))"
    by (simp add: seam_advance_def seam_joint_def seam_sheet_def Let_def)
  have "joint_column m ?w j = seam_digit m ((0,0),(0,0)) (?w j)"
    by (simp add: joint_column_def seam_digit_def zero port)
  also have "... = 0" by (rule joint_seam_zero_reset[OF radix joint_column_preserves_digits[OF radix digits]])
  finally show ?case by simp
qed

text \<open>The periodic front checks every outgoing port and emitted digit.
The result at a selected column and the receiving port after that column
then follow from a single cyclic action.\<close>

lemma checked_front_selected_column:
  fixes step :: "'s \<Rightarrow> nat \<Rightarrow> nat \<times> 's"
  assumes phase: "p < 5" and inlet: "actual 0 = ports p"
    and source: "\<And>k. k < n \<Longrightarrow> input k = motif ((p+k) mod 5)"
    and advance: "\<And>k. k < n \<Longrightarrow> actual (Suc k) = snd (step (actual k) (input k))"
    and checked: "\<And>i. i < 5 \<Longrightarrow> step (ports i) (motif i) =
      (output i, ports (Suc i mod 5))"
  shows "actual n = ports ((p+n) mod 5)"
    and "k < n \<Longrightarrow> fst (step (actual k) (input k)) = output ((p+k) mod 5)"
proof -
  have state: "actual j = ports ((p+j) mod 5)" if "j \<le> n" for j
    using that
  proof (induction j)
    case 0 then show ?case by (simp add: inlet phase)
  next
    case (Suc j)
    have small: "j < n" using Suc.prems by simp
    have prev: "actual j = ports ((p+j) mod 5)" by (rule Suc.IH; use small in simp)
    show ?case using advance[OF small] source[OF small] checked[of "(p+j) mod 5"] prev
      by (simp add: mod_Suc_eq)
  qed
  show "actual n = ports ((p+n) mod 5)" by (rule state) simp
  assume "k < n"
  then show "fst (step (actual k) (input k)) = output ((p+k) mod 5)"
    using state[of k] checked[of "(p+k) mod 5"] source[of k] by simp
qed

definition sync_word :: "nat => nat list" where
  "sync_word m = (if m=2 then [6,9,2,0,7] else [9,6,7,0,2])"

definition sync_digit where "sync_digit m p = sync_word m ! (p mod 5)"
definition sync_port where
  "sync_port m p = fold (seam_advance m)
    [sync_digit m (p+1),sync_digit m (p+2),sync_digit m (p+3),sync_digit m (p+4)]
    ((0,0),(0,0))"

lemma sync_digit_mod [simp]: "sync_digit m (p mod 5) = sync_digit m p"
  by (simp add: sync_digit_def)

lemma sync_joint_transition:
  assumes radix: "m=2 \<or> m=5" and slot: "p<5"
  shows "seam_joint m (sync_port m p) (sync_digit m p) =
    (sync_digit m (Suc p), sync_port m (Suc p mod 5))"
proof -
  have phases: "p=0 \<or> p=1 \<or> p=2 \<or> p=3 \<or> p=4" using slot by arith
  show ?thesis using radix phases
    by (elim disjE; hypsubst_thin; code_simp)
qed

theorem sync_joint_calibrated_digit:
  assumes radix: "m=2 \<or> m=5"
  shows "fold (seam_digit m) (map (\<lambda>t. sync_port m ((p+t) mod 5)) [0..<n])
     (sync_digit m p) = sync_digit m (p+n)"
proof (induction n)
  case 0 then show ?case by simp
next
  case (Suc n)
  have one: "seam_digit m (sync_port m ((p+n) mod 5)) (sync_digit m (p+n)) =
      sync_digit m (Suc (p+n))"
    using sync_joint_transition[OF radix, of "(p+n) mod 5"]
    by (simp add: seam_digit_def sync_digit_def mod_Suc_eq)
  show ?case by (simp add: Suc.IH one)
qed

lemma sync_word_lane_offset:
  "(p + 64 * chunk + lane) mod 5 = (p + 4 * (chunk mod 5) + lane) mod (5::nat)"
proof -
  have factor: "(64*chunk) mod 5 = (4*(chunk mod 5)) mod (5::nat)"
  proof -
    have "(64*chunk) mod 5 = ((64 mod 5)*(chunk mod 5)) mod (5::nat)"
      by (rule mod_mult_eq[symmetric])
    then show ?thesis by simp
  qed
  have prefix: "(p+64*chunk) mod 5 = (p+4*(chunk mod 5)) mod (5::nat)"
    using factor by (metis mod_add_right_eq)
  show ?thesis using prefix by (metis mod_add_left_eq)
qed

ML \<open>
  val checked = @{thms seam_unstep_exact joint_seam_four_inputs_flush
    joint_seam_emits_ordered_four_tick_gate joint_column_physical_four_tick_run joint_seam_exact_reset_suffix joint_seam_fixed_tail
    joint_column_zero_halo_entry checked_front_selected_column joint_seam_periodic_residual
    sync_joint_transition sync_joint_calibrated_digit sync_word_lane_offset};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "joint reflected seam uses an oracle";
  val _ = if Thm_Deps.has_skip_proof checked then
    error "joint reflected seam has skipped proofs" else ();
\<close>

end
