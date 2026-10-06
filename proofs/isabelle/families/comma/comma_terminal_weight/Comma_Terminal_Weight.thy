theory Comma_Terminal_Weight
  imports Comma_Decade_Residual_Core.Comma_Decade_Residual_Core
begin

text \<open>
The exact terminal offset is represented as an occurrence weight.  A fork
digit contributes its within-decade position, while a landmine occupies the
last position.  Nine units are added for each completed decade.  The codec
is an exact candidate occurrence representation; these lemmas do not claim
that the current runtime publisher has adopted it as a control key.
\<close>

definition comma_terminal_weight_admitted :: "comma_decade_terminal \<Rightarrow> bool" where
  "comma_terminal_weight_admitted terminal = (case terminal of
    Comma_Terminal_Fork a \<Rightarrow> 2 \<le> a \<and> a \<le> 9
  | Comma_Terminal_Landmine \<Rightarrow> True)"

fun comma_terminal_weight_digit :: "comma_decade_terminal \<Rightarrow> nat" where
  "comma_terminal_weight_digit (Comma_Terminal_Fork a) = a - 2"
| "comma_terminal_weight_digit Comma_Terminal_Landmine = 8"

definition comma_terminal_weight_terminal :: "nat \<Rightarrow> comma_decade_terminal" where
  "comma_terminal_weight_terminal j =
    (if j=8 then Comma_Terminal_Landmine else Comma_Terminal_Fork (j + 2))"

definition comma_terminal_weight_encode ::
    "nat \<Rightarrow> comma_decade_terminal \<Rightarrow> nat" where
  "comma_terminal_weight_encode height terminal =
    9 * height + comma_terminal_weight_digit terminal"

definition comma_terminal_weight_decode ::
    "nat \<Rightarrow> nat \<times> comma_decade_terminal" where
  "comma_terminal_weight_decode D =
    (D div 9, comma_terminal_weight_terminal (D mod 9))"

lemma comma_terminal_weight_fork_position:
  assumes step: "comma_finite_step r (Comma_Near f delta h)=Comma_Fork a d"
  shows "comma_terminal_weight_digit (Comma_Terminal_Fork a)=f-1"
proof -
  have bounds: "1\<le>f \<and> f<9 \<and> a=f+1"
    using step
    by (auto simp: comma_finite_step_def comma_weighted_step_def Let_def
        split: if_splits)
  show ?thesis using bounds by simp
qed

lemma comma_terminal_weight_landmine_position:
  assumes step: "comma_finite_step r (Comma_Near f delta h)=Comma_Landmine d"
  shows "f=9 \<and> comma_terminal_weight_digit Comma_Terminal_Landmine=8"
  using step
  by (auto simp: comma_finite_step_def comma_weighted_step_def Let_def
      split: if_splits)

text \<open>For an admitted sector-9 Near state, landmine detection is the
borrow criterion on the remaining headroom.  The broad Near validity bound
is retained here; no finite list of the eight possible offsets is used as a
proof premise or certificate.\<close>

lemma comma_near9_landmine_linear_seam:
  fixes h q s d :: nat
  assumes digit: "0<s" "s<10"
    and phase: "d=10-s"
    and decomposition: "h=10*q+s"
    and lower_seam: "10*d+1<h"
    and upper_seam: "h\<le>10*d+9"
  shows "h-1=9*(q+1) \<and> 2\<le>q+1 \<and> q+1\<le>9"
proof -
  have translated_lower: "101<10*q+11*s"
    using lower_seam phase decomposition by arith
  have translated_upper: "10*q+11*s\<le>109"
    using upper_seam phase decomposition by arith
  have factorization: "10*q+11*s=10*(q+s)+s"
    by arith
  have quotient: "q+s=10"
    using translated_lower translated_upper factorization digit(2) by arith
  have residue_bounds: "2\<le>s" "s\<le>9"
    using translated_lower translated_upper factorization quotient digit(2) by arith+
  have weight: "h-1=9*(q+1)"
    using decomposition quotient residue_bounds(2) by arith
  have quotient_bounds: "2\<le>q+1" "q+1\<le>9"
    using quotient residue_bounds by arith+
  show ?thesis using weight quotient_bounds by blast
qed

lemma comma_near9_landmine_borrow_criterion:
  assumes lower: "1 \<le> h" and upper: "h \<le> 540"
  shows "comma_finite_step r (Comma_Near 9 delta h)=Comma_Landmine delta \<longleftrightarrow>
    (18 \<le> h-1 \<and> h-1 \<le> 81 \<and> (h-1) mod 9=0)"
proof -
  let ?d = "(10-h mod 10) mod 10"
  let ?q = "h div 10"
  let ?s = "h mod 10"
  have step_rule:
    "comma_finite_step r (Comma_Near 9 delta h)=Comma_Landmine delta \<longleftrightarrow>
      10*?d+1<h \<and> h\<le>10*?d+9"
    using lower upper
    by (auto simp: comma_finite_step_def comma_weighted_step_def
        comma_weighted_step_with_headroom_def Let_def split: if_splits; arith)
  have digit: "?s<10" by simp
  have decomposition: "h=10*?q+?s"
    by (simp add: div_mult_mod_eq mult.commute)
  have residue_digit: "?d=(if ?s=0 then 0 else 10-?s)"
    using digit by (cases "?s=0") simp_all
  show ?thesis
  proof
    assume landmine: "comma_finite_step r (Comma_Near 9 delta h)=Comma_Landmine delta"
    have bounds: "10*?d+1<h" "h\<le>10*?d+9"
      using step_rule landmine by blast+
    show "18\<le>h-1 \<and> h-1\<le>81 \<and> (h-1) mod 9=0"
    proof (cases "?s=0")
      case True
      then have "?d=0" using residue_digit by simp
      then have "1<h" "h\<le>9" using bounds by auto
      moreover have "h=10*?q" using decomposition True by simp
      ultimately have False by arith
      then show ?thesis by simp
    next
      case False
      have d: "?d=10-?s" using residue_digit False by simp
      have positive: "0<?s" using False by simp
      have canonical_weight:
        "h-1=9*(?q+1) \<and> 2\<le>?q+1 \<and> ?q+1\<le>9"
        by (rule comma_near9_landmine_linear_seam[OF positive digit d decomposition
          bounds(1) bounds(2)])
      have weight: "h-1=9*(?q+1)" and quotient_bounds:
        "2\<le>?q+1" "?q+1\<le>9"
        using canonical_weight by auto
      show ?thesis
        using weight quotient_bounds by (auto simp: dvd_eq_mod_eq_0)
    qed
  next
    assume candidate:
      "18\<le>h-1 \<and> h-1\<le>81 \<and> (h-1) mod 9=0"
    let ?b = "h-1"
    obtain k where weight: "?b=9*k"
      using candidate by (auto simp: dvd_eq_mod_eq_0 elim: dvdE)
    have k_bounds: "2\<le>k" "k\<le>9"
      using candidate weight by arith+
    have h_value: "h=9*k+1" using lower weight by arith
    have decimal_decomposition:
      "h=10*(k-1)+(11-k)"
      using h_value k_bounds by arith
    have tail_bound: "11-k<10" using k_bounds by arith
    have phase: "h mod 10=11-k"
      using decimal_decomposition tail_bound by (simp add: mult.commute)
    have d: "?d=k-1"
    proof -
      have decimal_sub: "10-(11-k)=k-1" using k_bounds by arith
      show ?thesis using phase decimal_sub k_bounds by simp
    qed
    have seam_bounds:
      "10*(k-1)+1<h" "h\<le>10*(k-1)+9"
      using h_value k_bounds by arith+
    have exact_seam: "10*?d+1<h \<and> h\<le>10*?d+9"
      using d seam_bounds by simp
    show "comma_finite_step r (Comma_Near 9 delta h)=Comma_Landmine delta"
      using step_rule exact_seam by blast
  qed
qed

corollary comma_near9_landmine_borrow_band:
  assumes lower: "1 \<le> h" and upper: "h \<le> 540"
    and band: "18 \<le> h-1" "h-1 \<le> 81"
  shows "comma_finite_step r (Comma_Near 9 delta h)=Comma_Landmine delta \<longleftrightarrow>
    (h-1) mod 9=0"
  using comma_near9_landmine_borrow_criterion[where r=r and delta=delta, OF lower upper]
    band by simp

text \<open>The within-decade terminal position is a control projection, while
the exact headroom and displacement remain occurrence data.  A fork can only
occur at the unique headroom \(91-9f\), and a landmine is recognized by the
sector-9 borrow band.  Continuing and crossing moves have no terminal
position.\<close>

definition comma_near_terminal_width_j :: "nat \<Rightarrow> nat \<Rightarrow> nat option" where
  "comma_near_terminal_width_j f h =
    (if 1 \<le> f \<and> f < 9 \<and> h = 91 - 9 * f then Some (f - 1)
     else if f = 9 \<and> 1 \<le> h \<and> 18 \<le> h - 1 \<and>
       h - 1 \<le> 81 \<and> (h - 1) mod 9 = 0
     then Some 8 else None)"

fun comma_terminal_width_j_of_move :: "comma_finite_move \<Rightarrow> nat option" where
  "comma_terminal_width_j_of_move (Comma_Fork a delta) = Some (a - 2)"
| "comma_terminal_width_j_of_move (Comma_Landmine delta) = Some 8"
| "comma_terminal_width_j_of_move (Comma_Next successor) = None"
| "comma_terminal_width_j_of_move Comma_Invalid = None"

lemma comma_near_fork_headroom_normal_form:
  assumes step:
    "comma_finite_step r (Comma_Near f delta h) =
      Comma_Fork a move_delta"
  shows "1 \<le> f \<and> f < 9 \<and> h = 91 - 9 * f \<and>
    a = f + 1 \<and> move_delta = delta"
proof -
  let ?d = "(10 - h mod 10) mod 10"
  have fields: "1 \<le> f \<and> f < 9 \<and>
      h = 10 * ?d + f + 1 \<and> a = f + 1 \<and> move_delta = delta"
    using step
    by (auto simp: comma_near_control_formula Let_def split: if_splits)
  have head_equation: "h = 10 * ?d + (f + 1)"
    using fields by arith
  have f_plus_bound: "f + 1 < 10"
    using fields by arith
  have reduced:
      "(10 * ?d + (f + 1)) mod 10 = (f + 1) mod 10"
    by (rule mod_mult_self4)
  have digit: "h mod 10 = f + 1"
    using head_equation reduced f_plus_bound by simp
  have d: "?d = 9 - f"
    using digit f_plus_bound by simp
  have headroom: "h = 91 - 9 * f"
    using head_equation d fields by arith
  show ?thesis using fields headroom by blast
qed

ML \<open>val _ = Thm.consolidate [@{thm comma_near_fork_headroom_normal_form}]\<close>

lemma comma_near_fork_headroom_iff:
  assumes sector_lower: "1 \<le> f" and sector_upper: "f < 9"
    and headroom_lower: "1 \<le> h" and headroom_upper: "h \<le> 540"
  shows "comma_finite_step r (Comma_Near f delta h) =
      Comma_Fork (f + 1) delta \<longleftrightarrow> h = 91 - 9 * f"
proof
  assume step:
    "comma_finite_step r (Comma_Near f delta h) =
      Comma_Fork (f + 1) delta"
  have normal: "h = 91 - 9 * f"
    using comma_near_fork_headroom_normal_form[OF step] by blast
  show "h = 91 - 9 * f" by (rule normal)
next
  assume headroom: "h = 91 - 9 * f"
  have threshold: "h = 10 * (9 - f) + (f + 1)"
    using headroom sector_lower sector_upper by arith
  have digit: "h mod 10 = f + 1"
    using threshold sector_lower sector_upper by simp
  have d: "(10 - h mod 10) mod 10 = 9 - f"
    using digit sector_lower sector_upper by simp
  show "comma_finite_step r (Comma_Near f delta h) =
      Comma_Fork (f + 1) delta"
    using sector_lower sector_upper headroom_lower headroom_upper d threshold
    by (simp add: comma_near_control_formula Let_def)
qed

ML \<open>val _ = Thm.consolidate [@{thm comma_near_fork_headroom_iff}]\<close>

lemma comma_near_terminal_width_j_refines:
  assumes sector_lower: "1 \<le> f" and sector_upper: "f \<le> 9"
    and headroom_lower: "1 \<le> h" and headroom_upper: "h \<le> 540"
  shows "comma_near_terminal_width_j f h =
    comma_terminal_width_j_of_move
      (comma_finite_step r (Comma_Near f delta h))"
proof (cases "f = 9")
  case True
  show ?thesis
  proof (cases "comma_finite_step r (Comma_Near f delta h)")
    case (Comma_Fork a move_delta)
    have False
      using Comma_Fork True sector_lower sector_upper
      by (auto simp: comma_near_control_formula Let_def split: if_splits)
    then show ?thesis by simp
  next
    case (Comma_Landmine move_delta)
    have shift: "move_delta=delta"
      using Comma_Landmine True sector_lower sector_upper
        headroom_lower headroom_upper
      by (auto simp: comma_near_control_formula Let_def split: if_splits)
    have exact_step:
        "comma_finite_step r (Comma_Near 9 delta h)=Comma_Landmine delta"
      using Comma_Landmine True shift by simp
    have band:
        "18 \<le> h - 1 \<and> h - 1 \<le> 81 \<and> (h - 1) mod 9 = 0"
      using iffD1[OF comma_near9_landmine_borrow_criterion
          [where r=r and delta=delta, OF headroom_lower headroom_upper]
          exact_step] .
    show ?thesis using True band Comma_Landmine headroom_lower headroom_upper
      by (simp add: comma_near_terminal_width_j_def)
  next
    case (Comma_Next successor)
    have not_landmine:
        "comma_finite_step r (Comma_Near 9 delta h) \<noteq>
          Comma_Landmine delta"
      using Comma_Next True by simp
    have not_band:
        "\<not> (18 \<le> h - 1 \<and> h - 1 \<le> 81 \<and> (h - 1) mod 9 = 0)"
    proof
      assume band:
        "18 \<le> h - 1 \<and> h - 1 \<le> 81 \<and> (h - 1) mod 9 = 0"
      have exact_landmine:
          "comma_finite_step r (Comma_Near 9 delta h)=Comma_Landmine delta"
        using iffD2[OF comma_near9_landmine_borrow_criterion
            [where r=r and delta=delta, OF headroom_lower headroom_upper]
            band] .
      show False using exact_landmine not_landmine by contradiction
    qed
    show ?thesis using True not_band Comma_Next headroom_lower headroom_upper
      by (simp add: comma_near_terminal_width_j_def)
  next
    case Comma_Invalid
    then have False using True sector_lower sector_upper
        headroom_lower headroom_upper
      by (auto simp: comma_near_control_formula Let_def split: if_splits)
    then show ?thesis by simp
  qed
next
  case False
  have sector_below: "f < 9"
    using sector_upper False by arith
  show ?thesis
  proof (cases "comma_finite_step r (Comma_Near f delta h)")
    case (Comma_Fork a move_delta)
    have normal_full:
        "1 \<le> f \<and> f < 9 \<and> h = 91 - 9 * f \<and>
          a = f + 1 \<and> move_delta = delta"
      by (rule comma_near_fork_headroom_normal_form[OF Comma_Fork])
    show ?thesis using sector_below normal_full Comma_Fork
      by (simp add: comma_near_terminal_width_j_def)
  next
    case (Comma_Landmine move_delta)
    have False
      using Comma_Landmine sector_below
      by (auto simp: comma_near_control_formula Let_def split: if_splits)
    then show ?thesis by simp
  next
    case (Comma_Next successor)
    have not_headroom: "h \<noteq> 91 - 9 * f"
    proof
      assume headroom: "h = 91 - 9 * f"
      have fork:
          "comma_finite_step r (Comma_Near f delta h) =
            Comma_Fork (f + 1) delta"
        by (rule iffD2[OF comma_near_fork_headroom_iff
          [OF sector_lower sector_below headroom_lower headroom_upper]
          headroom])
      then show False using Comma_Next by simp
    qed
    show ?thesis using sector_below not_headroom Comma_Next
      by (simp add: comma_near_terminal_width_j_def)
  next
    case Comma_Invalid
    then have False using sector_lower sector_below
        headroom_lower headroom_upper
      by (auto simp: comma_near_control_formula Let_def split: if_splits)
    then show ?thesis by simp
  qed
qed

ML \<open>val _ = Thm.consolidate [@{thm comma_near_terminal_width_j_refines}]\<close>

lemma comma_terminal_weight_digit_bound:
  assumes "comma_terminal_weight_admitted terminal"
  shows "comma_terminal_weight_digit terminal < 9"
  using assms
proof (cases terminal)
  case (Comma_Terminal_Fork a)
  then show ?thesis using assms
    by (simp add: comma_terminal_weight_admitted_def; presburger)
next
  case Comma_Terminal_Landmine
  then show ?thesis by simp
qed

lemma comma_terminal_weight_terminal_digit:
  assumes "j < 9"
  shows "comma_terminal_weight_digit (comma_terminal_weight_terminal j) = j"
  using assms by (cases "j=8")
    (auto simp: comma_terminal_weight_terminal_def)

lemma comma_terminal_weight_terminal_admitted:
  "comma_terminal_weight_admitted
    (comma_terminal_weight_terminal (D mod 9))"
proof -
  have remainder: "D mod 9 < 9" by simp
  show ?thesis
  proof (cases "D mod 9 = 8")
    case True
    then show ?thesis
      by (simp add: comma_terminal_weight_admitted_def comma_terminal_weight_terminal_def)
  next
    case False
    have small: "D mod 9 < 8" using remainder False by presburger
    then show ?thesis
      using False
      by (simp add: comma_terminal_weight_admitted_def comma_terminal_weight_terminal_def;
          presburger)
  qed
qed

lemma comma_terminal_weight_decode_encode:
  assumes admitted: "comma_terminal_weight_admitted terminal"
  shows "comma_terminal_weight_decode (comma_terminal_weight_encode height terminal) =
    (height,terminal)"
proof -
  have digit: "comma_terminal_weight_digit terminal < 9"
    by (rule comma_terminal_weight_digit_bound[OF admitted])
  have div: "(9 * height + comma_terminal_weight_digit terminal) div 9 = height"
    using digit by (simp add: div_add1_eq)
  have mod: "(9 * height + comma_terminal_weight_digit terminal) mod 9 =
      comma_terminal_weight_digit terminal"
    using digit by (simp add: mod_add_left_eq)
  have terminal:
    "comma_terminal_weight_terminal (comma_terminal_weight_digit terminal) = terminal"
    using admitted by (cases terminal)
      (auto simp: comma_terminal_weight_admitted_def comma_terminal_weight_terminal_def)
  show ?thesis
    by (simp only: comma_terminal_weight_decode_def comma_terminal_weight_encode_def
      div mod terminal)
qed

theorem comma_terminal_weight_encode_decode:
  "comma_terminal_weight_encode
      (fst (comma_terminal_weight_decode D))
      (snd (comma_terminal_weight_decode D)) = D"
proof -
  have digit_bound: "D mod 9 < 9" by simp
  have terminal_digit:
    "comma_terminal_weight_digit (comma_terminal_weight_terminal (D mod 9)) = D mod 9"
    by (rule comma_terminal_weight_terminal_digit[OF digit_bound])
  have arithmetic: "9 * (D div 9) + D mod 9 = D"
    by (simp add: div_mult_mod_eq mult.commute)
  show ?thesis
    by (simp only: comma_terminal_weight_decode_def fst_conv snd_conv
      comma_terminal_weight_encode_def terminal_digit arithmetic)
qed

lemma comma_terminal_weight_decades_add:
  "comma_terminal_weight_encode (height + decades) terminal =
    9 * decades + comma_terminal_weight_encode height terminal"
  by (simp add: comma_terminal_weight_encode_def algebra_simps)

theorem comma_terminal_weight_decode_decades_add:
  assumes admitted: "comma_terminal_weight_admitted terminal"
  shows "comma_terminal_weight_decode
      (9 * decades + comma_terminal_weight_encode height terminal) =
    (decades + height,terminal)"
proof -
  have encoded:
    "9 * decades + comma_terminal_weight_encode height terminal =
      comma_terminal_weight_encode (height + decades) terminal"
    by (simp add: comma_terminal_weight_encode_def algebra_simps)
  have roundtrip:
    "comma_terminal_weight_decode
      (comma_terminal_weight_encode (height + decades) terminal) =
       (height + decades,terminal)"
    by (rule comma_terminal_weight_decode_encode[OF admitted])
  show ?thesis using encoded roundtrip by (simp add: add.commute)
qed

lemma comma_decade_exact_summary_terminal_admitted:
  assumes "comma_decade_exact_summary s height terminal"
  shows "comma_terminal_weight_admitted terminal"
proof -
  have bounds: "(case terminal of Comma_Terminal_Fork a \<Rightarrow>
      2 \<le> a \<and> a \<le> 9 | Comma_Terminal_Landmine \<Rightarrow> True)"
    by (rule comma_decade_terminal_fork_bounds[OF assms])
  show ?thesis using bounds
    by (cases terminal) (auto simp: comma_terminal_weight_admitted_def)
qed

text \<open>A Stop value records the exact number of within-decade positions.
Terminal observations contribute their local digit; each continuing decade
adds nine.  This relation is defined directly over the decade control, with
no height argument or fuel in its proof interface.\<close>

inductive comma_decade_weighted_stop :: "comma_decade_state \<Rightarrow> nat \<Rightarrow> bool" where
  fork: "comma_decade_control s=Comma_Decade_Fork a 0 \<Longrightarrow>
    2\<le>a \<Longrightarrow> a\<le>9 \<Longrightarrow>
    comma_decade_weighted_stop s (a-2)"
| landmine: "comma_decade_control s=Comma_Decade_Landmine 0 \<Longrightarrow>
    comma_decade_weighted_stop s 8"
| live: "comma_decade_control s=Comma_Decade_Continue t \<Longrightarrow>
    comma_decade_weighted_stop t D \<Longrightarrow>
    comma_decade_weighted_stop s (D+9)"

theorem comma_decade_exact_summary_implies_weighted_stop:
  assumes summary: "comma_decade_exact_summary s height terminal"
  shows "comma_decade_weighted_stop s
    (comma_terminal_weight_encode height terminal)"
  using summary
proof (induction rule: comma_decade_exact_summary.induct)
  case (fork s a)
  have bounds: "2\<le>a" "a\<le>9"
    using comma_decade_terminal_fork_bounds[
        OF comma_decade_exact_summary.fork[OF fork.hyps]]
    by simp_all
  have weighted: "comma_decade_weighted_stop s (a-2)"
    by (rule comma_decade_weighted_stop.fork[OF fork.hyps bounds(1) bounds(2)])
  show ?case using weighted by (simp add: comma_terminal_weight_encode_def)
next
  case (landmine s)
  have weighted: "comma_decade_weighted_stop s 8"
    by (rule comma_decade_weighted_stop.landmine[OF landmine.hyps])
  show ?case using weighted by (simp add: comma_terminal_weight_encode_def)
next
  case (crossing s t height terminal)
  have child:
    "comma_decade_weighted_stop t
      (comma_terminal_weight_encode height terminal)"
    by (rule crossing.IH)
  have weighted:
    "comma_decade_weighted_stop s
      (comma_terminal_weight_encode height terminal+9)"
    by (rule comma_decade_weighted_stop.live[OF crossing.hyps(1) child])
  have code:
    "comma_terminal_weight_encode (Suc height) terminal =
      comma_terminal_weight_encode height terminal+9"
    by (simp add: comma_terminal_weight_encode_def algebra_simps)
  show ?case using weighted code by simp
qed

theorem comma_decade_weighted_stop_imp_exact_encode:
  assumes stop: "comma_decade_weighted_stop s D"
  shows "\<exists>height terminal.
    comma_decade_exact_summary s height terminal \<and>
    D=comma_terminal_weight_encode height terminal"
  using stop
proof (induction rule: comma_decade_weighted_stop.induct)
  case (fork s a)
  have summary: "comma_decade_exact_summary s 0 (Comma_Terminal_Fork a)"
    by (rule comma_decade_exact_summary.fork[OF fork.hyps(1)])
  show ?case using summary by (intro exI[of _ 0] exI[of _ "Comma_Terminal_Fork a"])
    (simp add: comma_terminal_weight_encode_def)
next
  case (landmine s)
  have summary: "comma_decade_exact_summary s 0 Comma_Terminal_Landmine"
    by (rule comma_decade_exact_summary.landmine[OF landmine.hyps])
  show ?case using summary by (intro exI[of _ 0] exI[of _ Comma_Terminal_Landmine])
    (simp add: comma_terminal_weight_encode_def)
next
  case (live s t D)
  obtain height terminal where summary:
    "comma_decade_exact_summary t height terminal"
    and encoded: "D=comma_terminal_weight_encode height terminal"
    using live.IH by blast
  have parent:
    "comma_decade_exact_summary s (Suc height) terminal"
    by (rule comma_decade_exact_summary.crossing[OF live.hyps(1) summary])
  have code:
    "D+9=comma_terminal_weight_encode (Suc height) terminal"
    using encoded by (simp add: comma_terminal_weight_encode_def algebra_simps
      add.commute)
  show ?case using parent code by blast
qed

theorem comma_decade_weighted_stop_iff_decoded_exact:
  "comma_decade_weighted_stop s D \<longleftrightarrow>
    comma_decade_exact_summary s
      (fst (comma_terminal_weight_decode D))
      (snd (comma_terminal_weight_decode D))"
proof
  assume stop: "comma_decade_weighted_stop s D"
  obtain height terminal where summary:
    "comma_decade_exact_summary s height terminal"
    and encoded: "D=comma_terminal_weight_encode height terminal"
    using comma_decade_weighted_stop_imp_exact_encode[OF stop] by blast
  have decoded:
    "comma_terminal_weight_decode D=(height,terminal)"
  proof -
    have same:
      "comma_terminal_weight_decode D =
        comma_terminal_weight_decode (comma_terminal_weight_encode height terminal)"
      by (rule arg_cong[OF encoded])
    show ?thesis
      by (rule trans[OF same comma_terminal_weight_decode_encode[
        OF comma_decade_exact_summary_terminal_admitted[OF summary]]])
  qed
  show "comma_decade_exact_summary s
      (fst (comma_terminal_weight_decode D))
      (snd (comma_terminal_weight_decode D))"
    using summary decoded by simp
next
  assume summary:
    "comma_decade_exact_summary s
      (fst (comma_terminal_weight_decode D))
      (snd (comma_terminal_weight_decode D))"
  have stop: "comma_decade_weighted_stop s
      (comma_terminal_weight_encode
        (fst (comma_terminal_weight_decode D))
        (snd (comma_terminal_weight_decode D)))"
    by (rule comma_decade_exact_summary_implies_weighted_stop[OF summary])
  show "comma_decade_weighted_stop s D"
    using stop comma_terminal_weight_encode_decode by simp
qed

theorem comma_decade_summary_terminal_weight_roundtrip:
  assumes summary: "comma_decade_exact_summary source height terminal"
  shows "comma_terminal_weight_decode
      (comma_terminal_weight_encode height terminal)=(height,terminal)"
  by (rule comma_terminal_weight_decode_encode[
    OF comma_decade_exact_summary_terminal_admitted[OF summary]])

ML \<open>
  val checked = @{thms comma_terminal_weight_decode_encode
    comma_terminal_weight_encode_decode comma_terminal_weight_decades_add
    comma_terminal_weight_decode_decades_add comma_terminal_weight_fork_position
    comma_terminal_weight_landmine_position
    comma_near_fork_headroom_normal_form comma_near_fork_headroom_iff
    comma_near_terminal_width_j_refines
    comma_near9_landmine_borrow_criterion comma_near9_landmine_borrow_band
    comma_decade_exact_summary_terminal_admitted
    comma_decade_exact_summary_implies_weighted_stop
    comma_decade_weighted_stop_imp_exact_encode
    comma_decade_weighted_stop_iff_decoded_exact
    comma_decade_summary_terminal_weight_roundtrip};
  val _ = Thm.consolidate checked;
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Comma terminal occurrence weight depends on an oracle"
\<close>

end
