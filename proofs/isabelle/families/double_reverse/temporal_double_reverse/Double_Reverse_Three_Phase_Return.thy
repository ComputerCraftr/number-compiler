theory Double_Reverse_Three_Phase_Return
  imports Double_Reverse_Periodic_Ring_Action
begin

text \<open>A three-step translating ring is usable at a physical coordinate only
when the source supplies the whole causal halo. The remainder is read from
the original ring and its first two local images.\<close>

lemma double_reverse_step_shift:
  fixes step :: "(int \<Rightarrow> nat) \<Rightarrow> int \<Rightarrow> nat"
  assumes rule: "\<And>x i. step x i = double_reverse_t2_digit (x (i-1)) (x i) (x (i+1))"
  shows "step (\<lambda>i. x (i+offset)) i = step x (i+offset)"
  by (simp add: rule algebra_simps)

lemma double_reverse_power_shift:
  fixes step :: "(int \<Rightarrow> nat) \<Rightarrow> int \<Rightarrow> nat"
  assumes rule: "\<And>x i. step x i = double_reverse_t2_digit (x (i-1)) (x i) (x (i+1))"
  shows "(step ^^ n) (\<lambda>i. x (i+offset)) i = (step ^^ n) x (i+offset)"
proof (induction n arbitrary: x i)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have equality: "(step ^^ n) (\<lambda>i. x (i+offset)) =
      (\<lambda>i. (step ^^ n) x (i+offset))"
    by (rule ext) (rule Suc.IH)
  show ?case
    by (simp only: funpow.simps comp_apply equality double_reverse_step_shift[OF rule])
qed

definition double_reverse_cyclic_word :: "nat list \<Rightarrow> int \<Rightarrow> nat" where
  "double_reverse_cyclic_word word i = word ! nat (i mod int (length word))"

lemma double_reverse_finite_three_miter:
  fixes step :: "(int \<Rightarrow> nat) \<Rightarrow> int \<Rightarrow> nat"
  assumes rule: "\<And>x i. step x i = double_reverse_t2_digit (x (i-1)) (x i) (x (i+1))"
      and nonempty: "word \<noteq> []"
      and checked: "\<And>i. 0 \<le> i \<Longrightarrow> i < int (length word) \<Longrightarrow>
        (step ^^ 3) (double_reverse_cyclic_word word) i =
          double_reverse_cyclic_word word (i+shift)"
  shows "(step ^^ 3) (double_reverse_cyclic_word word) i =
    double_reverse_cyclic_word word (i+shift)"
proof -
  let ?n = "int (length word)"
  let ?ring = "double_reverse_cyclic_word word"
  let ?q = "i div ?n"
  let ?r = "i mod ?n"
  have positive: "0 < ?n" using nonempty by simp
  have residue: "0 \<le> ?r" "?r < ?n" using positive by simp_all
  have shifted: "(\<lambda>j. ?ring (j + ?n*?q)) = ?ring"
    by (rule ext) (simp add: double_reverse_cyclic_word_def)
  have index: "?r + ?n*?q = i"
    by (simp add: mult.commute)
  have transport: "(step ^^ 3) ?ring i = (step ^^ 3) ?ring ?r"
    using double_reverse_power_shift[OF rule, of 3 ?ring "?n*?q" ?r]
    by (simp add: shifted index)
  have successor: "?ring (?r+shift) = ?ring (i+shift)"
    by (simp add: double_reverse_cyclic_word_def mod_add_left_eq)
  show ?thesis using transport checked[OF residue] successor by simp
qed

lemma double_reverse_three_blocks:
  fixes step :: "(int \<Rightarrow> nat) \<Rightarrow> int \<Rightarrow> nat" and ring :: "int \<Rightarrow> nat"
  assumes rule: "\<And>x i. step x i = double_reverse_t2_digit (x (i-1)) (x i) (x (i+1))"
      and miter: "\<And>i. (step ^^ 3) ring i = ring (i+shift)"
  shows "(step ^^ (3*q)) ring i = ring (i+int q*shift)"
proof (induction q arbitrary: i)
  case 0
  then show ?case by simp
next
  case (Suc q)
  have equality: "(step ^^ 3) ring = (\<lambda>i. ring (i+shift))"
    by (rule ext) (rule miter)
  have count: "3 * Suc q = 3*q+3" by simp
  have split: "(step ^^ (3*Suc q)) ring i =
      (step ^^ (3*q)) ((step ^^ 3) ring) i"
    by (simp only: count funpow_add comp_apply)
  have shift:
    "(step ^^ (3*q)) ((\<lambda>j. ring (j+shift))) i =
      (step ^^ (3*q)) ring (i+shift)"
    by (rule double_reverse_power_shift[OF rule])
  show ?case using split shift Suc.IH[of "i+shift"]
    by (simp only: equality; simp add: algebra_simps)
qed

lemma double_reverse_source_ring_agreement:
  fixes step :: "(int \<Rightarrow> nat) \<Rightarrow> int \<Rightarrow> nat"
    and source ring :: "int \<Rightarrow> nat"
  assumes rule: "\<And>x i. step x i = double_reverse_t2_digit (x (i-1)) (x i) (x (i+1))"
      and halo: "\<And>i. abs (i-center) \<le> int ticks \<Longrightarrow> source i = ring i"
  shows "(step ^^ ticks) source center = (step ^^ ticks) ring center"
  using halo
proof (induction ticks arbitrary: center)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have inner: "\<And>j. abs (j-center) \<le> 1 \<Longrightarrow> (step ^^ n) source j = (step ^^ n) ring j"
  proof -
    fix j assume bound: "abs (j-center) \<le> 1"
    show "(step ^^ n) source j = (step ^^ n) ring j"
    proof (rule Suc.IH)
      fix i assume "abs (i-j) \<le> int n"
      with bound have "abs (i-center) \<le> int (Suc n)" by (auto simp: abs_le_iff; linarith)
      thus "source i = ring i" by (rule Suc.prems)
    qed
  qed
  have left: "(step ^^ n) source (center-1) = (step ^^ n) ring (center-1)"
    by (rule inner) simp
  have middle: "(step ^^ n) source center = (step ^^ n) ring center"
    by (rule inner) simp
  have right: "(step ^^ n) source (center+1) = (step ^^ n) ring (center+1)"
    by (rule inner) simp
  show ?case
    apply (simp only: funpow.simps comp_apply)
    apply (subst rule)
    apply (subst rule)
    by (simp only: left middle right)
qed

theorem double_reverse_three_phase_source:
  fixes step :: "(int \<Rightarrow> nat) \<Rightarrow> int \<Rightarrow> nat"
    and source ring :: "int \<Rightarrow> nat"
  assumes rule: "\<And>x i. step x i = double_reverse_t2_digit (x (i-1)) (x i) (x (i+1))"
      and miter: "\<And>i. (step ^^ 3) ring i = ring (i+shift)"
      and halo: "\<And>i. abs (i-center) \<le> int (3*q+r) \<Longrightarrow> source i = ring i"
  shows "(step ^^ (3*q+r)) source center =
    (step ^^ r) ring (center + int q*shift)"
proof -
  have blocks: "(step ^^ (3*q)) ring = (\<lambda>i. ring (i+int q*shift))"
    by (rule ext) (rule double_reverse_three_blocks[OF rule miter])
  have agreement: "(step ^^ (3*q+r)) source center = (step ^^ (3*q+r)) ring center"
    by (rule double_reverse_source_ring_agreement[OF rule halo])
  have exponent: "3*q+r = r+3*q" by simp
  have split: "(step ^^ (3*q+r)) ring center =
      (step ^^ r) ((step ^^ (3*q)) ring) center"
    by (simp only: exponent funpow_add comp_apply)
  show ?thesis using agreement split
    by (simp only: blocks double_reverse_power_shift[OF rule])
qed

theorem double_reverse_finite_three_phase_source:
  fixes step :: "(int \<Rightarrow> nat) \<Rightarrow> int \<Rightarrow> nat"
  assumes rule: "\<And>x i. step x i = double_reverse_t2_digit (x (i-1)) (x i) (x (i+1))"
      and nonempty: "word \<noteq> []"
      and checked: "\<And>i. 0 \<le> i \<Longrightarrow> i < int (length word) \<Longrightarrow>
        (step ^^ 3) (double_reverse_cyclic_word word) i =
          double_reverse_cyclic_word word (i+shift)"
      and halo: "\<And>i. abs (i-center) \<le> int (3*q+r) \<Longrightarrow>
        source i = double_reverse_cyclic_word word i"
  shows "(step ^^ (3*q+r)) source center =
    (step ^^ r) (double_reverse_cyclic_word word) (center + int q*shift)"
  by (rule double_reverse_three_phase_source[OF rule
        double_reverse_finite_three_miter[OF rule nonempty checked] halo])

definition double_reverse_centered_step :: "(int \<Rightarrow> nat) \<Rightarrow> int \<Rightarrow> nat" where
  "double_reverse_centered_step x i =
    double_reverse_t2_digit (x (i-1)) (x i) (x (i+1))"

lemma double_reverse_three_phase_remainders:
  "(double_reverse_centered_step ^^ 0) x i = x i"
  "(double_reverse_centered_step ^^ 1) x i =
    double_reverse_t2_digit (x (i-1)) (x i) (x (i+1))"
  "(double_reverse_centered_step ^^ 2) x i =
    double_reverse_t2_digit
      (double_reverse_t2_digit (x (i-2)) (x (i-1)) (x i))
      (double_reverse_t2_digit (x (i-1)) (x i) (x (i+1)))
      (double_reverse_t2_digit (x i) (x (i+1)) (x (i+2)))"
  by (simp_all add: numeral_2_eq_2 funpow_Suc_right double_reverse_centered_step_def algebra_simps)

theorem double_reverse_checked_three_phase_readout:
  assumes nonempty: "word \<noteq> []"
      and checked: "\<And>i. 0 \<le> i \<Longrightarrow> i < int (length word) \<Longrightarrow>
        (double_reverse_centered_step ^^ 3) (double_reverse_cyclic_word word) i =
          double_reverse_cyclic_word word (i+shift)"
      and halo: "\<And>i. abs (i-center) \<le> int (3*q+r) \<Longrightarrow>
        source i = double_reverse_cyclic_word word i"
  shows "(double_reverse_centered_step ^^ (3*q+r)) source center =
    (double_reverse_centered_step ^^ r) (double_reverse_cyclic_word word)
      (center + int q*shift)"
  by (rule double_reverse_finite_three_phase_source[OF _ nonempty checked halo])
    (simp add: double_reverse_centered_step_def)

theorem double_reverse_checked_three_phase_pair:
  assumes left_word: "left \<noteq> []" and right_word: "right \<noteq> []"
      and left_checked: "\<And>i. 0 \<le> i \<Longrightarrow> i < int (length left) \<Longrightarrow>
        (double_reverse_centered_step ^^ 3) (double_reverse_cyclic_word left) i =
          double_reverse_cyclic_word left (i+left_shift)"
      and right_checked: "\<And>i. 0 \<le> i \<Longrightarrow> i < int (length right) \<Longrightarrow>
        (double_reverse_centered_step ^^ 3) (double_reverse_cyclic_word right) i =
          double_reverse_cyclic_word right (i+right_shift)"
      and left_halo: "\<And>i. abs (i-left_center) \<le> int (3*q+r) \<Longrightarrow>
        left_source i = double_reverse_cyclic_word left i"
      and right_halo: "\<And>i. abs (i-(right_center+right_births-left_births)) \<le> int (3*q+r) \<Longrightarrow>
        right_source i = double_reverse_cyclic_word right i"
  shows "((double_reverse_centered_step ^^ (3*q+r)) left_source left_center,
          (double_reverse_centered_step ^^ (3*q+r)) right_source
            (right_center+right_births-left_births)) =
         ((double_reverse_centered_step ^^ r) (double_reverse_cyclic_word left)
            (left_center+int q*left_shift),
          (double_reverse_centered_step ^^ r) (double_reverse_cyclic_word right)
            (right_center+right_births-left_births+int q*right_shift))"
  using double_reverse_checked_three_phase_readout[OF left_word left_checked left_halo]
    double_reverse_checked_three_phase_readout[OF right_word right_checked right_halo]
  by simp

ML \<open>
  val checked = @{thms double_reverse_three_phase_remainders
    double_reverse_checked_three_phase_readout double_reverse_checked_three_phase_pair};
  val _ = if null (Thm_Deps.all_oracles checked) then () else error "three-phase source depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked then error "three-phase source has skipped proofs" else ();
\<close>

end
