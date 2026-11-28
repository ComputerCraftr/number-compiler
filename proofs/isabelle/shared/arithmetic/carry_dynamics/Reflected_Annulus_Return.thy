theory Reflected_Annulus_Return
  imports Reflected_Wave_Readout
begin

definition uniform_reflected_digit :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "uniform_reflected_digit m d = m * (d mod (10 div m)) + d div (10 div m)"

lemma uniform_six:
  assumes "m \<in> {2,5}" "d < 10"
  shows "(uniform_reflected_digit m ^^ 6) d = d"
proof -
  have rows: "uniform_reflected_digit 2 0 = 0"
    "uniform_reflected_digit 2 1 = 2"
    "uniform_reflected_digit 2 2 = 4"
    "uniform_reflected_digit 2 3 = 6"
    "uniform_reflected_digit 2 4 = 8"
    "uniform_reflected_digit 2 5 = 1"
    "uniform_reflected_digit 2 6 = 3"
    "uniform_reflected_digit 2 7 = 5"
    "uniform_reflected_digit 2 8 = 7"
    "uniform_reflected_digit 2 9 = 9"
    "uniform_reflected_digit 5 0 = 0"
    "uniform_reflected_digit 5 1 = 5"
    "uniform_reflected_digit 5 2 = 1"
    "uniform_reflected_digit 5 3 = 6"
    "uniform_reflected_digit 5 4 = 2"
    "uniform_reflected_digit 5 5 = 7"
    "uniform_reflected_digit 5 6 = 3"
    "uniform_reflected_digit 5 7 = 8"
    "uniform_reflected_digit 5 8 = 4"
    "uniform_reflected_digit 5 9 = 9"
    by (simp_all add: uniform_reflected_digit_def)
  have digits: "d = 0 \<or> d = 1 \<or> d = 2 \<or> d = 3 \<or> d = 4 \<or> d = 5 \<or> d = 6 \<or> d = 7 \<or> d = 8 \<or> d = 9" using assms(2) by arith
  have six: "(6::nat) = Suc (Suc (Suc (Suc (Suc (Suc 0)))))" by simp
  from digits assms(1) show ?thesis by (subst six; auto simp: rows[unfolded One_nat_def] o_def)
qed

lemma uniform_blocks:
  assumes "m \<in> {2,5}" "d < 10"
  shows "(uniform_reflected_digit m ^^ (6 * k)) d = d"
  by (induction k) (simp_all add: funpow_add mult_Suc_right uniform_six[OF assms])

lemma uniform_physical_clock:
  "reflected_single_run (reflected_alternating_gate m) n (\<lambda>_. d) i =
   (uniform_reflected_digit m ^^ n) d"
  by (induction n arbitrary: i) (simp_all add: reflected_alternating_gate_def
      uniform_reflected_digit_def add.commute)

theorem uniform_reflected_annulus:
  assumes radix: "m \<in> {2,5}" "d < 10"
    and halo: "\<And>j. i - int n \<le> j \<Longrightarrow> j \<le> i \<Longrightarrow> source j = d"
  shows "reflected_single_run (reflected_alternating_gate m) n source i =
    (uniform_reflected_digit m ^^ (n mod 6)) d"
proof -
  have split: "n = n mod 6 + 6 * (n div 6)" by presburger
  have eq: "(uniform_reflected_digit m ^^ n) d =
    (uniform_reflected_digit m ^^ (n mod 6)) d"
    by (subst split, subst funpow_add, simp add: uniform_blocks[OF radix])
  have local: "reflected_single_run (reflected_alternating_gate m) n source i =
    reflected_single_run (reflected_alternating_gate m) n (\<lambda>_. d) i"
    by (rule reflected_single_run_locality) (rule halo)
  show ?thesis using local eq by (simp add: uniform_physical_clock)
qed

definition reflected_cyclic_at :: "'a list \<Rightarrow> int \<Rightarrow> 'a" where
  "reflected_cyclic_at w j = w ! nat (j mod int (length w))"

theorem reflected_motif_physical_ray:
  fixes a b origin shift i :: int
  assumes word: "w \<noteq> []" and shift: "0 \<le> shift" "shift \<le> 2"
    and source: "\<And>j. a \<le> j \<Longrightarrow> j < b \<Longrightarrow> src j = reflected_cyclic_at w (j-origin)"
    and slots: "\<And>k. 0 \<le> k \<Longrightarrow> k < int (length w) \<Longrightarrow>
      reflected_relative_two (reflected_source_two_gate m) (reflected_cyclic_at w) k =
        reflected_cyclic_at w (k-shift)"
    and cone: "a+2*int n \<le> i" "i < b"
  shows "reflected_single_run (reflected_alternating_gate m) (2*n) src i =
    reflected_cyclic_at w (i - int n * shift - origin)"
proof -
  let ?p = "int (length w)"
  have pos: "0 < ?p" using word by simp
  have wrap: "reflected_cyclic_at w (j mod ?p - z) = reflected_cyclic_at w (j-z)" for j z
    by (simp add: reflected_cyclic_at_def mod_diff_left_eq)
  have step: "reflected_relative_two (reflected_source_two_gate m) src j = src (j-shift)"
    if lo: "a+2 \<le> j" and hi: "j<b" for j
  proof -
    let ?x = "j-origin"
    have match: "reflected_relative_two (reflected_source_two_gate m) (reflected_cyclic_at w)
        (?x mod ?p) = reflected_cyclic_at w (?x mod ?p - shift)"
      by (rule slots) (use pos in simp_all)
    have cell: "src (j-z) = reflected_cyclic_at w (?x-z)" if "0\<le>z" "z\<le>2" for z
      using source[of "j-z"] lo hi that by (simp add: algebra_simps; linarith)
    show ?thesis using match cell[of 2] cell[of 1] cell[of 0] cell[OF shift]
      by (simp add: reflected_relative_two_def wrap reflected_cyclic_at_def mod_diff_left_eq)
  qed
  have lower: "0 \<le> int n * shift" by (rule mult_nonneg_nonneg) (simp_all add: shift)
  have upper: "int n * shift \<le> int n * 2" by (rule mult_left_mono) (simp_all add: shift)
  have bound: "a \<le> i - int n * shift" "i-int n*shift < b" using cone lower upper by linarith+
  show ?thesis using reflected_single_run_even_relative[OF shift step cone] source[OF bound] by simp
qed

text \<open>In the centered chart a pair update shifts the storage index by one.
The signed ray offset can already include the reflected width drift R-L.
Every observed digit (including the previous and next sheets of a defect)
has its own time, ray and halo obligation.\<close>

theorem reflected_annulus_observation:
  fixes shift ray :: "'port \<Rightarrow> int" and tick :: "'port \<Rightarrow> nat"
  assumes shifts: "\<And>p. p \<in> set ports \<Longrightarrow> 0 \<le> shift p"
    "\<And>p. p \<in> set ports \<Longrightarrow> shift p \<le> 2"
    and miter: "\<And>p j. p \<in> set ports \<Longrightarrow> lo p + 2 \<le> j \<Longrightarrow> j < hi p \<Longrightarrow>
       reflected_relative_two (reflected_source_two_gate m) source j = source (j - shift p)"
    and halo: "\<And>p. p \<in> set ports \<Longrightarrow> lo p + int (tick p) \<le> ray p"
      "\<And>p. p \<in> set ports \<Longrightarrow> ray p + int (tick p) < hi p"
  shows "observe (map (\<lambda>p. reflected_single_run (reflected_alternating_gate m)
           (2 * tick p) source (ray p + int (tick p))) ports) =
    observe (map (\<lambda>p. source (ray p + int (tick p) * (1 - shift p))) ports)"
proof -
  have point: "reflected_single_run (reflected_alternating_gate m) (2 * tick p)
      source (ray p + int (tick p)) = source (ray p + int (tick p) * (1 - shift p))"
    if member: "p \<in> set ports" for p
  proof -
    have margin: "lo p + 2 * int (tick p) \<le> ray p + int (tick p)"
      using halo(1)[OF member] by linarith
    show ?thesis using reflected_single_run_even_relative[OF shifts(1)[OF member]
      shifts(2)[OF member] miter[OF member] margin halo(2)[OF member]]
      by (simp add: algebra_simps)
  qed
  show ?thesis by (intro arg_cong[where f=observe] map_cong) (auto intro: point)
qed

text \<open>On a 2rev10 four-tick one-birth sheet, retain both threshold
masks in J = 4 C0 + C1. Dividing the signed lower remainder before
reducing the next digit preserves a possible negative carry.\<close>

lemma four_tick_laurent_annulus_digit:
  fixes x c0 c1 scale :: int
  assumes "0 < scale"
  defines "y \<equiv> 160*x - 198*(4*c0+c1)"
  shows "y div scale mod 10 =
    (160*(x div scale) + (160*(x mod scale)-198*(4*c0+c1)) div scale) mod 10"
proof -
  have split: "x div scale * scale + x mod scale = x" by simp
  have lifted: "y = (160*(x div scale))*scale + (160*(x mod scale)-198*(4*c0+c1))"
    proof -
    have "y = 160*(x div scale * scale + x mod scale) - 198*(4*c0+c1)"
      unfolding y_def by (simp only: split)
    also have "... = (160*(x div scale))*scale + (160*(x mod scale)-198*(4*c0+c1))"
      by (simp only: algebra_simps)
    finally show ?thesis .
  qed
  show ?thesis unfolding lifted using assms(1) by simp
qed

theorem uniform_annulus_physical_readout:
  fixes t :: nat and raw :: "nat list"
  assumes mult: "m=2 \<or> m=5" and digits: "reflected_decimal seed"
    and canonical: "reflected_trim_high seed = seed" and digit: "d<10"
    and inlet: "\<And>j. a \<le> j \<Longrightarrow> j < b \<Longrightarrow> reflected_signed_source (rev seed) j = d"
  defines "raw \<equiv> reflected_me_word m (Suc t) (rev seed)"
    and "patched \<equiv> map (\<lambda>i. if a + int (Suc t) \<le> int i \<and> int i < b
      then (uniform_reflected_digit m ^^ (Suc t mod 6)) d else raw ! i) [0..<length raw]"
  shows "reflected_msf_value (reflected_wave_physical_readout m (Suc t) patched) =
    decimal_lsd_value ((reflected_physical_word m ^^ Suc t) seed)"
proof -
  have radix: "m \<in> {2,5}" using mult by auto
  have cell: "raw ! i = (uniform_reflected_digit m ^^ (Suc t mod 6)) d"
    if bound: "i < length raw" and inside: "a + int (Suc t) \<le> int i" "int i < b" for i
  proof -
    have halo: "reflected_signed_source (rev seed) j = d"
      if "int i - int (Suc t) \<le> j" "j \<le> int i" for j
      using inside that by (intro inlet; linarith)
    have exact: "reflected_single_run (reflected_alternating_gate m) (Suc t)
         (reflected_signed_source (rev seed)) (int i) = raw ! i"
      using reflected_single_run_me_word[OF mult, of "rev seed" "Suc t" "int i"] digits bound
      by (simp add: raw_def reflected_signed_source_def reflected_padded_source_def list_all_iff)
    show ?thesis using exact[symmetric] uniform_reflected_annulus[where i="int i" and n="Suc t" and source="reflected_signed_source (rev seed)", OF radix digit halo] by (rule trans)
  qed
  have same: "patched = raw"
    by (rule nth_equalityI; auto simp: patched_def cell)
  show ?thesis using reflected_wave_source_readout[OF mult digits canonical, of t]
    by (simp only: same raw_def)
qed

ML \<open>
  val checked = @{thms uniform_reflected_annulus reflected_annulus_observation four_tick_laurent_annulus_digit uniform_annulus_physical_readout reflected_motif_physical_ray};
  val _ = if null (Thm_Deps.all_oracles checked) andalso
    not (Thm_Deps.has_skip_proof checked) then () else error "Unchecked annulus return";
\<close>
end
