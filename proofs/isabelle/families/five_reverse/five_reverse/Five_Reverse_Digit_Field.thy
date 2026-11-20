theory Five_Reverse_Digit_Field
  imports Five_Reverse_Mod45
begin

text \<open>
The variable-width field concatenates the decimal words for 5 times each
source digit.  This theory proves its two independent congruence laws and
the resulting mod-225 successor equation.  The quotient forgets the
individual carry and parity ports of the full word.
\<close>

definition five_digit_block_width :: "nat \<Rightarrow> nat" where
  "five_digit_block_width d = (if 5 * d < 10 then 1 else 2)"

function five_digit_field :: "nat \<Rightarrow> nat" where
  "five_digit_field n =
    (if n < 10 then 5 * n else
      five_digit_field (n div 10) *
        10^(five_digit_block_width (n mod 10)) + 5 * (n mod 10))"
  by pat_completeness auto

termination
  by (relation "measure id") auto

(* Keep recursive evaluation explicit.  Global simplifier expansion turns
   symbolic digit-field goals into a traversal of the complete source word. *)
declare five_digit_field.simps[simp del]

lemma five_digit_field_equation:
  "five_digit_field n =
    (if n < 10 then 5 * n else
      five_digit_field (n div 10) *
        10^(five_digit_block_width (n mod 10)) + 5 * (n mod 10))"
  by (rule five_digit_field.simps)

lemma five_digit_block_width_pos [simp]:
  "0 < five_digit_block_width d"
  by (simp add: five_digit_block_width_def)

lemma five_digit_block_width_le_two [simp]:
  "five_digit_block_width d \<le> 2"
  by (simp add: five_digit_block_width_def)

lemma five_digit_field_mod_five:
  "five_digit_field n mod 5 = 0"
proof (induction n rule: less_induct)
  case (less n)
  show ?case
  proof (cases "n < 10")
    case True
    have equation: "five_digit_field n =
        (if n < 10 then 5*n else
          five_digit_field (n div 10) *
            10^(five_digit_block_width (n mod 10)) + 5*(n mod 10))"
      by (rule five_digit_field_equation)
    then show ?thesis using True by simp
  next
    case False
    let ?q = "n div 10"
    let ?d = "n mod 10"
    have q_less: "?q < n" using False by simp
    have prefix: "five_digit_field ?q mod 5 = 0"
      by (rule less.IH[OF q_less])
    have equation:
      "five_digit_field n =
        five_digit_field ?q * 10^(five_digit_block_width ?d) + 5 * ?d"
    proof -
      have unfolded: "five_digit_field n =
        (if n < 10 then 5*n else
          five_digit_field ?q * 10^(five_digit_block_width ?d) + 5*?d)"
        by (rule five_digit_field_equation)
      show ?thesis using unfolded False by simp
    qed
    have product:
      "(five_digit_field ?q * 10^(five_digit_block_width ?d)) mod 5 = 0"
    proof -
      have congruent:
        "(five_digit_field ?q * 10^(five_digit_block_width ?d)) mod 5 =
          (0 * 10^(five_digit_block_width ?d)) mod 5"
        by (rule mod_mult_cong) (use prefix in simp_all)
      show ?thesis using congruent by simp
    qed
    have sum:
      "(five_digit_field ?q * 10^(five_digit_block_width ?d) + 5*?d) mod 5 =
        ((five_digit_field ?q * 10^(five_digit_block_width ?d)) mod 5 +
          (5*?d) mod 5) mod 5"
      by (rule mod_add_eq[symmetric])
    show ?thesis using equation product sum by simp
  qed
qed

lemma five_digit_field_mod_nine:
  "five_digit_field n mod 9 = (5 * n) mod 9"
proof (induction n rule: less_induct)
  case (less n)
  show ?case
  proof (cases "n < 10")
    case True
    have equation: "five_digit_field n =
        (if n < 10 then 5*n else
          five_digit_field (n div 10) *
            10^(five_digit_block_width (n mod 10)) + 5*(n mod 10))"
      by (rule five_digit_field_equation)
    then show ?thesis using True by simp
  next
    case False
    let ?q = "n div 10"
    let ?d = "n mod 10"
    let ?w = "five_digit_block_width ?d"
    have q_less: "?q < n" using False by simp
    have prefix: "five_digit_field ?q mod 9 = (5 * ?q) mod 9"
      by (rule less.IH[OF q_less])
    have power: "(10::nat)^?w mod 9 = 1"
      by (simp add: decimal_ten_power_mod_nine)
    have equation:
      "five_digit_field n = five_digit_field ?q * 10^?w + 5 * ?d"
    proof -
      have unfolded: "five_digit_field n =
        (if n < 10 then 5*n else five_digit_field ?q * 10^?w + 5*?d)"
        by (rule five_digit_field_equation)
      show ?thesis using unfolded False by simp
    qed
    have source: "n = 10 * ?q + ?d"
      by (simp add: div_mult_mod_eq mult.commute)
    have source_mod:
      "(5 * n) mod 9 = (5 * (10 * ?q + ?d)) mod 9"
      by (rule arg_cong[where f="\<lambda>r. (5*r) mod 9"]) (rule source)
    have product_residue:
      "(five_digit_field ?q * 10^?w) mod 9 = (5*?q) mod 9"
    proof -
      have congruent:
        "(five_digit_field ?q * 10^?w) mod 9 = ((5*?q)*1) mod 9"
        by (rule mod_mult_cong) (use prefix power in simp_all)
      show ?thesis using congruent by simp
    qed
    have field_step:
      "five_digit_field n mod 9 = ((5*?q) mod 9 + (5*?d) mod 9) mod 9"
    proof -
      have joined:
        "(five_digit_field ?q * 10^?w + 5*?d) mod 9 =
          ((five_digit_field ?q * 10^?w) mod 9 + (5*?d) mod 9) mod 9"
        by (rule mod_add_cong) simp_all
      show ?thesis using equation joined product_residue by simp
    qed
    have source_product:
      "(50*?q) mod 9 = (5*?q) mod 9"
      by (rule mod_mult_cong) simp_all
    have source_sum:
      "(5*(10*?q+?d)) mod 9 =
        ((50*?q) mod 9 + (5*?d) mod 9) mod 9"
    proof -
      have expanded: "5*(10*?q+?d) = 50*?q+5*?d"
        by (simp only: distrib_left; simp add: mult.assoc[symmetric])
      show ?thesis unfolding expanded by (rule mod_add_cong) simp_all
    qed
    show ?thesis
    proof -
      have source_step:
        "(5*n) mod 9 = ((5*?q) mod 9 + (5*?d) mod 9) mod 9"
        using source_mod source_sum by (simp only: source_product)
      show ?thesis by (simp only: field_step source_step)
    qed
  qed
qed

lemma five_digit_field_mod_twentyfive:
  "five_digit_field n mod 25 = 5 * (n mod 5)"
proof (induction n rule: less_induct)
  case (less n)
  show ?case
  proof (cases "n < 10")
    case True
    have equation: "five_digit_field n =
        (if n < 10 then 5*n else
          five_digit_field (n div 10) *
            10^(five_digit_block_width (n mod 10)) + 5*(n mod 10))"
      by (rule five_digit_field_equation)
    have scaled: "(5 * n) mod (5 * 5) = 5 * (n mod 5)"
      by (rule mod_mult_mult1)
    show ?thesis using True equation scaled by simp
  next
    case False
    let ?q = "n div 10"
    let ?d = "n mod 10"
    let ?w = "five_digit_block_width ?d"
    have q_less: "?q < n" using False by simp
    have prefix: "five_digit_field ?q mod 5 = 0"
      by (rule five_digit_field_mod_five)
    have d_bound: "?d < 10" by simp
    have equation:
      "five_digit_field n = five_digit_field ?q * 10^?w + 5 * ?d"
    proof -
      have unfolded: "five_digit_field n =
        (if n < 10 then 5*n else five_digit_field ?q * 10^?w + 5*?d)"
        by (rule five_digit_field_equation)
      show ?thesis using unfolded False by simp
    qed
    have prefix25:
      "(five_digit_field ?q * 10^?w) mod 25 = 0"
    proof -
      have five_divisor: "5 dvd five_digit_field ?q"
        using prefix by (simp add: mod_eq_0_iff_dvd)
      then obtain a where field: "five_digit_field ?q = 5*a"
        by (elim dvdE)
      have width_cases: "?w = 1 \<or> ?w = 2"
        using d_bound by (simp add: five_digit_block_width_def; arith)
      have ten_divisor: "(10::nat) dvd (10::nat)^?w"
        using width_cases by auto
      then obtain b where power: "(10::nat)^?w = 10*b"
        by (elim dvdE)
      have product: "five_digit_field ?q * 10^?w = 50*(a*b)"
        by (simp add: field power algebra_simps)
      have "25 dvd five_digit_field ?q * 10^?w"
        unfolding product by simp
      then show ?thesis by (simp add: mod_eq_0_iff_dvd)
    qed
    have prefix_step:
      "five_digit_field n mod 25 = 5 * ?d mod 25"
    proof -
      have joined:
        "(five_digit_field ?q * 10^?w + 5*?d) mod 25 =
          ((five_digit_field ?q * 10^?w) mod 25 + (5*?d) mod 25) mod 25"
        by (rule mod_add_cong) simp_all
      show ?thesis using equation joined prefix25 by simp
    qed
    have source: "n = 10*?q + ?d" by simp
    have five_dvd_ten: "(5::nat) dvd 10" by simp
    have digit_residue: "?d mod 5 = n mod 5"
      by (rule mod_mod_cancel[OF five_dvd_ten])
    have scaled: "(5 * ?d) mod (5 * 5) = 5 * (?d mod 5)"
      by (rule mod_mult_mult1)
    show ?thesis using prefix_step scaled digit_residue by simp
  qed
qed

lemma five_digit_field_five_reverse_mod_nine:
  "five_digit_field (five_reverse_step n) mod 9 =
    (5 * five_digit_field n) mod 9"
proof -
  have left:
    "five_digit_field (five_reverse_step n) mod 9 =
      (5 * five_reverse_step n) mod 9"
    by (rule five_digit_field_mod_nine)
  have right:
    "(5 * five_digit_field n) mod 9 = (25 * n) mod 9"
  proof -
    have field_residue:
      "five_digit_field n mod 9 = (5*n) mod 9"
      by (rule five_digit_field_mod_nine)
    have transport:
      "(5 * five_digit_field n) mod 9 =
        (5 * ((5*n) mod 9)) mod 9"
      by (rule mod_mult_cong) (use field_residue in simp_all)
    show ?thesis using transport
      by (simp add: mod_mult_right_eq mult.assoc[symmetric])
  qed
  have reverse_product:
    "(5 * decimal_reverse n) mod 9 = (5*n) mod 9"
    by (rule mod_mult_cong) (simp_all add: decimal_reverse_mod_nine)
  have source_product: "25*n = 5*(5*n)"
    by (simp add: mult.assoc[symmetric])
  have source:
    "(5 * five_reverse_step n) mod 9 = (25 * n) mod 9"
  proof -
    show ?thesis
      unfolding five_reverse_step_def source_product
      by (rule mod_mult_cong) (rule refl, rule reverse_product)
  qed
  show ?thesis using left right source by simp
qed

lemma five_digit_field_five_reverse_mod_twentyfive:
  "five_digit_field (five_reverse_step n) mod 25 = 0"
  using five_digit_field_mod_twentyfive[of "five_reverse_step n"]
  unfolding five_reverse_step_def by simp

lemma five_digit_field_five_reverse_mod225:
  "five_digit_field (five_reverse_step n) mod 225 =
    (5 * five_digit_field n) mod 225"
proof -
  let ?left = "five_digit_field (five_reverse_step n)"
  let ?right = "5 * five_digit_field n"
  have left9: "?left mod 9 = ?right mod 9"
    by (rule five_digit_field_five_reverse_mod_nine)
  have left25: "?left mod 25 = ?right mod 25"
  proof -
    have "?left mod 25 = 0"
      by (rule five_digit_field_five_reverse_mod_twentyfive)
    moreover have "?right mod 25 = 0"
    proof -
      have residue: "five_digit_field n mod 5 = 0"
        by (rule five_digit_field_mod_five)
      have divisor: "5 dvd five_digit_field n"
        using residue by (simp add: mod_eq_0_iff_dvd)
      then obtain a where field: "five_digit_field n = 5*a"
        by (elim dvdE)
      show ?thesis unfolding field by simp
    qed
    ultimately show ?thesis by simp
  qed
  have crt:
    "?left mod (9 * 25) = ?right mod (9 * 25) \<longleftrightarrow>
      (?left mod 9 = ?right mod 9 \<and> ?left mod 25 = ?right mod 25)"
  proof -
    let ?difference = "nat \<bar>int ?left-int ?right\<bar>"
    have whole:
      "?left mod (9 * 25) = ?right mod (9 * 25) \<longleftrightarrow>
        9 * 25 dvd ?difference"
      by (rule mod_eq_iff_dvd_symdiff_nat)
    have first:
      "?left mod 9 = ?right mod 9 \<longleftrightarrow> 9 dvd ?difference"
      by (rule mod_eq_iff_dvd_symdiff_nat)
    have second:
      "?left mod 25 = ?right mod 25 \<longleftrightarrow> 25 dvd ?difference"
      by (rule mod_eq_iff_dvd_symdiff_nat)
    have product:
      "(9::nat) * 25 dvd ?difference \<longleftrightarrow>
        ((9::nat) dvd ?difference \<and> (25::nat) dvd ?difference)"
    proof
      assume divided: "(9::nat) * 25 dvd ?difference"
      have first_divisor: "(9::nat) dvd 9 * 25" by simp
      have second_divisor: "(25::nat) dvd 9 * 25"
        by (simp add: mult.commute)
      show "(9::nat) dvd ?difference \<and> (25::nat) dvd ?difference"
        using dvd_trans[OF first_divisor divided]
          dvd_trans[OF second_divisor divided] by blast
    next
      assume factors:
        "(9::nat) dvd ?difference \<and> (25::nat) dvd ?difference"
      have coprime: "coprime (9::nat) 25"
        by (simp add: coprime_iff_gcd_eq_1 gcd_nat.simps)
      have first_divisor: "(9::nat) dvd ?difference" using factors by blast
      have second_divisor: "(25::nat) dvd ?difference" using factors by blast
      show "(9::nat) * 25 dvd ?difference"
        by (rule divides_mult[OF first_divisor second_divisor coprime])
    qed
    show ?thesis using whole first second product by blast
  qed
  show ?thesis using left9 left25 crt by simp
qed

theorem five_digit_field_orbit_mod225:
  "five_digit_field (five_reverse_orbit ticks seed) mod 225 =
    ((5 ^ ticks) * five_digit_field seed) mod 225"
proof (induction ticks)
  case 0
  show ?case by simp
next
  case (Suc ticks)
  have step:
    "five_digit_field (five_reverse_orbit (Suc ticks) seed) mod 225 =
      (5 * five_digit_field (five_reverse_orbit ticks seed)) mod 225"
    unfolding five_reverse_orbit.simps
    by (rule five_digit_field_five_reverse_mod225)
  have lifted:
    "(5 * five_digit_field (five_reverse_orbit ticks seed)) mod 225 =
      (5 * ((5 ^ ticks) * five_digit_field seed)) mod 225"
    by (rule mod_mult_cong) (rule refl, rule Suc.IH)
  show ?case using step lifted by (simp add: power_Suc mult.assoc)
qed

ML \<open>
  val checked = @{thms five_digit_field_mod_nine five_digit_field_mod_twentyfive
    five_digit_field_five_reverse_mod225 five_digit_field_orbit_mod225};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Five-reverse digit-field power depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked
    then error "Skipped five-reverse digit-field proof" else ();
\<close>

end
