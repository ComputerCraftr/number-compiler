theory Comma_Padic_Event_Transport
  imports Shared_S_Arithmetic.Padic_Event_Action Comma_Arithmetic.Comma_Period_Guard
begin

text \<open>This theory connects the generic prime-adic event observer to the
existing fixed-leading comma recurrence.  The event remains derived data;
its period is local to a guarded sector and is not continued through a seam.\<close>

lemma comma_padic_interval_step_guard_comma_sector:
  assumes sector: "comma_sector f width n"
    and target: "n + delta < (f + 1) * 10^width"
  shows "padic_interval_step_guard (f * 10^width) ((f+1)*10^width) n delta"
  using sector target by (simp add: comma_sector_def padic_interval_step_guard_def)


text \<open>For a comma fixed-leading sector, the existing displacement theorem
gives the additive cycle coordinates used above.  A caller supplies the
checked period closure and the interval guard for all cycle indices under
comparison.  At a Fork, Landmine, or Entry/Near seam the next sector must be
re-certified; this theorem does not continue the old cycle through it.\<close>

lemma comma_padic_fixed_iter_additive_cycle:
  assumes closes: "10 dvd len * f"
  shows "comma_fixed_iter f (k*len+j) d =
    comma_fixed_iter f j d + k * comma_period_displacement f d len"
proof -
  have normalized:
    "comma_period_displacement f (d mod 10) count =
      comma_period_displacement f d count" for count
    by (simp add: comma_period_displacement_def mod_add_left_eq)
  have displacement:
    "comma_period_displacement f d (k*len+j) =
      k * comma_period_displacement f d len + comma_period_displacement f d j"
    by (rule comma_period_displacement_repeated[OF closes])
  show ?thesis
    using comma_fixed_iter_displacement[of f "k*len+j" d]
      comma_fixed_iter_displacement[of f j d] displacement
    by (simp add: normalized algebra_simps)
qed

lemma comma_padic_fixed_iter_cycle_digit:
  assumes closes: "10 dvd len * f"
  shows "comma_fixed_iter f (k*len+j) d mod 10 = comma_fixed_iter f j d mod 10"
proof -
  have multiple: "10 dvd k*len*f"
  proof -
    have "10 dvd k*(len*f)" by (rule dvd_mult[OF closes])
    then show ?thesis by (simp only: mult.assoc)
  qed
  have zero: "(k*len*f) mod 10=0"
    using multiple by (simp add: dvd_eq_mod_eq_0)
  have phase: "(d mod 10 + (k*len+j)*f) mod 10 =
      (d mod 10 + j*f) mod 10"
  proof -
    have expanded: "(k*len+j)*f = j*f + k*len*f"
      by (simp add: algebra_simps)
    have "(d mod 10 + (k*len+j)*f) mod 10 =
        ((d mod 10 + j*f) + k*len*f) mod 10"
      by (simp only: expanded add.assoc)
    also have "... = ((d mod 10 + j*f) + (k*len*f) mod 10) mod 10"
      by (rule mod_add_right_eq[symmetric])
    also have "... = (d mod 10 + j*f) mod 10"
      by (simp only: zero add_0_right)
    finally show ?thesis .
  qed
  show ?thesis
    using comma_fixed_iter_phase[of f "k*len+j" d]
      comma_fixed_iter_phase[of f j d] phase by simp
qed

lemma comma_padic_fixed_iter_cycle_increment:
  assumes closes: "10 dvd len * f"
  shows "10 * (comma_fixed_iter f (k*len+j) d mod 10) + f =
    10 * (comma_fixed_iter f j d mod 10) + f"
  using comma_padic_fixed_iter_cycle_digit[OF closes] by simp

lemma comma_padic_fixed_iter_event_periodic:
  fixes p f len j k d lower upper :: nat
  assumes prime_p: "prime p" and lower_positive: "0 < lower"
    and f_positive: "0 < f" and closes: "10 dvd len * f"
    and displacement_positive: "0 < comma_period_displacement f d len"
    and guarded: "\<And>i. i \<le> padic_cycle_period p
        (multiplicity p (10 * (comma_fixed_iter f j d mod 10) + f))
        (multiplicity p (comma_period_displacement f d len)) \<Longrightarrow>
      padic_interval_step_guard lower upper
        (comma_fixed_iter f ((k+i)*len+j) d)
        (10 * (comma_fixed_iter f ((k+i)*len+j) d mod 10) + f)"
  shows "padic_value_event p (comma_fixed_iter f (k*len+j) d)
      (10 * (comma_fixed_iter f (k*len+j) d mod 10) + f) =
    padic_value_event p
      (comma_fixed_iter f
        ((k + padic_cycle_period p
          (multiplicity p (10 * (comma_fixed_iter f j d mod 10) + f))
          (multiplicity p (comma_period_displacement f d len)))*len+j) d)
      (10 * (comma_fixed_iter f
        ((k + padic_cycle_period p
          (multiplicity p (10 * (comma_fixed_iter f j d mod 10) + f))
          (multiplicity p (comma_period_displacement f d len)))*len+j) d mod 10) + f)"
proof -
  let ?base = "comma_fixed_iter f j d"
  let ?delta = "10 * (?base mod 10) + f"
  let ?displacement = "comma_period_displacement f d len"
  let ?period = "padic_cycle_period p (multiplicity p ?delta)
    (multiplicity p ?displacement)"
  have delta_positive: "0 < ?delta"
    using f_positive by simp
  have current_state:
    "comma_fixed_iter f (k*len+j) d = ?base + k*?displacement"
    by (rule comma_padic_fixed_iter_additive_cycle[OF closes])
  have later_state:
    "comma_fixed_iter f ((k+?period)*len+j) d =
      ?base + (k+?period)*?displacement"
    by (rule comma_padic_fixed_iter_additive_cycle[OF closes])
  have guarded_additive:
    "\<And>i. i \<le> ?period \<Longrightarrow>
      padic_interval_step_guard lower upper
        (?base + (k+i)*?displacement) ?delta"
  proof -
    fix i
    assume i_bound: "i \<le> ?period"
    have state:
      "comma_fixed_iter f ((k+i)*len+j) d = ?base + (k+i)*?displacement"
      by (rule comma_padic_fixed_iter_additive_cycle[OF closes])
    have digit:
      "comma_fixed_iter f ((k+i)*len+j) d mod 10 = ?base mod 10"
      by (rule comma_padic_fixed_iter_cycle_digit[OF closes])
    have increment:
      "10 * (comma_fixed_iter f ((k+i)*len+j) d mod 10) + f = ?delta"
      using digit by simp
    show "padic_interval_step_guard lower upper
        (?base + (k+i)*?displacement) ?delta"
      using guarded[OF i_bound] state increment by simp
  qed
  have additive_event:
    "padic_value_event p (?base + k*?displacement) ?delta =
      padic_value_event p (?base + (k+?period)*?displacement) ?delta"
    by (rule padic_event_periodic_on_guarded_additive_cycle
      [OF prime_p lower_positive delta_positive displacement_positive guarded_additive])
  have current_digit:
    "comma_fixed_iter f (k*len+j) d mod 10 = ?base mod 10"
    by (rule comma_padic_fixed_iter_cycle_digit[OF closes])
  have later_digit:
    "comma_fixed_iter f ((k+?period)*len+j) d mod 10 = ?base mod 10"
    by (rule comma_padic_fixed_iter_cycle_digit[OF closes])
  show ?thesis using additive_event current_state later_state current_digit later_digit by simp
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_padic_interval_step_guard_comma_sector
      comma_padic_fixed_iter_additive_cycle comma_padic_fixed_iter_cycle_digit
      comma_padic_fixed_iter_cycle_increment comma_padic_fixed_iter_event_periodic})
    then () else error "Comma prime-adic transport proof depends on an oracle";
\<close>
end
