theory Mahler_Powered_Graph_Refinement
  imports Mahler_Exact_Even_Event_Threshold
begin

text \<open>The selected graph port keeps the centered integer modulo twenty,
which contains both its decimal units digit and its integer tens parity.
The fractional coordinate is retained separately as a half-open interval.
This finite example is the source-admitted two-copy 60/40 row used by the
publisher. It does not assert a future for an arbitrary graph port.\<close>


text \<open>Two sources separated by twenty complete dyadic cylinders have
the same ordered integer digit and tens-parity ports, as well as the same
fractional phase at every earlier position.\<close>

theorem mahler_graph_ordered_port_source_transport:
  assumes time: "j \<le> N"
  shows "mahler_orbit (D + (20*k)*2^N) j mod 20 =
      mahler_orbit D j mod 20"
    and "fractional_endpoint (D + (20*k)*2^N) j t =
      fractional_endpoint D j t"
    and "cylinder_guard (D + (20*k)*2^N) N t =
      cylinder_guard D N t"
proof -
  have orbit:
    "mahler_orbit (D + (20*k)*2^N) j =
      mahler_orbit D j + (20*k)*2^(N-j)*3^j"
    by (rule moving_source_cylinder[OF time])
  have factor: "(20*k)*2^(N-j)*3^j = (k*2^(N-j)*3^j)*20"
    by (simp add: algebra_simps)
  show "mahler_orbit (D + (20*k)*2^N) j mod 20 =
      mahler_orbit D j mod 20"
    by (simp only: orbit factor mod_mult_self1)
  have scale:
    "(2::real)^N*(3/2)^j = of_nat (2^(N-j)*3^j)"
    by (rule dyadic_scale_transport[OF time])
  show "fractional_endpoint (D + (20*k)*2^N) j t =
      fractional_endpoint D j t"
    unfolding fractional_endpoint_def orbit
    using scale by (simp add: of_nat_mult algebra_simps)
  show "cylinder_guard (D + (20*k)*2^N) N t =
      cylinder_guard D N t"
    using guard_high_fiber_translation[of D N "20*k" t]
    by (simp add: mult.commute)
qed


lemma mahler_graph_even_port_swap:
  fixes x y :: nat
  assumes "x mod 4 = 0" "y mod 4 = 0" "2*y = 3*x"
      and "x mod 20 = 16 \<or> x mod 20 = 4"
  shows "(x mod 20 = 16 \<and> y mod 20 = 4) \<or>
    (x mod 20 = 4 \<and> y mod 20 = 16)"
proof -
  let ?r = "y mod 20"
  have bound: "?r < 20" by simp
  have four: "?r mod 4 = 0" using assms(2) by (simp add: mod_mod_cancel)
  have equation: "(2*?r) mod 20 = (3*(x mod 20)) mod 20"
    by (simp only: mod_mult_right_eq assms(3))
  obtain r where repr: "r = ?r" by blast
  have rbound: "r < 20" using bound repr by simp
  have rf: "r mod 4 = 0" using four repr by simp
  have re: "(2*r) mod 20 = (3*(x mod 20)) mod 20"
    using equation repr by simp
  have domain: "r = 0 \<or> r = 1 \<or> r = 2 \<or> r = 3 \<or> r = 4 \<or>
      r = 5 \<or> r = 6 \<or> r = 7 \<or> r = 8 \<or> r = 9 \<or>
      r = 10 \<or> r = 11 \<or> r = 12 \<or> r = 13 \<or> r = 14 \<or>
      r = 15 \<or> r = 16 \<or> r = 17 \<or> r = 18 \<or> r = 19"
    using rbound by arith
  have result: "(x mod 20 = 16 \<and> r = 4) \<or>
      (x mod 20 = 4 \<and> r = 16)"
    using domain rf re assms(4) by auto
  show ?thesis using result repr by simp
qed

text \<open>A zero-word power is selected by the complete dyadic source
cylinder. The two additional bits retain the final integer tens port. The
fractional bound retains every intermediate tenths port by monotonicity.\<close>

theorem mahler_graph_powered_even_row:
  fixes u m :: nat and t :: real
  defines "D \<equiv> 2^(2*m+2)*u"
  assumes port: "D mod 20 = 16 \<or> D mod 20 = 4"
      and tail: "0 \<le> t" "(3/2)^(2*m)*t < 1/10"
  shows "cylinder_guard D (2*m) t"
    and "mahler_orbit D (2*m) = 4*u*3^(2*m)"
    and "fractional_endpoint D (2*m) t = (3/2)^(2*m)*t"
    and "\<And>j. j \<le> 2*m \<Longrightarrow>
      mahler_orbit D j mod 20 =
        (if even j then D mod 20 else 20 - D mod 20)"
    and "\<And>j. j \<le> 2*m \<Longrightarrow>
      0 \<le> fractional_endpoint D j t \<and>
      fractional_endpoint D j t < 1/10"
proof -
  let ?n = "2*m"
  let ?N = "2*m+2"
  have orbit:
    "mahler_orbit D j = u*2^(?N-j)*3^j" if "j \<le> ?N" for j
    unfolding D_def by (rule even_source_run[OF that])
  have fraction:
    "fractional_endpoint D j t = (3/2)^j*t" if "j \<le> ?N" for j
    unfolding D_def by (rule even_run_fraction[OF that])
  have multiple:
    "mahler_orbit D j mod 4 = 0" if "j \<le> ?n" for j
  proof -
    have bound: "2 \<le> ?N-j" using that by arith
    have dvd: "(2::nat)^2 dvd 2^(?N-j)"
      by (rule dvd_power_le) (use bound in simp_all)
    have "4 dvd mahler_orbit D j"
      using dvd orbit[of j] that by auto
    then show ?thesis by (simp add: dvd_eq_mod_eq_0)
  qed
  have step:
    "2 * mahler_orbit D (Suc j) = 3 * mahler_orbit D j"
    if "Suc j \<le> ?n" for j
  proof -
    have div4: "mahler_orbit D j mod 4 = 0"
      by (rule multiple) (use that in arith)
    then have "4 dvd mahler_orbit D j" by (simp add: dvd_eq_mod_eq_0)
    then obtain k where source_form: "mahler_orbit D j = 4*k" by (auto simp: dvd_def)
    show ?thesis using source_form by (simp add: mahler_D_step_def algebra_simps)
  qed
  have ports:
    "mahler_orbit D j mod 20 =
      (if even j then D mod 20 else 20 - D mod 20)" if "j \<le> ?n" for j
    using that
  proof (induction j)
    case 0
    then show ?case by simp
  next
    case (Suc j)
    have previous: "mahler_orbit D j mod 20 =
      (if even j then D mod 20 else 20 - D mod 20)"
      using Suc.IH Suc.prems by simp
    have swap:
      "(mahler_orbit D j mod 20 = 16 \<and>
          mahler_orbit D (Suc j) mod 20 = 4) \<or>
       (mahler_orbit D j mod 20 = 4 \<and>
          mahler_orbit D (Suc j) mod 20 = 16)"
      by (rule mahler_graph_even_port_swap[OF multiple multiple step])
        (use Suc.prems previous port in auto)
    show ?case using swap previous port by (cases "even j") auto
  qed
  have fraction_bounds:
    "0 \<le> fractional_endpoint D j t \<and> fractional_endpoint D j t < 1/10"
    if "j \<le> ?n" for j
  proof -
    have power: "(3/2::real)^j \<le> (3/2)^?n"
      by (rule power_increasing[OF that]) simp
    have "(3/2::real)^j*t \<le> (3/2)^?n*t"
      by (rule mult_right_mono[OF power tail(1)])
    then show ?thesis using tail fraction[of j] that by auto
  qed
  have first: "fractional_endpoint D 0 t < 1/10"
    using fraction_bounds[of 0] by simp
  have identity: "fractional_endpoint D 0 t = t"
    using fraction[of 0] by simp
  have inlet: "t < 1/2" using first identity by linarith
  have all_bounds:
    "\<forall>j\<le>?n. 0 \<le> fractional_endpoint D j t \<and>
      fractional_endpoint D j t < 1/2"
    using fraction_bounds by fastforce
  show "cylinder_guard D ?n t"
    using guard_iff_endpoint_bounds[OF tail(1) inlet, of D ?n] all_bounds by blast
  show "mahler_orbit D ?n = 4*u*3^?n"
    using orbit[of ?n] by (simp add: algebra_simps)
  show "fractional_endpoint D ?n t = (3/2)^?n*t"
    by (rule fraction) simp
  show "mahler_orbit D j mod 20 =
      (if even j then D mod 20 else 20 - D mod 20)" if "j \<le> ?n" for j
    by (rule ports[OF that])
  show "0 \<le> fractional_endpoint D j t \<and>
      fractional_endpoint D j t < 1/10" if "j \<le> ?n" for j
    by (rule fraction_bounds[OF that])
qed


theorem mahler_graph_issued_powered_row:
  fixes D m :: nat and t :: real
  assumes valuation: "D mod 2^(2*m+2) = 0"
      and port: "D mod 20 = 16 \<or> D mod 20 = 4"
      and tail: "0 \<le> t" "(3/2)^(2*m)*t < 1/10"
  shows "cylinder_guard D (2*m) t"
    and "\<exists>u. D = 2^(2*m+2)*u \<and>
      mahler_orbit D (2*m) = 4*u*3^(2*m)"
    and "fractional_endpoint D (2*m) t = (3/2)^(2*m)*t"
    and "\<And>j. j \<le> 2*m \<Longrightarrow>
      mahler_orbit D j mod 20 =
        (if even j then D mod 20 else 20 - D mod 20)"
    and "\<And>j. j \<le> 2*m \<Longrightarrow>
      0 \<le> fractional_endpoint D j t \<and>
      fractional_endpoint D j t < 1/10"
proof -
  have "2^(2*m+2) dvd D" using valuation by (simp add: dvd_eq_mod_eq_0)
  then obtain u where source: "D = 2^(2*m+2)*u" by (auto simp: dvd_def)
  have result:
    "cylinder_guard (2^(2*m+2)*u) (2*m) t"
    "mahler_orbit (2^(2*m+2)*u) (2*m) = 4*u*3^(2*m)"
    "fractional_endpoint (2^(2*m+2)*u) (2*m) t = (3/2)^(2*m)*t"
    "\<And>j. j \<le> 2*m \<Longrightarrow>
      mahler_orbit (2^(2*m+2)*u) j mod 20 =
        (if even j then (2^(2*m+2)*u) mod 20
          else 20 - (2^(2*m+2)*u) mod 20)"
    "\<And>j. j \<le> 2*m \<Longrightarrow>
      0 \<le> fractional_endpoint (2^(2*m+2)*u) j t \<and>
      fractional_endpoint (2^(2*m+2)*u) j t < 1/10"
  proof -
    have admitted:
      "(2^(2*m+2)*u) mod 20 = 16 \<or> (2^(2*m+2)*u) mod 20 = 4"
      using source port by simp
    show "cylinder_guard (2^(2*m+2)*u) (2*m) t"
      by (rule mahler_graph_powered_even_row(1)[where u=u and m=m and t=t])
        (use admitted tail in simp_all)
    show "mahler_orbit (2^(2*m+2)*u) (2*m) = 4*u*3^(2*m)"
      by (rule mahler_graph_powered_even_row(2)[where u=u and m=m and t=t])
        (use admitted tail in simp_all)
    show "fractional_endpoint (2^(2*m+2)*u) (2*m) t = (3/2)^(2*m)*t"
      by (rule mahler_graph_powered_even_row(3)[where u=u and m=m and t=t])
        (use admitted tail in simp_all)
    show "mahler_orbit (2^(2*m+2)*u) j mod 20 =
        (if even j then (2^(2*m+2)*u) mod 20
          else 20 - (2^(2*m+2)*u) mod 20)" if "j \<le> 2*m" for j
      by (rule mahler_graph_powered_even_row(4)[where u=u and m=m and t=t])
        (use admitted tail that in simp_all)
    show "0 \<le> fractional_endpoint (2^(2*m+2)*u) j t \<and>
        fractional_endpoint (2^(2*m+2)*u) j t < 1/10" if "j \<le> 2*m" for j
      by (rule mahler_graph_powered_even_row(5)[where u=u and m=m and t=t])
        (use admitted tail that in simp_all)
  qed
  show "cylinder_guard D (2*m) t" using result(1) source by simp
  show "\<exists>u. D = 2^(2*m+2)*u \<and>
      mahler_orbit D (2*m) = 4*u*3^(2*m)"
    using result(2) source by blast
  show "fractional_endpoint D (2*m) t = (3/2)^(2*m)*t"
    using result(3) source by simp
  show "mahler_orbit D j mod 20 =
      (if even j then D mod 20 else 20 - D mod 20)" if "j \<le> 2*m" for j
    using result(4)[OF that] source by simp
  show "0 \<le> fractional_endpoint D j t \<and>
      fractional_endpoint D j t < 1/10" if "j \<le> 2*m" for j
    using result(5)[OF that] source by simp
qed

theorem mahler_graph_rotated_guard_transport:
  assumes "j \<le> n"
  shows "cylinder_guard D n t \<longleftrightarrow>
    cylinder_guard D j t \<and>
    cylinder_guard (mahler_orbit D j) (n-j) (fractional_endpoint D j t)"
  using source_guard_composition[of D j "n-j" t] assms by simp

text \<open>The source-admitted graph action can be split at a complete
two-tick copy.  The full dyadic cylinder admits both sides of the seam.
Its ledger is strictly decreasing throughout the ordered zero word, so
its minimum and first negative prefix are determined by physical elapsed
ticks.\<close>

theorem mahler_graph_adjoining_copy_consumer:
  fixes D m n :: nat and t :: real
  assumes valuation: "D mod 2^(2*(m+n)+2) = 0"
    and port: "D mod 20 = 16 \<or> D mod 20 = 4"
    and tail: "0 \<le> t" "(3/2)^(2*(m+n))*t < 1/10"
  shows "cylinder_guard D (2*m) t"
    and "cylinder_guard (mahler_orbit D (2*m)) (2*n)
      (fractional_endpoint D (2*m) t)"
    and "mahler_orbit D (2*m) mod 20 = D mod 20"
    and "\<And>j. j \<le> 2*(m+n) \<Longrightarrow> ledger_at D j = - int j"
proof -
  have total: "cylinder_guard D (2*(m+n)) t"
    by (rule mahler_graph_issued_powered_row(1)[OF valuation port tail])
  have split:
    "cylinder_guard D (2*m) t \<and>
      cylinder_guard (mahler_orbit D (2*m)) (2*n)
        (fractional_endpoint D (2*m) t)"
    using total mahler_graph_rotated_guard_transport[of "2*m" "2*(m+n)" D t]
    by simp
  show "cylinder_guard D (2*m) t" using split by blast
  show "cylinder_guard (mahler_orbit D (2*m)) (2*n)
      (fractional_endpoint D (2*m) t)" using split by blast
  show "mahler_orbit D (2*m) mod 20 = D mod 20"
    using mahler_graph_issued_powered_row(4)[OF valuation port tail, of "2*m"]
    by simp
  have divisor: "2^(2*(m+n)+2) dvd D"
    using valuation by (simp add: dvd_eq_mod_eq_0)
  show "ledger_at D j = - int j" if bound: "j \<le> 2*(m+n)" for j
  proof -
    have "(2::nat)^j dvd 2^(2*(m+n)+2)"
      by (rule dvd_power_le) (use bound in simp_all)
    then have "2^j dvd D" by (rule dvd_trans[OF _ divisor])
    then obtain u where source: "D = 2^j * u" by (auto simp: dvd_def)
    have "odd_events D j = 0"
      using odd_events_dyadic_block_zero[of j u] source by simp
    then show ?thesis using ledger_event_accounting[of D j] by simp
  qed
qed

theorem mahler_graph_first_ledger_failure:
  fixes D m n balance :: nat and t :: real
  assumes valuation: "D mod 2^(2*(m+n)+2) = 0"
    and port: "D mod 20 = 16 \<or> D mod 20 = 4"
    and tail: "0 \<le> t" "(3/2)^(2*(m+n))*t < 1/10"
    and failure: "balance < 2*(m+n)"
  shows "int balance + ledger_at D (Suc balance) < 0"
    and "\<And>j. j \<le> balance \<Longrightarrow> 0 \<le> int balance + ledger_at D j"
proof -
  have one: "Suc balance \<le> 2*(m+n)" using failure by simp
  show "int balance + ledger_at D (Suc balance) < 0"
    using mahler_graph_adjoining_copy_consumer(4)[OF valuation port tail one] by simp
  show "0 \<le> int balance + ledger_at D j" if "j \<le> balance" for j
    using mahler_graph_adjoining_copy_consumer(4)[OF valuation port tail, of j]
      that failure by simp
qed

ML \<open>
  val checked = @{thms mahler_graph_issued_powered_row
    mahler_graph_rotated_guard_transport mahler_graph_adjoining_copy_consumer
    mahler_graph_first_ledger_failure};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Mahler graph consumer depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked
    then error "Skipped Mahler graph consumer proof" else ();
\<close>

end
