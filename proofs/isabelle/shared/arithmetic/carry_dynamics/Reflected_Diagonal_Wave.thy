theory Reflected_Diagonal_Wave
  imports Reflected_Diagonal_Table
begin

text \<open>On an interior tile, moving east advances the column and clock.
Moving north advances only the clock. The two outgoing ranks therefore
refer to different physical coordinates even for a square tile.\<close>

definition diagonal_wave_west where
  "diagonal_wave_west m source p i =
    fst (diagonal_table_ports m p (reflected_single_run
      (reflected_alternating_gate m) p source (i - 1)))"

definition diagonal_wave_south where
  "diagonal_wave_south m source p i =
    snd (diagonal_table_ports m p (reflected_single_run
      (reflected_alternating_gate m) p source i))"

lemma diagonal_wave_gate:
  "diagonal_table_cell m (Suc p)
      (diagonal_wave_west m source p i) (diagonal_wave_south m source p i) =
    (diagonal_wave_west m source (Suc p) (i+1),
     diagonal_wave_south m source (Suc p) i)"
  by (cases "even p")
     (simp_all add: diagonal_wave_west_def diagonal_wave_south_def
      diagonal_table_cell_def diagonal_table_ports_def reflected_alternating_gate_def
      Let_def add.commute)

fun diagonal_wave_horizontal where
  "diagonal_wave_horizontal m source p i 0 = []"
| "diagonal_wave_horizontal m source p i (Suc n) =
    diagonal_wave_south m source p i # diagonal_wave_horizontal m source (Suc p) (i+1) n"

fun diagonal_wave_vertical where
  "diagonal_wave_vertical m source p i 0 = []"
| "diagonal_wave_vertical m source p i (Suc n) =
    diagonal_wave_west m source p i # diagonal_wave_vertical m source (Suc p) i n"

lemma diagonal_wave_row:
  "diagonal_table_row (diagonal_table_cell m) (Suc p)
      (diagonal_wave_west m source p i) (diagonal_wave_horizontal m source p i w) =
    (diagonal_wave_west m source (p+w) (i+int w),
     diagonal_wave_horizontal m source (Suc p) i w)"
  by (induction w arbitrary: i p)
     (simp_all add: diagonal_wave_gate Let_def algebra_simps)

theorem diagonal_wave_source_rectangle:
  "diagonal_table_rect (diagonal_table_cell m) (Suc p)
      (diagonal_wave_vertical m source p i h) (diagonal_wave_horizontal m source p i w) =
    (diagonal_wave_vertical m source (p+w) (i+int w) h,
     diagonal_wave_horizontal m source (p+h) i w)"
  by (induction h arbitrary: p)
     (simp_all add: diagonal_wave_row Let_def)

text \<open>The terminal fringe writes column u on the antidiagonal
u + v = source_end + ticks. Before the source and after the requested
diagonal, the C++ fringe emits zero.\<close>

definition diagonal_fringe_digit where
  "diagonal_fringe_digit m source source_end ticks u v =
     (let z = u + v - source_end in
       if z < 0 \<or> int ticks < z then 0
       else reflected_single_run (reflected_alternating_gate m) (nat z) source u)"

lemma diagonal_fringe_source:
  "diagonal_fringe_digit m source s n u (s-u) = source u"
  by (simp add: diagonal_fringe_digit_def Let_def)

lemma diagonal_fringe_advance:
  fixes s u v :: int
  assumes "s < u + v" "u + v \<le> s + int n"
  shows "diagonal_fringe_digit m source s n u v =
    reflected_alternating_gate m (nat (u+v-s-1))
       (diagonal_fringe_digit m source s n (u-1) v)
       (diagonal_fringe_digit m source s n u (v-1))"
proof -
  let ?t = "u + v - s - 1"
  have pos: "0 \<le> ?t" and hi: "?t < int n" using assms by linarith+
  have step: "nat (u + v - s) = Suc (nat ?t)" using pos by linarith
  have left: "u-1+v-s = ?t" and below: "u+(v-1)-s = ?t" by simp_all
  show ?thesis using pos hi assms
    by (simp add: diagonal_fringe_digit_def Let_def left below step)
qed

theorem diagonal_fringe_output_at:
  fixes s u v :: int
  assumes "u + v = s + int n"
  shows "diagonal_fringe_digit m source s n u v =
    reflected_single_run (reflected_alternating_gate m) n source u"
  using assms by (simp add: diagonal_fringe_digit_def Let_def)

theorem diagonal_fringe_local_refinement:
  fixes grid :: "int \<Rightarrow> int \<Rightarrow> nat"
  assumes inlet: "\<And>i. grid i (s-i) = source i"
    and step: "\<And>u v. s<u+v \<Longrightarrow> u+v\<le>s+int n \<Longrightarrow>
      grid u v = reflected_alternating_gate m (nat (u+v-s-1))
        (grid (u-1) v) (grid u (v-1))"
  shows "grid i (s+int n-i) = reflected_single_run (reflected_alternating_gate m) n source i"
proof -
  have exact: "t\<le>n \<Longrightarrow> grid i (s+int t-i) =
    reflected_single_run (reflected_alternating_gate m) t source i" for t i
  proof (induction t arbitrary: i)
    case 0
    show ?case by (simp add: inlet)
  next
    case (Suc t)
    let ?v = "s + int (Suc t) - i"
    have before: "t\<le>n" using Suc.prems by simp
    have inside: "s<i+?v" "i+?v\<le>s+int n" using Suc.prems by simp_all
    have left: "?v = s+int t-(i-1)" and below: "?v-1 = s+int t-i" by simp_all
    have incoming: "grid (i-1) ?v =
        reflected_single_run (reflected_alternating_gate m) t source (i-1)"
      using Suc.IH[OF before, of "i-1"] by (simp only: left)
    have other: "grid i (?v-1) =
        reflected_single_run (reflected_alternating_gate m) t source i"
      using Suc.IH[OF before, of i] by (simp only: below)
    have clock: "nat (i+?v-s-1) = t" by simp
    show ?case
      by (simp only: step[OF inside] incoming other clock reflected_single_run.simps)
  qed
  show ?thesis by (rule exact) simp
qed

lemma diagonal_fringe_tile_output_unique:
  fixes s n u b :: nat
  assumes size: "0 < b" and bound: "u \<le> s+n"
  defines "v \<equiv> s+n-u"
  shows "\<exists>!cell. case cell of (k,j,x,y) \<Rightarrow>
    u=k*b+x \<and> u+(j*b+y)=s+n \<and> x<b \<and> y<b"
proof -
  have unique: "\<And>a k x. a=k*b+x \<Longrightarrow> x<b \<Longrightarrow> k=a div b \<and> x=a mod b"
    using size by auto
  show ?thesis
  proof (rule ex1I[of _ "(u div b,v div b,u mod b,v mod b)"])
    show "case (u div b,v div b,u mod b,v mod b) of (k,j,x,y) \<Rightarrow>
      u=k*b+x \<and> u+(j*b+y)=s+n \<and> x<b \<and> y<b"
      using size bound by (simp add: v_def)
  next
    fix cell :: "nat \<times> nat \<times> nat \<times> nat"
    obtain k j x y where shape: "cell = (k,j,x,y)" by (cases cell) auto
    assume "case cell of (k,j,x,y) \<Rightarrow>
      u=k*b+x \<and> u+(j*b+y)=s+n \<and> x<b \<and> y<b"
    hence eq: "u=k*b+x" "u+(j*b+y)=s+n" "x<b" "y<b" by (simp_all add: shape)
    have veq: "v=j*b+y" using eq(2) unfolding v_def by arith
    show "cell = (u div b,v div b,u mod b,v mod b)"
      using unique[OF eq(1,3)] unique[OF veq eq(4)] by (simp add: shape)
  qed
qed

text \<open>One completed tile sends its east rank to the next slot and
its north rank to the same slot. Clearing or trimming an inactive range
must preserve both ranks, including at the new right edge.\<close>

definition diagonal_next_front where
  "diagonal_next_front eval W S (k::nat) =
     (if k=0 then 0 else fst (eval (W (k-1)) (S (k-1))),
      snd (eval (W k) (S k)))"

lemma diagonal_next_front_bounded:
  fixes eval :: "nat \<Rightarrow> nat \<Rightarrow> nat \<times> nat"
  assumes zero: "eval 0 0 = (0,0)"
    and support: "\<And>j. j<lo \<or> hi<j \<Longrightarrow> W j=0 \<and> S j=0"
    and outside: "k<lo \<or> Suc hi<k"
  shows "diagonal_next_front eval W S k = (0,0)"
proof -
  have curr: "k<lo \<or> hi<k" using outside by arith
  have prev: "k\<noteq>0 \<Longrightarrow> k-1<lo \<or> hi<k-1" using outside by arith
  show ?thesis
  proof (cases "k=0")
    case True
    show ?thesis using True support[OF curr] zero by (simp add: diagonal_next_front_def)
  next
    case False
    have before: "W (k-1)=0" "S (k-1)=0" using support[OF prev[OF False]] by auto
    have here: "W k=0" "S k=0" using support[OF curr] by auto
    show ?thesis by (simp only: diagonal_next_front_def False if_False before here zero fst_conv snd_conv)
  qed
qed

lemma diagonal_next_front_right:
  fixes eval :: "nat \<Rightarrow> nat \<Rightarrow> nat \<times> nat"
  assumes "eval 0 0 = (0,0)" "W (Suc hi)=0" "S (Suc hi)=0"
  shows "diagonal_next_front eval W S (Suc hi) = (fst (eval (W hi) (S hi)),0)"
  using assms by (simp add: diagonal_next_front_def)

ML \<open>
  val checked = @{thms diagonal_wave_gate diagonal_wave_row diagonal_wave_source_rectangle
    diagonal_fringe_source diagonal_fringe_advance diagonal_fringe_output_at diagonal_fringe_local_refinement diagonal_fringe_tile_output_unique
    diagonal_next_front_bounded diagonal_next_front_right};
  val _ = if null (Thm_Deps.all_oracles checked) andalso not (Thm_Deps.has_skip_proof checked)
    then () else error "Reflected source wave proof audit failed";
\<close>

end
