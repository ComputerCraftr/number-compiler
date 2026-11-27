theory Reverse_Native_Slab_Collars
  imports Reverse_Native_Slab_Outer_Packet
begin

definition slab_pair_digits :: "nat list \<Rightarrow> nat list \<Rightarrow> nat list" where
  "slab_pair_digits xs ys = map (\<lambda>(a,b). a+b) (zip xs ys)"

definition slab_outer_advance :: "nat list \<Rightarrow> bool \<Rightarrow> nat list" where
  "slab_outer_advance front seam =
    slab_pair_digits (emit False front)
      (take (length front) ((if carry_out seam (rev front) then [1] else []) @ rev (emit seam (rev front))))"

text \<open>A resetting cell at the far side of the symmetric middle fixes the
backward inlet of the complete outer collar. Its reverse scan issues the
physical birth and the correctly shifted high digits on that same pass.\<close>
theorem slab_outer_collar_step:
  fixes front middle :: "nat list"
  defines "row \<equiv> front @ middle @ rev front"
  assumes reset: "\<And>c. carry_out c middle = seam"
  shows "carry_out False row = carry_out seam (rev front)"
    and "take (length front) (step row) = slab_outer_advance front seam"
proof -
  show clock: "carry_out False row = carry_out seam (rev front)"
    by (simp add: row_def carry_out_append reset)
  let ?f = "emit False front"
  let ?m = "emit (carry_out False front) middle"
  let ?h = "emit seam (rev front)"
  let ?b = "if carry_out seam (rev front) then [1::nat] else []"
  have word: "digits row = ?f @ ?m @ ?h @ ?b"
    unfolding digits_def using clock by (simp add: row_def emit_append carry_out_append reset)
  have low: "take (length front) (digits row) = ?f" by (simp add: word)
  have high: "take (length front) (rev (digits row)) =
      take (length front) (?b @ rev ?h)"
    by (cases "length front"; cases "carry_out seam (rev front)") (simp_all add: word take_append)
  show "take (length front) (step row) = slab_outer_advance front seam"
    unfolding step_def slab_outer_advance_def slab_pair_digits_def
    by (simp only: take_map take_zip low high)
qed

definition slab_center :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "slab_center k xs = take (length xs - 2*k) (drop k xs)"

lemma slab_center_rev:
  "slab_center k (rev xs) = rev (slab_center k xs)"
proof (cases "2*k \<le> length xs")
  case True
  have diff: "length xs - (k + (length xs - 2*k)) = k" "length xs - (k+k) = length xs - 2*k" using True by arith+
  show ?thesis by (simp add: slab_center_def rev_take rev_drop drop_take diff)
next
  case False then show ?thesis by (simp add: slab_center_def)
qed

lemma slab_source_split:
  assumes bound: "2*k \<le> length xs" and sym: "rev xs = xs"
  shows "take k xs @ slab_center k xs @ rev (take k xs) = xs"
proof -
  have last: "rev (take k xs) = drop (length xs-k) xs" by (simp add: rev_take sym)
  have plus: "k + (length xs - 2*k) = length xs - k" using bound by arith
  have rest: "slab_center k xs @ drop (length xs-k) xs = drop k xs"
    using append_take_drop_id[of "length xs-2*k" "drop k xs"]
    by (simp add: slab_center_def plus add.commute)
  show ?thesis by (simp add: last rest)
qed

lemma slab_center_head:
  assumes bounds: "2*k < length xs"
  shows "slab_center k xs \<noteq> []" "hd (slab_center k xs) = xs!k"
proof -
  have k: "k < length xs" and len: "0 < length xs - 2*k" using bounds by arith+
  have split: "drop k xs = xs!k # drop (Suc k) xs" using Cons_nth_drop_Suc[OF k] by simp
  show "slab_center k xs \<noteq> []" "hd (slab_center k xs) = xs!k"
    using len by (cases "length xs-2*k"; simp_all add: slab_center_def split)+
qed

theorem slab_outer_collar_at:
  assumes valid: "valid_pair row" and bound: "2*k < length row" and reset: "row!k \<noteq> 9"
  shows "carry_out False row = carry_out (9 < row!k) (rev (take k row))"
    and "take k (step row) = slab_outer_advance (take k row) (9 < row!k)"
proof -
  let ?m = "slab_center k row"
  have sym: "rev row = row" using valid by (simp add: valid_pair_def)
  have split: "take k row @ ?m @ rev (take k row) = row"
    by (rule slab_source_split[OF less_imp_le[OF bound] sym])
  have msym: "rev ?m = ?m" using slab_center_rev[of k row] sym by metis
  have ne: "?m \<noteq> []" by (rule slab_center_head(1)[OF bound])
  have mlast: "last ?m = row!k" using hd_rev[of ?m] msym slab_center_head(2)[OF bound] by metis
  have port: "carry_out c ?m = (9 < row!k)" for c
    proof -
    have exact: "carry_out c ?m = carry_apply (domain (last ?m)) (carry_out c (butlast ?m))"
      using carry_out_append_one[of c "butlast ?m" "last ?m"] ne by simp
    show ?thesis using reset by (auto simp: exact mlast domain_def split: if_splits)
  qed
  have len: "length (take k row) = k" using bound by simp
  show "carry_out False row = carry_out (9 < row!k) (rev (take k row))"
    using slab_outer_collar_step(1)[OF port, of "take k row"] by (simp only: split)
  show "take k (step row) = slab_outer_advance (take k row) (9 < row!k)"
    using slab_outer_collar_step(2)[OF port, of "take k row"] by (simp only: split len)
qed

lemma slab_center_step:
  "slab_center k (step row) =
    slab_pair_digits (slab_center k (digits row)) (rev (slab_center k (digits row)))"
  by (simp add: slab_center_def slab_pair_digits_def step_def take_map drop_map take_zip drop_zip
                slab_center_rev[symmetric, unfolded slab_center_def])

definition slab_inner_low :: "nat list \<Rightarrow> bool \<Rightarrow> nat list" where
  "slab_inner_low cells born =
    (let rest = tl cells in
      take (length rest - (if born then 0 else 1)) (emit (9 < hd cells) rest))"

text \<open>The active center collar contracts one pair at each side per tick.
If the physical width grows, its last emitted digit remains inside the
cut. The reset makes the surviving emissions independent of the inlet
entering the discarded cell.\<close>
theorem slab_contract_collar:
  assumes valid: "valid_pair row" and bound: "2*k < length row" and reset: "row!k \<noteq> 9"
  defines "low \<equiv> slab_inner_low (slab_center k row) (carry_out False row)"
  shows "slab_center (Suc k) (digits row) = low"
    and "slab_center (Suc k) (step row) = slab_pair_digits low (rev low)"
proof -
  let ?f = "take k row"
  let ?m = "slab_center k row"
  obtain rest where m: "?m = row!k # rest"
    using slab_center_head[OF bound] by (cases ?m) auto
  have sym: "rev row = row" using valid by (simp add: valid_pair_def)
  have split: "row = ?f @ ?m @ rev ?f"
    using slab_source_split[OF less_imp_le[OF bound] sym] by simp
  have split_emit: "emit False row = emit False ?f @ emit (carry_out False ?f) ?m @
      emit (carry_out (carry_out False ?f) ?m) (rev ?f)"
    using arg_cong[OF split, of "emit False"] by (simp only: emit_append carry_out_append)
  have inlet: "carry_apply (domain (row!k)) c = (9 < row!k)" for c
    using reset by (simp add: domain_def)
  have k: "k \<le> length row" using bound by arith
  have len: "length row = 2*k + Suc (length rest)"
    using arg_cong[OF split, of length] m k by simp
  have low: "slab_center (Suc k) (digits row) = low"
    proof -
    have left_len: "length ?f = k" using k by simp
    have total: "length (digits row) = length row + (if carry_out False row then 1 else 0)"
      by (simp add: length_digits_exact)
    have trim: "length (digits row) - 2 * Suc k =
        length rest - (if carry_out False row then 0 else 1)"
      using total len by (cases "carry_out False row"; arith)
    show ?thesis
      unfolding slab_center_def[of "Suc k"] low_def slab_inner_low_def
      apply (subst trim)
      using k
      by (cases "carry_out False row"; simp add: digits_def split_emit m Let_def inlet
          drop_append min_absorb2 take_append)
  qed
  show "slab_center (Suc k) (digits row) = low" by (rule low)
  show "slab_center (Suc k) (step row) = slab_pair_digits low (rev low)"
    by (simp only: slab_center_step low)
qed

text \<open>Trimming equally many digits from each side preserves the physical
center. The contracting collar returns the selected center digit directly
when the successor has odd width.\<close>
lemma slab_center_digit:
  assumes clipped: "2*k < length xs"
  shows "slab_center k xs ! (length (slab_center k xs) div 2) = xs ! (length xs div 2)"
proof -
  have a: "k \<le> length xs" and b: "length xs - 2*k \<le> length xs - k" using clipped by arith+
  have size: "length (slab_center k xs) = length xs - 2*k"
    using b by (simp add: slab_center_def)
  have inside: "(length xs - 2*k) div 2 < length xs - 2*k" using clipped by presburger
  have i: "k + (length xs - 2*k) div 2 = length xs div 2" using clipped by presburger
  show ?thesis by (simp add: size slab_center_def inside i a)
qed

corollary slab_contract_physical_center:
  assumes v: "valid_pair row" and room: "2*k < length row" and reset: "row!k \<noteq> 9"
    and inside: "2*Suc k < length (digits row)"
  defines "low \<equiv> slab_inner_low (slab_center k row) (carry_out False row)"
  shows "low ! (length low div 2) = digits row ! (length (digits row) div 2)"
  using slab_center_digit[OF inside] slab_contract_collar(1)[OF v room reset]
  by (simp add: low_def)

definition slab_collar_tick where
  "slab_collar_tick port collars =
    (let front = fst collars; cells = snd collars;
         born = carry_out port (rev front);
         low = slab_inner_low cells born
     in (slab_outer_advance front port, slab_pair_digits low (rev low)))"

primrec slab_collar_run where
  "slab_collar_run ports initial 0 = initial"
| "slab_collar_run ports initial (Suc t) =
    slab_collar_tick (ports t) (slab_collar_run ports initial t)"

lemma slab_iter_len: "length xs \<le> length ((step ^^ t) xs)"
  by (induction t) (simp_all add: length_digits_exact)

lemma slab_collar_run_exact:
  fixes xs :: "nat list" and k c n :: nat and p :: "nat \<Rightarrow> bool"
  defines "rows \<equiv> \<lambda>t. (step ^^ t) xs"
    and "initial \<equiv> (take c xs, slab_center k xs)"
  assumes ports: "\<And>t. t < n \<Longrightarrow> valid_pair (rows t) \<and>
      2*c < length (rows t) \<and> 2*(k+t) < length (rows t) \<and>
      rows t ! c \<noteq> 9 \<and> rows t ! (k+t) \<noteq> 9 \<and> p t = (9 < rows t ! c)"
  shows "slab_collar_run p initial n = (take c (rows n), slab_center (k+n) (rows n))"
proof -
  have run: "slab_collar_run p initial t = (take c (rows t), slab_center (k+t) (rows t))"
    if le: "t \<le> n" for t
    using le
  proof (induction t)
    case 0 then show ?case by (simp add: initial_def rows_def)
  next
    case (Suc t)
    have lt: "t < n" using Suc.prems by arith
    have v: "valid_pair (rows t)" and o: "2*c < length (rows t)"
      and i: "2*(k+t) < length (rows t)" and a: "rows t ! c \<noteq> 9"
      and b: "rows t ! (k+t) \<noteq> 9" and p: "p t = (9 < rows t ! c)"
      using ports[OF lt] by blast+
    have prev: "slab_collar_run p initial t = (take c (rows t), slab_center (k+t) (rows t))"
      by (rule Suc.IH) (use lt in arith)
    have nxt: "rows (Suc t) = step (rows t)" by (simp add: rows_def)
    show ?case using slab_outer_collar_at[OF v o a] slab_contract_collar(2)[OF v i b]
      by (simp add: prev nxt slab_collar_tick_def Let_def p)
  qed
  show ?thesis by (rule run) simp
qed

ML \<open>
  val checked = @{thms slab_collar_run_exact slab_contract_collar slab_outer_collar_at};
  val _ = if null (Thm_Deps.all_oracles checked) then () else error "Slab collar oracle";
  val _ = if Thm_Deps.has_skip_proof checked then error "Skipped slab collar" else ();
\<close>
end
