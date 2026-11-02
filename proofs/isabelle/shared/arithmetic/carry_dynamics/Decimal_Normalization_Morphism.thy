theory Decimal_Normalization_Morphism
  imports Shared_Decimal_Cocycle_Core
begin

text \<open>A decimal multiplier acts on an LSD-first digit word through one
ordered carry path.  The input and output words remain distinct; the final
carry is the boundary value to the right of the represented window.\<close>

fun decimal_lsd_value :: "nat list \<Rightarrow> nat" where
  "decimal_lsd_value [] = 0"
| "decimal_lsd_value (d#ds) = d + 10 * decimal_lsd_value ds"

fun decimal_multiplier_columns ::
    "nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat list \<times> nat" where
  "decimal_multiplier_columns multiplier incoming [] = ([], incoming)"
| "decimal_multiplier_columns multiplier incoming (d#ds) =
    (let total = multiplier*d + incoming;
         next = total div 10;
         (tail, outgoing) = decimal_multiplier_columns multiplier next ds
     in (total mod 10 # tail, outgoing))"

theorem decimal_multiplier_columns_exact:
  "multiplier * decimal_lsd_value digits + incoming =
    decimal_lsd_value (fst (decimal_multiplier_columns multiplier incoming digits)) +
      10^(length digits) * snd (decimal_multiplier_columns multiplier incoming digits)"
proof (induction digits arbitrary: incoming)
  case Nil
  then show ?case by simp
next
  case (Cons digit digits)
  let ?total = "multiplier*digit + incoming"
  let ?next = "?total div 10"
  obtain tail outgoing where columns:
    "decimal_multiplier_columns multiplier ?next digits = (tail, outgoing)"
    by (cases "decimal_multiplier_columns multiplier ?next digits") auto
  have column_split: "?total = ?total mod 10 + 10 * ?next"
    using div_mult_mod_eq[of ?total 10]
    by (simp add: mult.commute)
  have rest:
    "multiplier * decimal_lsd_value digits + ?next =
      decimal_lsd_value tail + 10^(length digits) * outgoing"
    using Cons.IH[of ?next] columns by simp
  have combined:
    "?total + 10 * multiplier * decimal_lsd_value digits =
      ?total mod 10 +
        10 * (decimal_lsd_value tail + 10^(length digits) * outgoing)"
  proof -
    have first:
      "?total + 10 * multiplier * decimal_lsd_value digits =
        ?total mod 10 + 10 * (?next + multiplier * decimal_lsd_value digits)"
      using column_split by (simp add: algebra_simps)
    have second:
      "?next + multiplier * decimal_lsd_value digits =
        decimal_lsd_value tail + 10^(length digits) * outgoing"
      using rest by (simp add: add.commute)
    show ?thesis using first second by simp
  qed
  have column_result:
    "decimal_multiplier_columns multiplier incoming (digit#digits) =
      (?total mod 10 # tail, outgoing)"
    using columns by (simp add: decimal_multiplier_columns.simps Let_def)
  show ?case
    using combined column_result
    by (simp add: decimal_lsd_value.simps power_Suc algebra_simps)
qed

text \<open>A finite spatial cut retains the carry escaping its final column.
The coefficient stream may be symbolic; neither theorem constructs a digit
list or expands a temporal path. Spatial z is independent of any temporal
selector clock.\<close>

lemma decimal_normalization_finite_cut:
  fixes raw normalized carry :: "nat \<Rightarrow> 'a::comm_ring_1"
    and z :: 'a
  assumes columns: "\<And>j. j<width \<Longrightarrow>
    raw j - normalized j = 10 * carry j -
      (if j=0 then 0 else carry (j-1))"
  shows "(\<Sum>j<width. (raw j-normalized j)*z^j) =
    (10-z)*(\<Sum>j<width. carry j*z^j) +
      (if width=0 then 0 else carry (width-1)*z^width)"
  using columns
proof (induction width)
  case 0
  then show ?case by simp
next
  case (Suc width)
  have smaller: "\<And>j. j<width \<Longrightarrow>
    raw j-normalized j = 10 * carry j -
      (if j=0 then 0 else carry (j-1))"
    using Suc.prems by auto
  have previous:
    "(\<Sum>j<width. (raw j-normalized j)*z^j) =
      (10-z)*(\<Sum>j<width. carry j*z^j) +
        (if width=0 then 0 else carry (width-1)*z^width)"
    by (rule Suc.IH[OF smaller])
  have final_column:
    "raw width-normalized width = 10 * carry width -
      (if width=0 then 0 else carry (width-1))"
    by (rule Suc.prems) simp
  have "(\<Sum>j<Suc width. (raw j-normalized j)*z^j) =
      (\<Sum>j<width. (raw j-normalized j)*z^j) +
        (raw width-normalized width)*z^width"
    by (simp only: sum.lessThan_Suc)
  also have "... =
      (10-z)*(\<Sum>j<width. carry j*z^j) +
        (if width=0 then 0 else carry (width-1)*z^width) +
        (10 * carry width - (if width=0 then 0 else carry (width-1)))*z^width"
    by (simp only: previous final_column)
  also have "... =
      (10-z)*((\<Sum>j<width. carry j*z^j) + carry width*z^width) +
        carry width*z^(Suc width)"
    by (simp add: power_Suc algebra_simps split: if_splits)
  finally show ?case by (simp only: sum.lessThan_Suc) simp
qed

lemma decimal_mod32_erase_annihilated_coefficients:
  fixes coefficient residual z :: "nat \<Rightarrow> 'a::comm_ring_1"
  assumes characteristic: "(32::'a)=0"
    and factors: "\<And>j. j<width \<Longrightarrow> coefficient j=2^(order j)*residual j"
  shows "(\<Sum>j<width. coefficient j*10^j*z j) =
    (\<Sum>j<width. if 5 \<le> order j+j then 0 else coefficient j*10^j*z j)"
proof (rule sum.cong)
  show "{..<width}={..<width}" by (rule refl)
  fix j
  assume index: "j\<in>{..<width}"
  show "coefficient j*10^j*z j =
      (if 5 \<le> order j+j then 0 else coefficient j*10^j*z j)"
  proof (cases "5 \<le> order j+j")
    case True
    have factor: "coefficient j=2^(order j)*residual j"
      by (rule factors) (use index in simp)
    have dead: "coefficient j*10^j=0"
      by (rule decimal_mod32_coefficient_annihilator[OF characteristic factor True])
    show ?thesis by (simp only: True if_True dead mult_zero_left)
  next
    case False
    then show ?thesis by simp
  qed
qed

theorem decimal_normalization_mod32_reconstruct_cut:
  fixes raw normalized carry :: "nat \<Rightarrow> 'a::comm_ring_1"
    and z w :: 'a
  assumes characteristic: "(32::'a)=0" and inverse_root: "z*w=1"
    and columns: "\<And>j. j<width \<Longrightarrow>
      raw j-normalized j = 10 * carry j -
        (if j=0 then 0 else carry (j-1))"
  shows "(\<Sum>j<width. carry j*z^j) =
    decimal_base_z_inverse_kernel w *
      ((\<Sum>j<width. raw j*z^j) -
       (\<Sum>j<width. normalized j*z^j) -
       (if width=0 then 0 else carry (width-1)*z^width))"
proof -
  have defect:
    "(\<Sum>j<width. raw j*z^j) - (\<Sum>j<width. normalized j*z^j) =
      (10-z)*(\<Sum>j<width. carry j*z^j) +
        (if width=0 then 0 else carry (width-1)*z^width)"
    using decimal_normalization_finite_cut[where raw=raw and normalized=normalized
        and carry=carry and width=width and z=z, OF columns]
    by (simp only: left_diff_distrib sum_subtractf)
  show ?thesis
    by (rule decimal_base_z_mod32_carry_reconstruction_from_inverse
        [OF characteristic inverse_root defect])
qed

ML \<open>
  val checked = @{thms decimal_multiplier_columns_exact
    decimal_normalization_finite_cut
    decimal_mod32_erase_annihilated_coefficients
    decimal_normalization_mod32_reconstruct_cut};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Decimal normalization morphism depends on an oracle";
\<close>

end
