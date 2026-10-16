theory Reverse_Symmetric_Transfer
  imports Reverse_Inward_Constraint_Soundness
begin

text \<open>The first non-nine symmetric pair is the outermost decisive carry
map. This is the finite selector used by the NC16 inward transfer filter.
The following set-valued recursion characterizes every map admitted by a
collection of pair domains; it preserves correlations about the first
decisive position and does not turn a marginal into a physical future word.\<close>

fun inward_symmetric_rows :: "nat set list \<Rightarrow> nat list set" where
  "inward_symmetric_rows [] = {[]}"
| "inward_symmetric_rows (values # rows) =
    (\<Union>value\<in>values. (Cons value) ` inward_symmetric_rows rows)"

fun inward_symmetric_transfer :: "nat list \<Rightarrow> carry_domain \<Rightarrow> carry_domain" where
  "inward_symmetric_transfer [] center = center"
| "inward_symmetric_transfer (coefficient # coefficients) center =
    (if coefficient = 9 then inward_symmetric_transfer coefficients center
     else domain coefficient)"

fun inward_symmetric_transfer_range ::
    "nat set list \<Rightarrow> carry_domain \<Rightarrow> carry_domain set" where
  "inward_symmetric_transfer_range [] center = {center}"
| "inward_symmetric_transfer_range (values # rows) center =
    domain ` (values - {9}) \<union>
      (if 9 \<in> values then inward_symmetric_transfer_range rows center
       else {})"

lemma inward_symmetric_rows_nonempty:
  "(\<forall>values\<in>set domains. values \<noteq> {}) \<Longrightarrow>
    inward_symmetric_rows domains \<noteq> {}"
proof (induction domains)
  case Nil
  then show ?case by simp
next
  case (Cons current_domain remaining_domains)
  have head: "current_domain \<noteq> {}" using Cons.prems by simp
  have tail: "\<forall>values\<in>set remaining_domains. values \<noteq> {}"
    using Cons.prems by simp
  have "inward_symmetric_rows remaining_domains \<noteq> {}"
    using Cons.IH[OF tail] .
  then obtain row where row: "row \<in> inward_symmetric_rows remaining_domains"
    by blast
  obtain coefficient where coefficient: "coefficient \<in> current_domain"
    using head by blast
  show ?case using row coefficient by auto
qed

theorem inward_symmetric_transfer_range_exact:
  "(\<forall>values\<in>set domains. values \<noteq> {}) \<Longrightarrow>
    inward_symmetric_transfer_range domains center =
      {inward_symmetric_transfer row center |
        row. row \<in> inward_symmetric_rows domains}"
proof (induction domains)
  case Nil
  then show ?case by simp
next
  case (Cons current_domain remaining_domains)
  have tail: "\<forall>values\<in>set remaining_domains. values \<noteq> {}"
    using Cons.prems by simp
  have tail_rows: "inward_symmetric_rows remaining_domains \<noteq> {}"
    using inward_symmetric_rows_nonempty[OF tail] .
  have tail_member: "\<exists>row. row \<in> inward_symmetric_rows remaining_domains"
    using tail_rows by blast
  have tail_exact:
    "inward_symmetric_transfer_range remaining_domains center =
      {inward_symmetric_transfer row center |
        row. row \<in> inward_symmetric_rows remaining_domains}"
    using Cons.IH[OF tail] .
  show ?case
  proof (rule set_eqI)
    fix result
    show "result \<in> inward_symmetric_transfer_range
          (current_domain # remaining_domains) center \<longleftrightarrow>
        result \<in> {inward_symmetric_transfer row center |
          row. row \<in> inward_symmetric_rows
            (current_domain # remaining_domains)}"
    proof
      assume in_range:
        "result \<in> inward_symmetric_transfer_range
          (current_domain # remaining_domains) center"
      then have parts:
        "result \<in> domain ` (current_domain - {9}) \<union>
          (if 9 \<in> current_domain then
            inward_symmetric_transfer_range remaining_domains center
           else {})"
        by simp
      from parts show
        "result \<in> {inward_symmetric_transfer row center |
          row. row \<in> inward_symmetric_rows
            (current_domain # remaining_domains)}"
      proof
        assume reset:
          "result \<in> domain ` (current_domain - {9})"
        then obtain coefficient where
          coefficient: "coefficient \<in> current_domain - {9}" and
          result: "result = domain coefficient"
          by blast
        obtain tail_row where tail_row:
          "tail_row \<in> inward_symmetric_rows remaining_domains"
          using tail_member by blast
        have admitted:
          "coefficient # tail_row \<in>
            inward_symmetric_rows (current_domain # remaining_domains)"
        proof -
          have coefficient_domain: "coefficient \<in> current_domain"
            using coefficient by simp
          have tail_image:
            "coefficient # tail_row \<in>
              (Cons coefficient) ` inward_symmetric_rows remaining_domains"
            by (rule imageI) (rule tail_row)
          show ?thesis
            unfolding inward_symmetric_rows.simps
            by (rule UN_I[
                where A=current_domain and a=coefficient
                  and B="\<lambda>value. (Cons value) `
                    inward_symmetric_rows remaining_domains"
                  and b="coefficient # tail_row",
                OF coefficient_domain tail_image])
        qed
        have transfer:
          "inward_symmetric_transfer (coefficient # tail_row) center =
            domain coefficient"
          using coefficient by simp
        show ?thesis
          unfolding mem_Collect_eq
          using admitted result transfer
          by (intro exI[where x="coefficient # tail_row"]; simp)
      next
        assume continued:
          "result \<in> (if 9 \<in> current_domain then
            inward_symmetric_transfer_range remaining_domains center
           else {})"
        have nine: "9 \<in> current_domain"
        proof (cases "9 \<in> current_domain")
          case True
          then show ?thesis .
        next
          case False
          with continued show ?thesis by simp
        qed
        have tail_result:
          "result \<in> inward_symmetric_transfer_range remaining_domains center"
          using continued nine by simp
        have represented:
          "result \<in> {inward_symmetric_transfer row center |
            row. row \<in> inward_symmetric_rows remaining_domains}"
          using tail_result tail_exact by simp
        then obtain tail_row where tail_row:
          "tail_row \<in> inward_symmetric_rows remaining_domains" and
          result: "result = inward_symmetric_transfer tail_row center"
          by blast
        have admitted:
          "9 # tail_row \<in>
            inward_symmetric_rows (current_domain # remaining_domains)"
        proof -
          have tail_image:
            "9 # tail_row \<in>
              (Cons 9) ` inward_symmetric_rows remaining_domains"
            by (rule imageI) (rule tail_row)
          show ?thesis
            unfolding inward_symmetric_rows.simps
            by (rule UN_I[
                where A=current_domain and a=9
                  and B="\<lambda>value. (Cons value) `
                    inward_symmetric_rows remaining_domains"
                  and b="9 # tail_row",
                OF nine tail_image])
        qed
        have transfer:
          "inward_symmetric_transfer (9 # tail_row) center =
            inward_symmetric_transfer tail_row center"
          by simp
        show ?thesis
          unfolding mem_Collect_eq
          using admitted result transfer
          by (intro exI[where x="9 # tail_row"]; simp)
      qed
    next
      assume represented:
        "result \<in> {inward_symmetric_transfer row center |
          row. row \<in> inward_symmetric_rows
            (current_domain # remaining_domains)}"
      then obtain row where row:
        "row \<in> inward_symmetric_rows (current_domain # remaining_domains)"
        and result: "result = inward_symmetric_transfer row center"
        by blast
      have row_union:
        "row \<in> (\<Union>coefficient\<in>current_domain.
          (Cons coefficient) ` inward_symmetric_rows remaining_domains)"
        using row by simp
      then obtain coefficient where coefficient:
        "coefficient \<in> current_domain" and
        row_image:
          "row \<in> (Cons coefficient) `
            inward_symmetric_rows remaining_domains"
        by blast
      then obtain tail_row where tail_row:
        "tail_row \<in> inward_symmetric_rows remaining_domains" and
        row_shape: "row = coefficient # tail_row"
        by blast
      show "result \<in> inward_symmetric_transfer_range
          (current_domain # remaining_domains) center"
      proof (cases "coefficient = 9")
        case True
        have nine: "9 \<in> current_domain" using coefficient True by simp
        have tail_result:
          "inward_symmetric_transfer tail_row center \<in>
            inward_symmetric_transfer_range remaining_domains center"
          using tail_row tail_exact by blast
        have result_tail:
          "result = inward_symmetric_transfer tail_row center"
          using result row_shape True by simp
        have result_conditional:
          "result \<in> (if 9 \<in> current_domain then
            inward_symmetric_transfer_range remaining_domains center
           else {})"
          using nine tail_result result_tail by simp
        show ?thesis
          unfolding inward_symmetric_transfer_range.simps
          by (rule UnI2[OF result_conditional])
      next
        case False
        have reset:
          "inward_symmetric_transfer (coefficient # tail_row) center =
            domain coefficient"
          using False by simp
        have coefficient:
          "coefficient \<in> current_domain - {9}"
          using coefficient False by simp
        have result_domain: "result = domain coefficient"
          using result row_shape reset by simp
        have image:
          "domain coefficient \<in> domain ` (current_domain - {9})"
          by (rule imageI) (rule coefficient)
        have result_image:
          "result \<in> domain ` (current_domain - {9})"
          using result_domain image by simp
        show ?thesis
          unfolding inward_symmetric_transfer_range.simps
          by (rule UnI1[OF result_image])
      qed
    qed
  qed
qed

corollary inward_symmetric_transfer_admitted:
  assumes domains: "\<forall>values\<in>set domains. values \<noteq> {}"
      and row: "row \<in> inward_symmetric_rows domains"
  shows "inward_symmetric_transfer row center \<in>
    inward_symmetric_transfer_range domains center"
proof -
  have represented:
    "inward_symmetric_transfer row center \<in>
      {inward_symmetric_transfer candidate center |
        candidate. candidate \<in> inward_symmetric_rows domains}"
    using row by blast
  note exact = inward_symmetric_transfer_range_exact[OF domains]
  show ?thesis using exact represented by simp
qed

lemma inward_symmetric_first_non_nine_resets:
  assumes "coefficient \<noteq> 9"
  shows "inward_symmetric_transfer (coefficient # coefficients) center =
    domain coefficient"
  using assms by simp

lemma inward_symmetric_all_equal_keeps_center:
  "inward_symmetric_transfer (replicate n 9) center = center"
  by (induction n) simp_all

ML \<open>
  val checked = @{thms inward_symmetric_transfer_range_exact
    inward_symmetric_transfer_admitted
    inward_symmetric_first_non_nine_resets
    inward_symmetric_all_equal_keeps_center};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Symmetric transfer depends on an oracle";
\<close>

end
