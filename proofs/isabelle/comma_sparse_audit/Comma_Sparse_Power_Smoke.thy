theory Comma_Sparse_Power_Smoke
  imports Comma_Sparse_Power_Algebra.Comma_Sparse_Power_Algebra
begin

ML_file "../shared/Proof_Dependency_Audit.ML"

ML_file "../comma_sparse_power_algebra/sparse_power_constructor.ML"

ML \<open>
  local
    open Comma_Sparse_Power_Constructor
    val valid_word = word_term [{label=Stop (0,Landmine),mask=1}]
    fun rejects expected words =
      (case Exn.capture parse_table words of
        Exn.Exn (ERROR message) =>
          if String.isSubstring expected message then ()
          else error "Sparse shape regression failed for the wrong reason"
      | _ => error "Sparse shape regression accepted malformed data")
    val _ = List.app (fn count => rejects "exactly 46"
      (replicate count valid_word)) [0,1,45,47]
    val _ = rejects "924-phase domain"
      (word_term [{label=Stop (0,Landmine),mask=full_mask+1}] ::
        replicate 45 valid_word)
    val _ = rejects "outside the admitted fibers"
      (word_term [{label=Live 46,mask=1}] :: replicate 45 valid_word)
    val _ = if length (parse_table (replicate 46 valid_word))=46 then ()
      else error "Sparse shape regression rejected a well-shaped table"
  in end
\<close>

ML \<open>
  local
    val ctxt = @{context}
    val evaluate = Simplifier.rewrite ctxt
    val guards = Comma_Sector_Guards.make ctxt {max_nodes=128}
    fun evaluate_mask_and masked =
      (case strip_comb (Thm.term_of masked) of
        (head, [left, right]) =>
          if head = Term.head_of @{term "a AND b :: nat"} then
            #theorem (#mask_and guards left right)
          else error "Fused smoke requested a non-AND mask"
      | _ => error "Fused smoke requested a malformed mask")
    val normalize = Comma_Mask_Rows_Conversion.make ctxt
      {key_order=evaluate, label_equal=evaluate, mask_or=evaluate}
    val input = @{cterm
      "comma_mask_rows_normalize (\<lambda>n::nat. [n])
        [(2,1),(1,0),(2,4),(1,2)]"}
    val equation = normalize input
    val _ = if Thm.term_of (Thm.lhs_of equation) aconv Thm.term_of input
        andalso Thm.term_of (Thm.rhs_of equation) aconv
          @{term "[(1,2),(2,5)] :: (nat \<times> nat) list"}
        andalso Thm.nprems_of equation=0 andalso null (Thm.hyps_of equation)
        andalso null (Thm_Deps.all_oracles [equation]) then ()
      else error "Shared row conversion failed exact sort/merge/prune smoke"
    fun rejects label expected conversion =
      (case Exn.capture conversion input of
        Exn.Exn (ERROR message) =>
          if String.isSubstring expected message then ()
          else error ("Shared row conversion rejected " ^ label ^
            " for the wrong reason: " ^ message)
      | Exn.Exn error => Exn.reraise error
      | Exn.Res _ => error ("Shared row conversion accepted " ^ label))
    val wrong_root = Comma_Mask_Rows_Conversion.make ctxt
      {key_order=fn _ => Thm.reflexive @{cterm True},
       label_equal=evaluate, mask_or=evaluate}
    val unresolved = Comma_Mask_Rows_Conversion.make ctxt
      {key_order=Thm.reflexive, label_equal=evaluate, mask_or=evaluate}
    val wrong_mask = Comma_Mask_Rows_Conversion.make ctxt
      {key_order=evaluate, label_equal=evaluate,
       mask_or=fn _ => Thm.reflexive @{cterm "0::nat"}}
    val conditional = Comma_Mask_Rows_Conversion.make ctxt
      {key_order=fn requested =>
         Thm.implies_intr @{cprop True} (Thm.reflexive requested),
       label_equal=evaluate, mask_or=evaluate}
    val hypothesis = Comma_Mask_Rows_Conversion.make ctxt
      {key_order=fn requested =>
         Thm.assume (Thm.cterm_of ctxt
           (Logic.mk_equals (Thm.term_of requested, @{term True}))),
       label_equal=evaluate, mask_or=evaluate}
    val _ = rejects "a foreign comparison theorem"
      "Boolean callback changed its request" wrong_root
    val _ = rejects "an unresolved ordering predicate"
      "Boolean callback did not return a Boolean literal" unresolved
    val _ = rejects "a foreign mask theorem"
      "mask OR callback changed its request" wrong_mask
    val _ = rejects "a conditional comparison theorem"
      "Masked-row Boolean callback is conditional" conditional
    val _ = rejects "a hypothesis-bearing comparison theorem"
      "Masked-row Boolean callback is conditional" hypothesis
    val fused = Comma_Mask_Rows_Conversion.make_restrict_filter ctxt evaluate_mask_and
    val fused_input = @{cterm
      "comma_sector_rows_filter_nonzero
        (comma_sector_rows_restrict (3::nat)
          [(Comma_Round_Invalid,0), (Comma_Round_Fork 1 0,5),
           (Comma_Round_Invalid,3)])"}
    val fused_equation = fused fused_input
    val _ = if Thm.term_of (Thm.lhs_of fused_equation) aconv
          Thm.term_of fused_input
        andalso Thm.term_of (Thm.rhs_of fused_equation) aconv
          @{term "[(Comma_Round_Fork 1 0,1),
            (Comma_Round_Invalid,3)] :: comma_sector_rows"}
        andalso Thm.nprems_of fused_equation=0
        andalso null (Thm.hyps_of fused_equation)
        andalso null (Thm_Deps.all_oracles [fused_equation]) then ()
      else error "Fused restriction/filter conversion changed row order or masks"
    val zero = Comma_Mask_Rows_Conversion.make_restrict_filter ctxt
      (fn _ => error "Guard-zero conversion opened rows")
    val zero_input = @{cterm
      "comma_sector_rows_filter_nonzero
        (comma_sector_rows_restrict 0
          (replicate ((10::nat)^100) (Comma_Round_Invalid,1)))"}
    val zero_equation = zero zero_input
    val _ = if Thm.term_of (Thm.lhs_of zero_equation) aconv
          Thm.term_of zero_input
        andalso Thm.term_of (Thm.rhs_of zero_equation) aconv
          @{term "[] :: comma_sector_rows"}
        andalso Thm.nprems_of zero_equation=0
        andalso null (Thm.hyps_of zero_equation)
        andalso null (Thm_Deps.all_oracles [zero_equation]) then ()
      else error "Guard-zero restriction/filter conversion was not a closed empty result"
  in end
\<close>

text \<open>Exercise the same five-square publisher on a small synthetic table.
This checks executable data equality, including live lookup, phase rotation
and merging; it is not a certificate for the production B1 relation.\<close>
local_setup \<open>
  fn lthy =>
    let
      open Comma_Sparse_Power_Constructor
      val word = word_term
        [{label=Live 0,mask=3}, {label=Stop (0,Landmine),mask=4}]
      val words = replicate 46 word
      val (_,next) = Local_Theory.define
        ((Binding.name "comma_sparse_smoke_base",NoSyn),
          ((Binding.name "comma_sparse_smoke_base_def",[]),
            HOLogic.mk_list wordT words)) lthy
    in next end
\<close>

local_setup \<open>
  fn lthy =>
    let
      open Comma_Sparse_Power_Constructor
      val ctxt = Local_Theory.target_of lthy
      val base = @{term comma_sparse_smoke_base}
      val definition = @{thm comma_sparse_smoke_base_def}
      fun rejected label expected request =
        (case Exn.capture request () of
          Exn.Exn (ERROR message) =>
            if String.isSubstring expected message then ()
            else error ("Sparse publisher rejected " ^ label ^
              " for the wrong reason: " ^ message)
        | Exn.Exn failure => Exn.reraise failure
        | Exn.Res _ => error ("Sparse publisher accepted " ^ label))
      fun check_rejected label expected source source_definition =
        rejected label expected (fn () =>
          publish {base=source, definition=source_definition} lthy)
      val short_table = @{term "([]::comma_sparse_word list)"}
      val short_definition = Thm.reflexive (Thm.cterm_of ctxt short_table)
      val open_word = @{term "[(Comma_Word_Live x,1)]::comma_sparse_word"}
      val open_table = HOLogic.mk_list wordT (replicate 46 open_word)
      val open_definition = Thm.reflexive (Thm.cterm_of ctxt open_table)
      val assumed_definition = Thm.assume (Thm.cterm_of ctxt
        (Logic.mk_equals (base, Thm.term_of (Thm.rhs_of definition))))
      val _ = check_rejected "a forged base owner" "wrong owner or type"
        short_table definition
      val _ = check_rejected "a wrong-length table" "exactly 46"
        short_table short_definition
      val _ = check_rejected "open row payloads" "unsupported natural expression"
        open_table open_definition
      val _ = check_rejected "an assumed definition" "not closed and oracle-free"
        base assumed_definition
    in publish {base=base, definition=definition} lthy end
\<close>

text \<open>
  This smoke theory exercises the retained HOL sparse algebra directly.  The
  former version called constructor-ML helpers that no longer exist after the
  data-only publisher cutover.  The checks below preserve its behavioral
  coverage: a nonuniform live pullback, equal-label phase merging, invalid
  propagation, and fail-closed short-table lookup.  They deliberately do not
  certify the concrete B1/B32 relation; the synthetic publisher run above
  exercises its data extraction and rejection boundary independently.
\<close>

definition comma_sparse_smoke_live :: comma_sparse_word where
  "comma_sparse_smoke_live =
    [(Comma_Word_Live 0, mask 924)]"

definition comma_sparse_smoke_stop :: comma_word_result where
  "comma_sparse_smoke_stop = Comma_Word_Stop 0 (Comma_Terminal_Fork 0)"

definition comma_sparse_smoke_tail :: comma_sparse_word where
  "comma_sparse_smoke_tail =
    [(comma_sparse_smoke_stop, 1), (comma_sparse_smoke_stop, 3)]"

lemma comma_sparse_smoke_tail_has:
  "comma_sparse_has comma_sparse_smoke_tail q comma_sparse_smoke_stop =
    (comma_phase_member 1 q \<or> comma_phase_member 3 q)"
  by (auto simp: comma_sparse_smoke_tail_def comma_sparse_has_def)

lemma comma_sparse_power_transition_smoke:
  assumes phase: "r<924"
  shows "comma_sparse_has
      (comma_sparse_compose 1 comma_sparse_smoke_live
        (\<lambda>_. comma_sparse_smoke_tail)) r
        (Comma_Word_Stop 1 (Comma_Terminal_Fork 0)) =
      (comma_phase_member 1 ((r+1) mod 924) \<or>
       comma_phase_member 3 ((r+1) mod 924))"
proof -
  have composed:
    "comma_sparse_has
      (comma_sparse_compose 1 comma_sparse_smoke_live
        (\<lambda>_. comma_sparse_smoke_tail)) r
        (Comma_Word_Stop 1 (Comma_Terminal_Fork 0)) =
      (\<exists>head. comma_sparse_has comma_sparse_smoke_live r head \<and>
        (case head of
          Comma_Word_Live j \<Rightarrow>
            (\<exists>tail. comma_sparse_has comma_sparse_smoke_tail
                ((r+1) mod 924) tail \<and>
                Comma_Word_Stop 1 (Comma_Terminal_Fork 0) =
                  comma_sparse_shift 1 tail)
        | other \<Rightarrow>
            Comma_Word_Stop 1 (Comma_Terminal_Fork 0) = other))"
    by (rule comma_sparse_compose_has[OF phase])
  show ?thesis
    using composed phase
    by (auto simp: comma_sparse_smoke_live_def comma_sparse_smoke_tail_def
      comma_sparse_smoke_stop_def comma_sparse_has_def comma_phase_full_mask)
qed

lemma comma_sparse_power_merge_smoke:
  "comma_sparse_has
      (comma_sparse_normalize
        [(comma_sparse_smoke_stop,1), (comma_sparse_smoke_stop,3)]) r
      comma_sparse_smoke_stop =
    (comma_phase_member 1 r \<or> comma_phase_member 3 r)"
  by (simp only: comma_sparse_normalize_has)
    (auto simp: comma_sparse_has_def)

lemma comma_sparse_power_invalid_smoke:
  "comma_sparse_data_compose n
      [(Comma_Word_Invalid,mask 924)]
      (\<lambda>_. comma_sparse_smoke_tail) =
    [(Comma_Word_Invalid,mask 924)]"
  by (rule comma_sparse_data_compose_invalid)

lemma comma_sparse_table_lookup_short_regression:
  "comma_sparse_table_lookup ([] :: comma_sparse_word list) 0 =
      [(Comma_Word_Invalid,mask 924)]"
  by (simp add: comma_sparse_table_lookup_def comma_sparse_table_valid_def)

text \<open>Container shape is checked before any cell is read.  In particular,
  an existing index in a malformed table cannot expose its plausible row.\<close>
lemma comma_sparse_table_malformed_sizes_regression:
  assumes "row_total \<in> {0,1,45,47}"
  shows "comma_sparse_table_lookup (replicate row_total comma_sparse_smoke_tail) i =
      [(Comma_Word_Invalid,mask 924)]"
    and "comma_sparse_table_square n (replicate row_total comma_sparse_smoke_tail) = []"
    and "comma_sparse_table_power (replicate row_total comma_sparse_smoke_tail) k = []"
  using assms by (auto intro: comma_sparse_table_lookup_malformed
    comma_sparse_table_square_malformed comma_sparse_table_power_malformed)

lemma comma_sparse_table_one_existing_row_regression:
  "comma_sparse_table_lookup [comma_sparse_smoke_tail] 0 =
    [(Comma_Word_Invalid,mask 924)]"
  by (rule comma_sparse_table_lookup_malformed) simp

lemma comma_sparse_table_exact_shape_regression:
  "i<46 \<Longrightarrow>
    comma_sparse_table_lookup (replicate 46 comma_sparse_smoke_tail) i =
      comma_sparse_smoke_tail"
  by (simp add: comma_sparse_table_lookup_def comma_sparse_table_valid_def)

lemma comma_sparse_stop_mask_oversized_regression:
  "\<not>comma_sparse_power_rows_stop26
    [(Comma_Word_Stop 0 Comma_Terminal_Landmine,Suc (mask 924))]"
  by (simp add: comma_sparse_power_rows_stop26_def)

lemma comma_sparse_empty_word_cannot_refine:
  "\<not>comma_sparse_refines F []"
proof
  assume valid: "comma_sparse_refines F []"
  have "comma_sparse_has [] 0 (F 0)"
    using comma_sparse_refines_at[OF valid, of 0 "F 0"] by simp
  then show False by (simp add: comma_sparse_has_def)
qed

lemma comma_sparse_admit_valid_index_regression:
  "i<46 \<Longrightarrow>
    comma_sparse_admit (base :: nat \<Rightarrow> comma_sparse_word) i = base i"
  by (simp add: comma_sparse_admit_def)

lemma comma_sparse_admit_invalid_index_regression:
  "46\<le>i \<Longrightarrow>
    comma_sparse_admit (base :: nat \<Rightarrow> comma_sparse_word) i =
      [(Comma_Word_Invalid, mask 924)]"
  by (simp add: comma_sparse_admit_def)

text \<open>These two tiny theorems retain the dependency-audit smoke.  They are
  policy checks, not sparse semantic certificates.\<close>
lemma comma_total_macro_smoke_leaf:
  "(0::nat)=0"
  by simp

lemma comma_harmless_dependency_wrapper:
  "(0::nat)=0"
  by (rule comma_total_macro_smoke_leaf)

lemma comma_sparse_clean_dependency_wrapper:
  "True"
  by simp

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_sparse_power_transition_smoke
      comma_sparse_power_merge_smoke comma_sparse_power_invalid_smoke
      comma_sparse_table_lookup_short_regression
      comma_sparse_table_malformed_sizes_regression
      comma_sparse_table_one_existing_row_regression
      comma_sparse_table_exact_shape_regression
      comma_sparse_stop_mask_oversized_regression
      comma_sparse_empty_word_cannot_refine}) then ()
    else error "Sparse power algebra smoke depends on an oracle"
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_sparse_admit_valid_index_regression
      comma_sparse_admit_invalid_index_regression}) then ()
    else error "Sparse admit index regression depends on an oracle"
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Sparse clean dependency wrapper"
    @{thms comma_sparse_clean_dependency_wrapper}
  val _ = Comma_Proof_Dependency_Audit.audit_fuel_free_global @{context}
    "Sparse global clean dependency wrapper"
    @{thms comma_sparse_clean_dependency_wrapper}
  val hidden = Exn.capture (fn () =>
    Comma_Proof_Dependency_Audit.require_native_clean @{context}
      "Sparse hidden dependency wrapper"
      @{thms comma_harmless_dependency_wrapper}) ()
  val _ = (case hidden of
      Exn.Exn (ERROR message) =>
        if String.isSubstring "comma_total_macro_smoke_leaf" message
        then () else error "Hidden retired dependency failed for the wrong reason"
    | _ => error "Transitive retired dependency was not rejected")
  val hidden_global = Exn.capture (fn () =>
    Comma_Proof_Dependency_Audit.audit_fuel_free_global @{context}
      "Sparse global hidden dependency wrapper"
      @{thms comma_harmless_dependency_wrapper}) ()
  val _ = (case hidden_global of
      Exn.Exn (ERROR message) =>
        if String.isSubstring "comma_total_macro_smoke_leaf" message
        then () else error "Global gate failed for the wrong reason"
    | _ => error "Global gate accepted a transitive retired dependency")
\<close>

end
