structure Comma_Semantic_Continue_Application_Transport =
struct
  open Comma_Semantic_Continue_Observer_Contract

  structure Masked = Comma_Semantic_Continue_Masked_Columns
  structure Columns = Comma_Semantic_Continue_Column_Proofs

  type callbacks = Masked.callbacks
  type value = Comma_Semantic_Continue_Observer_Contract.value

  fun validate_actual (callbacks:callbacks) label actual actual_admitted =
    let
      val _ = Masked.require_column (label ^ " actual") actual
      val actual_admitted = Masked.require_proposition (#validate_native callbacks)
        (label ^ " actual admission") (Masked.admitted_prop actual) actual_admitted
    in actual_admitted end

  (* The completed application was proved under the exact True demand.  Remove
     that outer conjunction by transporting the checked equivalence; this
     helper never constructs or evaluates an application. *)
  fun unmask (callbacks:callbacks) label actual actual_admitted
      (full:value) =
    let
      val actual_admitted = validate_actual callbacks label actual actual_admitted
      val _ = if fastype_of (#column full) = columnT then ()
        else error (label ^ " full result is not a CRT column")
      val _ = Columns.require_literal_column (label ^ " full result") (#column full)
      val masked_actual = Masked.apply_and @{term "Comma_CRT_Bool True"} actual
      val _ = Masked.require_proposition (#validate_native callbacks)
        (label ^ " full actual admission") (Masked.admitted_prop masked_actual)
        (#actual_admitted full)
      val full_admitted = Masked.require_proposition (#validate_native callbacks)
        (label ^ " full result admission") (Masked.admitted_prop (#column full))
        (#admitted full)
      val full_equivalent = Masked.require_proposition (#validate_native callbacks)
        (label ^ " full exact request")
        (Masked.equiv_prop masked_actual (#column full)) (#equivalent full)
      val true_equivalent = Masked.true_mask_equiv callbacks
        (label ^ " True-mask identity")
        {column=actual,admitted=actual_admitted}
      val unmasked_to_masked = Masked.symmetric_equiv callbacks
        (label ^ " True-mask symmetry") masked_actual actual true_equivalent
      val equivalent = Columns.trans_equiv (#ctxt callbacks)
        (#validate_native callbacks) (label ^ " unmasked result transport")
        actual masked_actual (#column full) unmasked_to_masked full_equivalent
    in
      {column= #column full, admitted=full_admitted,
       actual_admitted=actual_admitted, equivalent=equivalent}:value
    end

end
