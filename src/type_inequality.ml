(* Take the non-equal pairs of an array from index n, yielding each pair once up to
 * reordering - there is the possibility of optimising this *)
let rec distinct_pairs a =
  if Array.length a == 0
    then [| |]
    else
      let x = a.(0) in
      let xs = Array.init (Array.length a - 1) (fun i -> a.(i+1)) in
      let pairs = Array.map (fun x' -> (x, x')) xs in
      let rest = distinct_pairs xs in
      Array.append pairs rest

open Declarations

(* Pull a nice user-facing name out of an inductive declaration *)
let get_label_string indDec =
  Names.Id.to_string (indDec.mind_typename)

(* For index n, and term t with arity r, build t vn+r ... vn for the deBruijn
 * indices vn ... vn+r *)
let apply_universal_vars_in_context_from_index ctxts term n =
  (* Calculate how many deBruijn indices to create *)
  let num_of_ctxts = Context.Rel.fold_outside (fun _ n -> n + 1) ~init:0 ctxts in
  (* Build them - remember, they start from 1 *)
  let debruijn_indices = Array.init num_of_ctxts (fun i -> n + num_of_ctxts - (i + 1)) in
  let debruijn_indices = Array.map (fun i -> EConstr.mkRel i) debruijn_indices in
  (* Apply them to the term, and return the next variable index *)
  (EConstr.mkApp (term, debruijn_indices), n + num_of_ctxts)

(* For a list of vars v1...vn and term t, build forall v1, ..., forall vn, t *)
let quantify_universal_vars_in_context ctxts term =
  let ctxts = Context.Rel.fold_outside
    (fun ctxt acc ->
        Context.Rel.add
          (Context.Rel.Declaration.map_constr_het EConstr.of_constr ctxt)
          acc)
    ~init:Context.Rel.empty
    ctxts
  in
  EConstr.it_mkProd_or_LetIn term ctxts

(* Generating the axiom for two inductive declarations *)
let declare_type_inequality_axiom env sigma univ eq not (ind1, indBody1) (ind2, indBody2) =
  let axiom_name = get_label_string indBody1 ^ "_neq_" ^ get_label_string indBody2 in
  (* Generate the axiom itself *)
  (* The axiom generated doesn't work for inductives in the template universe -
   * and I don't know why. *)
  match indBody1.mind_arity with
  | Declarations.RegularArity regArity1 ->
      begin match indBody2.mind_arity with
      | Declarations.RegularArity regArity2 ->
          (* Fully apply the inductive type constructors to get two terms, generating a
           * new variable in each argument position for each constructor
           * Notice we start from 1 here because deBruijn indices are 1-indexed *)
          let (t2, n) = apply_universal_vars_in_context_from_index indBody2.mind_arity_ctxt (EConstr.mkInd ind2) 1 in
          (* Here we start from the index n being the next deBruijn index *)
          let (t1, _) = apply_universal_vars_in_context_from_index indBody1.mind_arity_ctxt (EConstr.mkInd ind1) n in
          (* Build the negation of the equality of the fully-applied terms *)
          let t1_neq_t2 = EConstr.mkApp (not, [|(EConstr.mkApp (eq, [|EConstr.mkSort regArity1.mind_sort; t1; t2|]))|]) in
          (* Quantify all the variables used in the terms *)
          let quantified_t1_neq_t2 =
                quantify_universal_vars_in_context
                  indBody1.mind_arity_ctxt
                  (quantify_universal_vars_in_context
                    indBody2.mind_arity_ctxt
                    t1_neq_t2)
          in
          if (Sorts.equal regArity1.mind_sort regArity2.mind_sort)
            then
              (* Generate a unique new axiom name by adding ' repeatedly *)
              let axiom_name =
                let base_name = ref axiom_name in
                while Global.exists_objlabel (Names.Label.of_id (Names.Id.of_string !base_name)) do
                  base_name := !base_name ^ "'"
                done;
                !base_name in
              let sigma = Evd.fix_undefined_variables sigma in
              (* TODO: load these into the hint DB *)
              let (_axRef, _axInstace) =
                ComAssumption.declare_axiom
                    ~poly:true
                    ~local:Declare.ImportDefaultBehavior
                    ~kind:Decls.Logical
                    false
                    (EConstr.to_constr sigma quantified_t1_neq_t2)
                    univ
                    []
                    Declaremods.NoInline
                    (CAst.make (Names.Id.of_string axiom_name))
              in
              Feedback.msg_notice (Pp.strbrk ("Declared \"" ^ axiom_name ^ "\"."))
            else ()
      | Declarations.TemplateArity _ -> ()
      end
  | Declarations.TemplateArity _ -> ()

let pair_inductive_with_declaration_body mutInd mutIndDec =
  (* Types in the mutual inductive declaration are 0-indexed *)
  Array.mapi (fun idx dec -> ((mutInd, idx), dec)) mutIndDec.mind_packets

let generate_type_inequality_axioms () =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  (* Universe stuff - may be affecting the templating issue above *)
  let univs = Evd.check_univ_decl ~poly:true sigma UState.default_univ_decl in
  let ubinders = Evd.universe_binders sigma in
  (* Load up the two types we need for the axioms *)
  let eq = Coqlib.lib_ref "core.eq.type" in
  let (sigma, eq) = (Evarutil.new_global sigma eq) in
  let not = Coqlib.lib_ref "core.not.type" in
  let (sigma, not) = (Evarutil.new_global sigma not) in
  (* Get all inductive definitions to create axioms for *)
  let inductives =
        Environ.fold_inductives
          (fun ind indDec l ->
            Array.append (pair_inductive_with_declaration_body ind indDec) l)
          env
          [| |]
  in
  let ind_pairs = distinct_pairs inductives in
  (* Build the axioms themselves *)
  Array.iter (fun (l, r) -> declare_type_inequality_axiom env sigma (univs, ubinders) eq not l r) ind_pairs
