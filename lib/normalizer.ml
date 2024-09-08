open Ast
open Batteries

type type_check_error =
  | ExpectPairGot of value
  | ExpectCallableGot of value
  | ExpectAbsurdGot of value
  | ExpectSameOrEqGot of value
  | ExpectNatGot of value
  | ExpectEqGot of value
  | ExpectPiGot of value
  | ExpectSigmaGot of value
  | ExpectTrivialGot of value
  | ExpectAtomGot of value
  | ExpectSameTypeGot of value * value
  | UndefinedSymbol of symbol
  | DuplicateDefinition of symbol
  | ReadbackFailed of normal
  | CantSynthesize of expression

exception RE of type_check_error

let alpha_equiv e1_top e2_top = 
  (* We store de Bruijn Indices in the List *)
  let rec alpha_equiv_aux e1 e2 syms1 syms2 =
    match (e1, e2) with
    | (Atom a1, Atom a2) -> 0 == compare a1 a2
    | (Symbol sym1, Symbol sym2) ->
        begin match (List.index_of sym1 syms1, List.index_of sym2 syms2) with
        | Some i, Some j -> i == j
        | Some _, None -> raise (RE(UndefinedSymbol(sym2)))
        | None, _ -> raise (RE(UndefinedSymbol(sym1)))
        end
    | (Lambda(sym1, inner1), Lambda(sym2, inner2)) ->
        alpha_equiv_aux inner1 inner2 (sym1 :: syms1) (sym2 :: syms2)
    | (Pi(x1, a1, b1), Pi(x2, a2, b2))
    | (Sigma(x1, a1, b1), Sigma(x2, a2, b2))  ->
        alpha_equiv_aux a1 a2 syms1 syms2
        && alpha_equiv_aux b1 b2 (x1 :: syms1) (x2 :: syms2)
    | The(Atom Absurd, _), The(Atom Absurd, _) ->
        true
    | The(x1, y1), The(x2, y2)
    | Cons(x1, y1), Cons(x2, y2)
    | App(x1, y1), App(x2, y2)
    | Ind_Absurd(x1, y1), Ind_Absurd(x2, y2)
->
        alpha_equiv_aux x1 x2 syms1 syms2
        && alpha_equiv_aux y1 y2 syms1 syms2
    | Car(x1), Car(x2)
    | Cdr(x1), Cdr(x2)
    | Add1(x1), Add1(x2)
    ->
        alpha_equiv_aux x1 x2 syms1 syms2
    | Eq(x1, y1, z1), Eq(x2, y2, z2)
    | Replace(x1, y1, z1), Replace(x2, y2, z2)
    -> 
        alpha_equiv_aux x1 x2 syms1 syms2
        && alpha_equiv_aux y1 y2 syms1 syms2
        && alpha_equiv_aux z1 z2 syms1 syms2
    | Ind_Nat(u1, v1, x1, y1), Ind_Nat(u2, v2, x2, y2)
    -> 
        alpha_equiv_aux u1 u2 syms1 syms2
        && alpha_equiv_aux v1 v2 syms1 syms2
        && alpha_equiv_aux x1 x2 syms1 syms2
        && alpha_equiv_aux y1 y2 syms1 syms2
    | _ -> false

  in alpha_equiv_aux e1_top e2_top [] []

let lookup_context_type (sym: symbol) (ctx: context) =
  match StrMap.find_opt sym ctx with
  | None -> None
  | Some(Def {ty; _}) -> Some ty
  | Some(Bind {ty}) -> Some ty

let context_to_environment (ctx: context) =
  let f sym = function
  | Def { value; _ } -> value
  | Bind { ty } -> VNeu(ty, NVar(sym))
  in
  StrMap.mapi f ctx

let extend_context (ctx: context) (x: symbol) (t: value) =
  StrMap.add x (Bind { ty = t}) ctx

let rec apply_closure (f: closure) (x: value) =
  match f with
  | Transparent { env; var; body } ->
      evaluate (StrMap.add var x env) body
  | HigherOrder { fn; _ } ->
      fn x

and evaluate (env: environment) = function
  | Atom(a) -> VAtom(a)
  | The(_, inner) -> evaluate env inner
  | Pi(x, a, b) ->
      VPi(evaluate env a, Transparent {env = env; var = x; body = b})
  | Lambda(x, b) ->
      VLambda(Transparent { env = env; var = x; body = b})
  | Sigma(x, a, d) ->
      VSigma(evaluate env a, Transparent { env = env; var = x; body = d})
  | Cons(car, cdr) ->
      VPair(evaluate env car, evaluate env cdr)
  | Add1 inner ->
      VAdd1 (evaluate env inner)
  | Eq(a, from, _to) ->
      VEq(evaluate env a, evaluate env from, evaluate env _to)
  | Symbol(x) ->
    begin match StrMap.find_opt x env with
    | Some(v) -> v
    | None -> raise (RE(UndefinedSymbol(x)))
    end
  | Car(pair) ->
      evaluate_car (evaluate env pair)
  | Cdr(pair) ->
      evaluate_cdr (evaluate env pair)
  | App(rator, rand) ->
      evaluate_apply (evaluate env rator) (evaluate env rand)
  | Ind_Absurd(target, motive) ->
      evaluate_ind_absurd (evaluate env target) (evaluate env motive)
  | Replace(target, motive, base) ->
      evaluate_replace (evaluate env target) (evaluate env motive) (evaluate env base)
  | Ind_Nat(target, motive, base, step) ->
      evaluate_ind_nat (evaluate env target) (evaluate env motive) (evaluate env base) (evaluate env step)

and evaluate_car (v: value) =
  match v with
  | VPair(car, _) -> car
  | VNeu(VSigma(a, _), ne) ->
      VNeu(a, (NCar ne))
  | _ -> raise (RE(ExpectPairGot(v)))

and evaluate_cdr (v: value) =
  match v with
  | VPair(_, cdr) -> cdr
  | VNeu(VSigma(_, d), ne) ->
      VNeu(apply_closure d (evaluate_car v), (NCdr ne))
  | _ -> raise (RE(ExpectPairGot(v)))

and evaluate_apply (f: value) (x: value) = 
  match f with
  | VLambda c -> apply_closure c x
  | VNeu(VPi(a, b), ne) ->
      VNeu(apply_closure b x, NApp(ne, The(a, x)))
  | _ -> raise (RE(ExpectCallableGot(f)))

and evaluate_ind_absurd (target: value) (motive: value) =
  match target with
  | VNeu(VAtom(Absurd), ne) ->
      VNeu(motive, (NInd_Absurd(ne, (The(VAtom U, motive)))))
  | _ -> raise (RE(ExpectAbsurdGot(target)))

and evaluate_replace (target: value) (motive: value) (base: value) =
  match target with
  | VAtom(Same) -> base
  | VNeu(VEq(a, from, _to), ne) ->
      VNeu(
        evaluate_apply motive _to, 
        NReplace(
          ne,
          (The (VPi(a, (HigherOrder { var = "x"; tag = "evaluate_replace_tmp"; fn = const (VAtom U)})), motive)),
          (The((evaluate_apply motive from), base))))
  | _ -> raise (RE(ExpectSameOrEqGot(target)))

and evaluate_ind_nat (target: value) (motive: value) (base: value) (step: value) =
  match target with
  | VAtom(Zero) -> base
  | VAdd1(n) ->
      evaluate_apply (evaluate_apply step n) (evaluate_ind_nat n motive base step)
  | VNeu(VAtom Nat, ne) ->
      VNeu(
        evaluate_apply motive target,
        NInd_Nat(
          ne,
          The(VPi(VAtom Nat, HigherOrder { var = "k"; tag = "evaluate_ind_nat_tmp"; fn = const (VAtom U)}), motive),
          The(evaluate_apply motive (VAtom Zero), base),
          The(ind_nat_step_type motive, step)))
  | _ -> raise (RE(ExpectNatGot(target)))

and ind_nat_step_type (motive: value) =
  let g n_minus_1 _ =
    evaluate_apply motive (VAdd1 n_minus_1)
  in
  let f n_minus_1 = 
    VPi(evaluate_apply motive n_minus_1, HigherOrder{ var = "ith"; tag = "ind_nat_step_type_tmp2"; fn = g n_minus_1}) 
  in
  VPi(VAtom Nat, HigherOrder{ var = "n-1"; tag = "ind_nat_step_type_tmp"; fn = f})

let rec read_back_norm (ctx: context) (norm: normal) =
    match norm with
    | The(VAtom Nat, VAtom Zero) -> Atom Zero

    | The(VAtom Nat, VAdd1 inner) -> 
        Add1(read_back_norm ctx (The(VAtom Nat, inner)))

    | The(VPi(a, b), f) ->
        let x = get_closure_bound_var b in
        let y = freshen (to_sym_set ctx) x in
        let y_val = VNeu(a, NVar(y)) in
            Lambda(
                y,
                read_back_norm (extend_context ctx y a) (The(apply_closure b y_val, evaluate_apply f y_val)))

    | The(VSigma(a, d), p) ->
        (* NOTE: here we're different from the algorithm *)
        let car_val = evaluate_car p in
        let the_car = The(a, car_val) in
        let the_cdr = The(apply_closure d car_val, evaluate_cdr p) in
        Cons(read_back_norm ctx the_car, read_back_norm ctx the_cdr)

    | The(VAtom(Trivial), _) ->
        Atom(Sole)

    | The(VAtom(Absurd), VNeu(VAtom(Absurd), ne)) ->
        The(Atom(Absurd), read_back_neutral ctx ne)

    | The(VEq _, VAtom(Same)) ->
        Atom(Same)

    | The(VAtom(Atom), VAtom(Quote(x))) ->
        Atom(Quote(x))
        
    | The(VAtom(U), VAtom(a)) ->
        Atom(a)

    | The(VAtom(U), VEq(a, from, _to)) ->
        Eq(
            read_back_norm ctx (The(VAtom(U), a)),
            read_back_norm ctx (The(a, from)),
            read_back_norm ctx (The(a, _to)))

    | The(VAtom(U), VSigma(a, d)) ->
        let x = get_closure_bound_var d in
        let y = freshen (to_sym_set ctx) x in
        Sigma(
            y,
            read_back_norm ctx (The(VAtom(U), a)),
            read_back_norm (extend_context ctx y a) (The(VAtom(U), apply_closure d (VNeu(a, NVar(y))))))

    | The(_, VNeu(_, ne)) ->
        read_back_neutral ctx ne

    | _ -> 
        raise (RE(ReadbackFailed(norm)))

and read_back_neutral ctx = function
    | NVar(x) -> Symbol(x)
    | NApp(ne, rand) -> App(read_back_neutral ctx ne, read_back_norm ctx rand)
    | NCar(ne) -> Car(read_back_neutral ctx ne)
    | NCdr(ne) -> Cdr(read_back_neutral ctx ne)
    | NInd_Nat(ne, motive, base, step) ->
        Ind_Nat(read_back_neutral ctx ne, read_back_norm ctx motive, read_back_norm ctx base, read_back_norm ctx step)
    | NReplace(ne, motive, base) ->
        Replace(read_back_neutral ctx ne, read_back_norm ctx motive, read_back_norm ctx base)
    | NInd_Absurd(ne, motive) ->
        Ind_Absurd(read_back_neutral ctx ne, read_back_norm ctx motive)

let ( let* ) (o: ('a, 'b) BatResult.t) f =
    match o with
    | Ok(inner) -> f inner
    | Error _ as e -> e

type typed_expression = expression * expression

let rec synth (ctx: context) (e: expression): (typed_expression, type_check_error) BatResult.t =
    let env = context_to_environment ctx in
    match e with
    | The(ty, exp) ->
        let* t_out = check ctx ty (VAtom U) in
        let* e_out = check ctx exp (evaluate env t_out) in
        Ok (t_out, e_out)

    | Atom(U) ->
        Ok (Atom(U), Atom(U))

    | Sigma(x, a, d) ->
        let* a_out = check ctx a (VAtom U) in
        let* d_out = check (extend_context ctx x (evaluate env a_out)) d (VAtom U) in 
        Ok(Atom(U), Sigma(x, a_out, d_out))

    | Car(pair) ->
        let* (pair_ty, pair_out) = synth ctx pair in
        begin match evaluate env pair_ty with
        | VSigma(a, _) ->
            Ok(read_back_norm ctx (The((VAtom U), a)), Car(pair_out))
        | non_sigma ->
            Error(ExpectSigmaGot(non_sigma))
        end

    | Cdr(pair) ->
        let* (pair_ty, pair_out) = synth ctx pair in
        begin match evaluate env pair_ty with
        | VSigma(_, d) ->
            let the_car = evaluate_car (evaluate env pair_out) in
            Ok(read_back_norm ctx (The((VAtom U), apply_closure d the_car)), Cdr(pair_out))
        | non_sigma ->
            Error(ExpectSigmaGot(non_sigma))
        end

    | Atom(a) -> Ok((Atom U), (Atom a))
    | Ind_Nat(target, motive, base, step) ->
        let* target_out = check ctx target (VAtom Nat) in
        let* motive_out = check ctx motive (VPi(VAtom(Nat), HigherOrder{ var = "n"; fn = const (VAtom U); tag = "check_ind_nat_motive_tmp"})) in
        let motive_val = evaluate env motive_out in
        let* base_out = check ctx base (evaluate_apply motive_val (VAtom Zero)) in
        let* step_out = check ctx step (ind_nat_step_type motive_val) in 
        Ok(read_back_norm ctx (The((VAtom(U)), evaluate_apply motive_val (evaluate env target_out))),
           Ind_Nat(target_out, motive_out, base_out, step_out))
    | Eq(a, from, _to) ->
        let* a_out = check ctx a (VAtom(U)) in
        let a_val = evaluate env a_out in
        let* from_out = check ctx from a_val in
        let* to_out = check ctx _to a_val in
        Ok(Atom(U), Eq(a_out, from_out, to_out))
    | Replace(target, motive, base) ->
        let* (target_t, target_out) = synth ctx target in
        begin match evaluate env target_t with
        | VEq(a, from, _to) ->
            let* motive_out = check ctx motive (VPi(a, (HigherOrder { var = "x"; fn = const (VAtom U); tag = "check_replace_motive_out_tmp"}))) in
            let motive_v = evaluate env motive_out in
            let* base_out = check ctx base (evaluate_apply motive_v from) in
            Ok(read_back_norm ctx (The((VAtom U), (evaluate_apply motive_v _to))), Replace(target_out, motive_out, base_out))
        | non_eq ->
            Error(ExpectEqGot(non_eq))
        end
    | Pi(x, a, b) ->
        let* a_out = check ctx a (VAtom U) in
        let* b_out = check (extend_context ctx x (evaluate env a_out)) b (VAtom U) in
        Ok(Atom(U), Pi(x, a_out, b_out))
    | Ind_Absurd(target, motive) ->
        let* target_out = check ctx target (VAtom Absurd) in
        let* motive_out = check ctx motive (VAtom U) in
        Ok(motive_out, Ind_Absurd(target_out, motive_out))
    | App(rator, rand) ->
        let* (rator_t, rator_out) = synth ctx rator in
        begin match (evaluate env rator_t) with
        | VPi(a, b) ->
            let* rand_out = check ctx rand a in
                Ok(
                    read_back_norm ctx (The(VAtom(U), apply_closure b (evaluate env rand_out))), 
                    App(rator_out, rand_out))
        | non_pi ->
            Error(ExpectPiGot(non_pi))
        end
    | Symbol(x) ->
        begin match lookup_context_type x ctx with
        | Some(ty) -> Ok(read_back_norm ctx (The(VAtom(U), ty)), Symbol(x))
        | None -> Error(UndefinedSymbol(x)) 
        end
    | none_of_above ->
        Error(CantSynthesize(none_of_above))

and check (ctx: context) (e: expression) (t: value): (expression, type_check_error) BatResult.t =
    let env = context_to_environment ctx in
    match e with
    | Cons(a, d) ->
        begin match t with
        | VSigma(_a, _d) ->
            let* a_out = check ctx a _a in
            let* d_out = check ctx d (apply_closure _d (evaluate env a_out)) in
                Ok(Cons(a_out, d_out))
        | non_sigma -> Error(ExpectSigmaGot(non_sigma))
        end
    | Atom(Zero) ->
        begin match t with
        | VAtom(Nat) ->
            Ok(Atom(Zero))
        | non_nat -> Error(ExpectNatGot(non_nat))
        end
    | Add1(n) ->
        begin match t with
        | VAtom(Nat) ->
            let* n_out = check ctx n (VAtom(Nat)) in
            Ok(Add1(n_out))
        | non_nat -> Error(ExpectNatGot(non_nat))
        end
    | Atom(Same) -> 
        begin match t with
        | VEq(a, from, _to) ->
            let* _ = convert ctx a from _to in
            Ok(Atom(Same))
        | non_eq -> Error(ExpectEqGot(non_eq))
        end
    | Atom(Sole) ->
        begin match t with
        | VAtom(Trivial) -> Ok(Atom(Sole))
        | non_trivial -> Error(ExpectTrivialGot(non_trivial))
        end
    | Lambda(x, b) ->
        begin match t with
        | VPi(_a, _b) ->
            let x_val = VNeu(_a, NVar(x)) in
            let* b_out = check (extend_context ctx x _a) b (apply_closure _b x_val) in
            Ok(Lambda(x, b_out))
        | non_pi -> Error(ExpectPiGot(non_pi))
        end
    | Atom(Quote(a)) ->
        begin match t with
        | VAtom(Atom) -> Ok(Atom(Quote(a)))
        | non_atom -> Error(ExpectAtomGot(non_atom))
        end
    | _ ->
        let* (t_out, e_out) = synth ctx e in
        let* _ = convert ctx (VAtom(U)) t (evaluate env t_out) in
        Ok(e_out)

and convert (ctx: context) (t: value) (v1: value) (v2: value): (unit, type_check_error) BatResult.t =
    let e1 = read_back_norm ctx (The(t, v1)) in
    let e2 = read_back_norm ctx (The(t, v2)) in
    if alpha_equiv e1 e2 
    then Ok(())
    else Error(ExpectSameTypeGot(v1, v2))

let string_of_expression (e: expression): string =
    "todo"

let interact (ctx: context) (input: statement) =
    let env = context_to_environment ctx in
    match input with
    | Define(sym, e) ->
        begin match StrMap.find_opt sym ctx with
        | Some _ -> Error(DuplicateDefinition(sym))
        | None ->
            let* (ty, exp) = synth ctx e in
            Ok(StrMap.add sym (Def {ty = evaluate env ty; value = evaluate env exp }) ctx )
        end
    | Expr(e) ->
        let* (ty, exp) = synth ctx e in
            (Printf.printf "Type: %s, Normal Form: %s\n"
                (string_of_expression ty)
                (string_of_expression (read_back_norm ctx (The(evaluate env ty, evaluate env exp))));
            Ok(ctx))

let rec run_program ctx inputs = 
    match inputs with
    | [] -> Ok(ctx)
    | input :: rest ->
        let* ctx' = interact ctx input in
            run_program ctx' rest
