open Fmlib_std.Result

type symbol = string

module StrMap = Map.Make(String)
module StrSet = Set.Make(String)

type sym_set = StrSet.t

type nbe_type = 
  | Unit
  | Int
  | Arrow of nbe_type * nbe_type

type atom = 
  | AUnit
  | AInt of int

type normal = (* or 'normal' *)
  | VClos of closure
  | VFix of nbe_type (* A *) * closure (* A -> B*)
  | VAtom of atom
  | VNeu of nbe_type * neutral
  | VThe of nbe_type * normal

and neutral = 
  | NId of symbol
  | NApp of neutral * normal

and expr = 
  | EThe of nbe_type * expr 
  | EAtom of atom
  | ESym of symbol
  | EApp of expr * expr
  | EFix of nbe_type (* A *) * expr (* A -> B *)
  | ELetIn of symbol * expr * expr
  | ELam of symbol * expr (* needs annotation *)

and closure = {
  env: env;
  var: symbol;
  body: expr;
}

and env = normal StrMap.t

exception Unimplemented
exception Unreachable
exception UndefinedVariable of symbol
exception Uncallable of normal
exception ExpectCallable of nbe_type
exception NeedAnnotation

let rec evaluate (env: env) (expr: expr): normal =
  match expr with
  | ELam(x, bdy) -> VClos { env=env; var=x; body=bdy }
  | EApp(lhs, rhs) -> apply (evaluate env lhs) (evaluate env rhs)
  | ELetIn(x, rhs, inner) -> 
      apply (VClos {env = env; var=x; body=inner}) (evaluate env rhs) 
  | ESym(sym) ->
      begin match StrMap.find_opt sym env with
      | Some(v) -> v
      | None -> raise (UndefinedVariable sym)
      end
  | EAtom a -> VAtom a
  | EThe(_, inner) -> evaluate env inner
  | EFix(ty, exp) -> 
      let inner_refied = evaluate env exp in
      begin match inner_refied with
      | VClos clos -> 
          VFix(ty, clos)
      | VFix _ as fixed -> fixed
      | _ -> raise (ExpectCallable(ty))
      end

and apply (f: normal) (x: normal) =
  match f with
  | (VFix(_, _f)) as y_f ->
      let f = VClos _f in
      apply (apply f y_f) x
  | VClos { env; var; body } ->
      evaluate (StrMap.add var x env) body
  | VNeu(Arrow(a, b), f) -> 
      VNeu(b, NApp(f, VThe(a, x)))
  | VNeu _ -> raise (Uncallable(f))
  | VAtom _ -> raise Unreachable
  | VThe (_, f') ->
      apply f' x 

let rec freshen (used_names: sym_set) (prefix: symbol): symbol =
  if StrSet.mem prefix used_names
  then
    freshen used_names (prefix ^ "'")
  else 
    prefix

(* Inrepreter *)

type stmt =
  | Define of symbol * expr 
  | Expr of expr

let rec string_of_type (ty: nbe_type): string =
  match ty with
  | Unit -> "Unit"
  | Int -> "Int"
  | Arrow(lhs, rhs) -> Printf.sprintf "%s -> (%s)" (string_of_type lhs) (string_of_type rhs)

let string_of_atom = function
  | AUnit -> "()"
  | AInt i -> string_of_int i

let rec string_of_expr (e: expr): string =
  match e with
  | ELam(var, bdy) -> Printf.sprintf "(\\%s.%s)" var (string_of_expr bdy)
  | EApp(lhs, rhs) -> Printf.sprintf "(%s %s)" (string_of_expr lhs) (string_of_expr rhs)
  | ELetIn(var, rhs, inner) -> Printf.sprintf "(let %s = %s in %s)" var (string_of_expr rhs) (string_of_expr inner)
  | ESym(sym) -> sym
  | EAtom a -> string_of_atom a
  | EThe(exp, ty) -> Printf.sprintf "(the %s %s)" (string_of_type exp) (string_of_expr ty)
  | EFix(ty_a, exp) -> Printf.sprintf "(fix %s. %s)" (string_of_type ty_a) (string_of_expr exp)

type context = nbe_type StrMap.t

type type_err =
  | VariableUndefined of symbol
  | ExpectingFunction of expr * nbe_type
  | ExpectingFunctionType of nbe_type
  | ExpectingAnnotation of expr
  | ExpectingAnnotationNe of neutral
  | TypeMismatch of nbe_type * nbe_type

let type_of_atom (a: atom): nbe_type =
  match a with
  | AUnit -> Unit
  | AInt _ -> Int

let rec read_back (used_names: sym_set) (ty: nbe_type) (v: normal): (expr, type_err) Result.t=
  match ty, v with
  | ty, VAtom a -> 
      if 0 = compare ty (type_of_atom a)
      then Ok(EAtom a)
      else Error(TypeMismatch(ty, type_of_atom a))
  | ty_expected, VNeu(ty_marked, ne) ->
      if 0 = compare ty_marked ty_expected
      then read_back_neutral used_names ne
      else Error(TypeMismatch(ty_marked, ty_expected))
  | Arrow(a, b), VClos { env; var; body } ->
      let var' = freshen used_names var in
      let neu_var' = VNeu(a, (NId var')) in
      let used_names' = (StrSet.add var' used_names) in
      let env' = StrMap.add var neu_var' env in
      let* inner = read_back used_names' b (evaluate env' body) in
      Ok(ELam(var', inner))
  | ty, VClos _ ->
      Error(ExpectingFunctionType(ty))
  | b, VFix(a, inner) ->
      let* inner' = read_back used_names (Arrow(a, b)) (VClos inner) in
      Ok(EFix(a, inner'))
  | ty_expected, VThe(ty_marked, inner) ->
      if 0 = compare ty_marked ty_expected
      then read_back used_names ty_marked inner
      else Error(TypeMismatch(ty_marked, ty_expected))

and read_back_neutral (used_names: sym_set) (ne: neutral): (expr, type_err) Result.t =
  match ne with
  | NId(id) -> Ok(ESym(id))
  | NApp(f, VThe(x_type, x)) ->
      let* lhs = read_back_neutral used_names f in
      let* rhs = read_back used_names x_type x in
        Ok(EApp(lhs, rhs))
  | NApp _ ->
      Error(ExpectingAnnotationNe(ne))

type def = nbe_type * normal 
type defs = def StrMap.t

let normalize (rho: env) (ty: nbe_type) (e: expr) =
  read_back StrSet.empty ty (evaluate rho e)

let defs_to_ctx (defs: defs): context =
  StrMap.map fst defs

let defs_to_env (defs: defs): env =
  StrMap.map snd defs

let to_sym_set (map: 'a StrMap.t): sym_set =
  map |> StrMap.to_seq |> Seq.split |> fst |> StrSet.of_seq

let rec synth_type (ctx: context) (e: expr): (nbe_type, type_err) Result.t =
  match e with
  | EThe(ty, exp) ->
      let* _ = check_type ctx exp ty 
      in Ok(ty)
  | EAtom a -> Ok(type_of_atom a)
  | ESym(sym) ->
      begin match StrMap.find_opt sym ctx with
      | Some(ty) -> Ok(ty)
      | None -> Error(VariableUndefined(sym))
      end
  | EApp(f, x) ->
      let* f_ty = synth_type ctx f in
      begin match f_ty with
      | Arrow(input, output) ->
          let* _ = check_type ctx x input in
          Ok(output)
      | _ -> Error(ExpectingFunction(f, f_ty))
      end
  | EFix(_, f) -> (* Fix: A -> B -> B *)
      let* f_ty = synth_type ctx f in
      begin match f_ty with
      | Arrow(_, output) -> Ok(output)
      | _ -> Error(ExpectingFunction(f, f_ty))
      end
  | ELetIn(sym, rhs, inner) ->
      let* rhs_ty = synth_type ctx rhs in
      let ctx' = StrMap.add sym rhs_ty ctx in
      synth_type ctx' inner
  | _ -> 
      Error(ExpectingAnnotation(e))

and check_type (ctx: context) (e: expr) (ty: nbe_type): (unit, type_err) Result.t = 
  match (e, ty) with
  | ELam(var, bdy), Arrow(input, output) -> 
      check_type (StrMap.add var input ctx) bdy output
  | ELam _, _ -> 
      Error(ExpectingFunctionType(ty))
  | _, _ -> 
      let* type_expected = synth_type ctx e in
      if 0 = compare type_expected ty
      then 
        Ok(())
      else
        Error(TypeMismatch(ty, type_expected))

let rec check_program (ctx: context) (prog: stmt list): (context, type_err) Result.t =
  match prog with
  | [] -> Ok(ctx)
  | Define(sym, exp) :: prog_rest ->
      let* ty = synth_type ctx exp 
      in check_program (StrMap.add sym ty ctx) prog_rest
  | Expr(e) :: prog_rest ->
      let* ty = synth_type ctx e in 
      Printf.printf "%s has type %s" (string_of_expr e) (string_of_type ty);
      check_program ctx prog_rest

let rec run_program (defs: defs) (exprs: stmt list): (defs, type_err) Result.t =
  match exprs with
  | [] -> Ok(defs)
  | Define(lhs, rhs) :: rest ->
      let* t = synth_type (defs_to_ctx defs) rhs in
      let v = evaluate (defs_to_env defs) rhs in
      let defs' = StrMap.add lhs (t, v) defs in
      run_program defs' rest
(*let rec read_back (used_names: sym_set) (ty: nbe_type) (v: normal): (expr, type_err) Result.t=*)
  | Expr(e) :: rest ->
      let* t = synth_type (defs_to_ctx defs) e in
      let v = evaluate (defs_to_env defs) e in
      let* v_exp = (read_back (to_sym_set defs) t v) in
      let v_str = string_of_expr v_exp in
      Printf.printf "the %s %s\n" (string_of_type t) v_str; 
      run_program defs rest

