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
  | VFix of closure
  | VAtom of atom
  | VNeu of neutral

and neutral = 
  | NId of symbol
  | NApp of neutral * normal

and expr = 
  | EAnnotate of expr * nbe_type
  | EAtom of atom
  | ESym of symbol
  | EApp of expr * expr
  | EFix of expr
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

let rec reify (env: env) (expr: expr): normal =
  match expr with
  | ELam(x, bdy) -> VClos { env=env; var=x; body=bdy }
  | EApp(lhs, rhs) -> apply (reify env lhs) (reify env rhs)
  | ELetIn(x, rhs, inner) -> 
      apply (VClos {env = env; var=x; body=inner}) (reify env rhs) 
  | ESym(sym) ->
      begin match StrMap.find_opt sym env with
      | Some(v) -> v
      | None -> raise (UndefinedVariable sym)
      end
  | EAtom a -> VAtom a
  | EAnnotate(inner, _) -> reify env inner
  | EFix(exp) -> 
      let inner_refied = reify env exp in
      begin match inner_refied with
      | VClos closure -> 
          VFix closure
      | e -> e
      end

and apply (f: normal) (x: normal) =
  match f with
  | (VFix _f) as y_f ->
      let f = VClos _f in
      apply (apply f y_f) x
  | VClos { env; var; body } ->
      reify (StrMap.add var x env) body
  | VNeu(f) -> VNeu(NApp(f, x))
  | VAtom _ -> raise Unreachable

let rec freshen (used_names: sym_set) (prefix: symbol): symbol =
  if StrSet.mem prefix used_names
  then
    freshen used_names (prefix ^ "'")
  else 
    prefix

let rec reflect (used_names: sym_set) (v: normal): expr =
  match v with
  | VClos { env; var; body } ->
      let var' = freshen used_names var in
      let neu_var' = VNeu (NId var') in
      let used_names' = (StrSet.add var' used_names) in
      let env' = StrMap.add var neu_var' env in
      ELam(var', reflect used_names' (reify env' body))
  | VFix clos ->
      EFix (reflect used_names (VClos clos))
  | VAtom a -> EAtom a
  | VNeu(NId(id)) -> ESym(id)
  | VNeu(NApp(lhs, rhs)) ->
      EApp(reflect used_names (VNeu(lhs)), reflect used_names rhs)

let normalize (rho: env) (e: expr) =
  reflect StrSet.empty (reify rho e)

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
  | EAnnotate(exp, ty) -> Printf.sprintf "(%s :: %s)" (string_of_expr exp) (string_of_type ty)
  | EFix(exp) -> Printf.sprintf "(fix %s)" (string_of_expr exp)

let rec run_program (env: env) (exprs: stmt list): normal =
  match exprs with
  | [] -> VAtom AUnit
  | [Expr(e)] -> 
      reify env e
  | Define(lhs, rhs) :: rest ->
      let rhs_v = reify env rhs in
      let env' = StrMap.add lhs rhs_v env in
      run_program env' rest
  | Expr(e) :: rest ->
      Printf.printf "%s\n" (normalize env e |> string_of_expr); 
      run_program env rest

type context = nbe_type StrMap.t

type type_err =
  | VariableUndefined of symbol
  | ExpectingFunction of expr * nbe_type
  | ExpectingFunctionType of nbe_type
  | ExpectingAnnotation of expr
  | TypeMismatch of nbe_type * nbe_type

let type_of_atom (a: atom): nbe_type =
  match a with
  | AUnit -> Unit
  | AInt _ -> Int

let rec synth_type (ctx: context) (e: expr): (nbe_type, type_err) Result.t =
  match e with
  | EAnnotate(exp, ty) ->
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
  | EFix(f) -> (* Fix: A -> B -> B *)
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
