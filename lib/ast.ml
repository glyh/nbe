open Batteries

module StrMap = Map.Make(String) 
module StrSet = Set.Make(String)

type symbol = string

type atom = 
  | Nat
  | Zero
  | Same
  | Trivial
  | Sole
  | Absurd
  | Atom
  | U
  | Quote of string

type expression = 
  | Atom of atom
  | Symbol of symbol
  | Lambda of symbol * expression
  | Pi of symbol * expression * expression
  | Sigma of symbol * expression * expression
  | The of expression * expression
  | Cons of expression * expression
  | App of expression * expression
  | Ind_Absurd of expression * expression
  | Car of expression
  | Cdr of expression
  | Add1 of expression
  | Eq of expression * expression * expression
  | Replace of expression * expression * expression
  | Ind_Nat of expression * expression * expression * expression

type closure = 
  | Transparent of {
    env: environment;
    var: symbol;
    body: expression;
  }
  | HigherOrder of {
    var: symbol;
    fn: value -> value;
    tag: string;
  }

and value =
  | VAtom of atom
  | VPi of value * closure
  | VLambda of closure
  | VSigma of value * closure
  | VPair of value * value
  | VAdd1 of value
  | VEq of value * value * value
  | VNeu of value * neutral
  (*| VThe of value * value*)

and environment = value StrMap.t

and neutral =
  | NVar of symbol
  | NApp of neutral * normal
  | NCar of neutral
  | NCdr of neutral
  | NInd_Absurd of neutral * normal
  | NReplace of neutral * normal * normal
  | NInd_Nat of neutral * normal * normal * normal

and normal = 
  | The of value * value

let get_closure_bound_var = function
  | Transparent { var; _ } -> var
  | HigherOrder { var; _ } -> var

type defintion = {ty: value; value: value}
type bind = {ty: value}

type context_element =
  | Def of defintion
  | Bind of bind

type context = context_element StrMap.t

type sym_set = StrSet.t
let to_sym_set m: sym_set =
  m
  |> StrMap.to_seq
  |> Seq.split
  |> fst
  |> StrSet.of_seq

let rec freshen (used_names: sym_set) (prefix: symbol): symbol =
  if StrSet.mem prefix used_names
  then
    freshen used_names (prefix ^ "'")
  else 
    prefix

type statement =
  | Define of symbol * expression
  | Expr of expression

