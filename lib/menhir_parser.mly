%{
  [@@@coverage exclude_file]
  open Nbe
  exception Unreachable

%}

%token EOF

%token <string> IDENT 
%token FSLASH 
%token DOT
%token LET 
%token EQ 
%token IN 
%token SEMICOL 
%token LPAREN 
%token RPAREN 
%token GLOBAL
%token UNIT
%token THE
%token <int> INT
%token INT_T
%token UNIT_T
%token ARROW

%start <stmt list> program_eof

%%

program_eof:
  | ss=list(statement) EOF { ss }

statement:
  | GLOBAL id=IDENT EQ e=expression SEMICOL { Define(id, e) }
  | e=expression SEMICOL { Expr(e) }

expression:
  | THE ty=nbe_type e=expression {
    EAnnotate(e, ty)
  } 
  | FSLASH id=IDENT DOT bdy=expression { ELam(id, bdy) }
  | LET id=IDENT EQ rhs=expression IN inner=expression { 
    ELetIn(id, rhs, inner) 
  }
  | e=expression_app { e }

expression_app: 
  | es=nonempty_list(expression_simple) {
    match es with
    | [] -> raise Unreachable 
    | e :: es ->
      List.fold_left (fun acc ele -> EApp(acc, ele)) e es
  }

atom: 
  | UNIT { AUnit }
  | i=INT { AInt i }

expression_simple:
  | LPAREN e=expression RPAREN { e }
  | id=IDENT { ESym id }
  | a=atom { EAtom a }

nbe_type:
  | tys=separated_nonempty_list(ARROW, nbe_type_simple) {
    match List.rev tys with
    | [] ->
        raise Unreachable
    | x :: xs ->
      List.fold_left (fun acc ele -> Arrow(ele, acc)) x xs
  }

nbe_type_simple:
  | INT_T { Int }
  | UNIT_T { Unit }
  | LPAREN t=nbe_type RPAREN { t }
