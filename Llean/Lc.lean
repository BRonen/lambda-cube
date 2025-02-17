inductive Expr where
  | abs : Expr -> Expr
  | app : Expr -> Expr -> Expr
  | var : Nat -> Expr
  | val : Nat -> Expr

open Expr

def exprToString (e : Expr) : String :=
  match e with
   | val v => s!"{v}!"
   | var v => s!"{v}!"
   | abs body =>
      let body : String := exprToString body
      s!"(λ. {body})"
   | app f arg =>
      let arg : String := exprToString arg
      let f : String := exprToString f
      s!"({f} {arg})"

instance : ToString Expr where
  toString : Expr -> String := exprToString

def test := app (abs (var 0)) (abs (var 0))
#eval println! test

#eval ((List.cons 1 List.nil).cons 2).drop 1

inductive Value where
  | value : Nat -> Value
  | closure : List Value -> Expr -> Value

open Value

def valueToString (v : Value) : String :=
  match v with
   | value v => s!"{v}"
   | closure ctx body =>
      let ctx := ctx.map valueToString
      s!"(τ {ctx} : {body})"
  decreasing_by sorry

instance : ToString Value where
  toString : Value -> String := valueToString

def eval (ctx : List Value) (expr : Expr) : Option Value :=
  match expr with
   | val v => some (value v)
   | var i =>
     match ctx.get? i with
      | some v => some v
      | none => none
   | abs body => some (closure ctx body)
   | app f arg =>
     match eval ctx arg with
      | none => none
      | some param =>
        let f := eval (ctx.cons param) f
        match f with
         | some (closure ctx body) => eval ctx body
         | f => f
  decreasing_by sorry

#eval eval
  List.nil
  (app (abs (app (abs (var 0)) (val 5))) (val 3))

