namespace LambdaCube.LambdaCalculus

inductive Expr where
  | abs : Expr → Expr
  | app : Expr → Expr → Expr
  | var : Nat → Expr
  | val : Nat → Expr

open Expr

instance : ToString Expr where
  toString :=
    let rec f
    | val v => s!"{v}!"
    | var v => s!"{v}!"
    | abs body => s!"(λ. {f body})"
    | app ap arg => s!"({f ap} {f arg})"
    f

#eval app (abs (var 0)) (abs (var 0))

inductive Value where
  | value : Nat → Value
  | closure : List Value → Expr → Value

open Value

instance : ToString Value where
  toString :=
    let rec f := λv =>
      let rec fs
      | v :: vs => f v ++ fs vs
      | [] => ""
      match v with
      | value v => s!"{v}"
      | closure ctx body => s!"(τ {fs ctx} : {body})"
    f

partial def eval (ctx : List Value) : Expr → Except String Value
| val v => Except.ok $ value v
| var i =>
  match getElem? ctx i with
   | some v => Except.ok v
   | none => Except.error s!"Variable not found: {i}"
| abs body => Except.ok $ closure ctx body
| app f arg => do
  let arg' ← eval ctx arg
  match ← eval ctx f with
   | closure ctx' body => eval (arg' :: ctx') body
   | e => Except.error s!"Trying to apply a non-closure value: {e}"

#eval eval [] (app (abs (var 0)) (abs (app (var 0) (var 0))))
#eval eval [] (app (abs (app (abs (var 0)) (val 5))) (val 3))

end LambdaCube.LambdaCalculus
