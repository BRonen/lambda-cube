inductive Expr where
  | abs : Expr → Expr
  | app : Expr → Expr → Expr
  | var : Nat → Expr
  | val : Nat → Expr

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
  toString : Expr → String := exprToString

def test := app (abs (var 0)) (abs (var 0))
#eval test
#eval ((List.cons 1 List.nil).cons 2).drop 1

inductive Value where
  | value : Nat → Value
  | closure : List Value → Expr → Value

open Value

mutual
  -- Removed listSize and size as they were primarily used for fuel calculation
  -- and are not strictly necessary for structural recursion in toString.

  def valueToString (v : Value) : String :=
    match v with
     | value v => s!"{v}"
     | closure ctx body =>
        let ctx := ctx.map valueToString
        s!"(τ {ctx} : {body})"
end

instance : ToString Value where
  toString : Value → String := valueToString

-- Renamed eval' to eval and removed fuel parameter
mutual
  partial def eval (ctx : List Value) (expr : Expr) : Except String Value :=
    match expr with
     | val v => Except.ok $ value v
     | var i =>
       match ctx.get? i with
        | some v => Except.ok v
        | none => Except.error s!"Variable not found: {i} inside {expr}"
     | abs body => Except.ok $ closure ctx body
     | app f arg => do
       let arg' ← eval ctx arg
       match ← eval ctx f with
        | closure ctx' body => eval (ctx'.cons arg') body
        | _ => Except.error s!"Trying to apply a non-closure value: {expr}"
end

-- Removed fuelNeeded function

#eval eval List.nil (app (abs (var 0)) (abs (app (var 0) (var 0))))
#eval eval List.nil (app (abs (app (abs (var 0)) (val 5))) (val 3))
