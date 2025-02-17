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

mutual
  def listSize (l : List Value) : Nat :=
    match l with
     | []      => 0
     | v :: vs => size v + listSize vs

  def size (v : Value) : Nat :=
    match v with
     | value _ => 1
     | closure ctx _ => 1 + listSize ctx
end

def valueToString (fuel : Nat) (v : Value) : String :=
  match fuel, v with
   | 0, _ => ""
   | _, value v => s!"{v}"
   | fuel' + 1, closure ctx body =>
      let ctx := ctx.map (valueToString fuel')
      s!"(τ {ctx} : {body})"

instance : ToString Value where
  toString (v : Value) : String := valueToString (size v) v

def eval' (fuel : Nat) (ctx : List Value) (expr : Expr) : Except String Value :=
  match fuel with
   | 0 => Except.error "Fuel not enough"
   | fuel' + 1 =>
     match expr with
      | val v => Except.ok (value v)
      | var i =>
        match ctx.get? i with
         | some v => Except.ok v
         | none => Except.error s!"Variable not found: {i} inside {expr}"
      | abs body => Except.ok (closure ctx body)
      | app f arg =>
        match eval' fuel' ctx arg with
         | Except.ok arg' =>
           match eval' fuel' (ctx.cons arg') f with
            | Except.ok (closure ctx body) => eval' fuel' ctx body
            | other => other
         | other => other

def fuelNeeded : Expr → Nat
  | Expr.val _ => 1
  | Expr.var _ => 1
  | Expr.abs body => 1 + fuelNeeded body
  | Expr.app f arg => 1 + fuelNeeded f + fuelNeeded arg

def eval ctx expr := eval' (fuelNeeded expr) ctx expr

def expr := (app (abs (app (abs (var 0)) (val 5))) (val 3))

#eval expr
#eval fuelNeeded expr
#eval eval List.nil expr
