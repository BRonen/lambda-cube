namespace Llean.Stlc

inductive TExpr where
  | abst : TExpr → TExpr
  | intt : TExpr
deriving DecidableEq

open TExpr

instance : ToString TExpr where
  toString :=
    let rec f := λt =>
      match t with
      | abst c => s!"(∀ {f c})"
      | intt => s!"ℕ"
    f

inductive Expr where
  | abs : TExpr → Expr → Expr
  | app : Expr → Expr → Expr
  | var : Nat → Expr
  | val : Nat → Expr

open Expr

def size : Expr → Nat
  | Expr.val _ => 1
  | Expr.var _ => 1
  | Expr.abs _ body => 1 + size body
  | Expr.app f arg => 1 + size f + size arg

instance : ToString Expr where
  toString :=
    let rec f
    | val v => s!"{v}"
    | var v => s!"{v}!"
    | abs t body => s!"(λ {t}. {f body})"
    | app ap arg => s!"({f ap} {f arg})"
    f

def test := app (abs (abst intt) (var 0)) (abs intt (var 0))
#eval test
#eval ((List.cons 1 List.nil).cons 2).drop 1

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

def check' (fuel : Nat) (ctx : List TExpr) (expr : Expr) : Except String TExpr :=
  if fuel = 0 then
    Except.error s!"Fuel not enough to check: {expr} with {ctx}"
  else
    let fuel' := fuel - 1
    match expr with
     | val _ => Except.ok intt
     | var i =>
       match ctx.get? i with
        | some t => pure t
        | none => Except.error s!"Variable not found: {i} inside {ctx}"
     | abs t body => do
       let _ ← check' fuel' (ctx.cons t) body
       pure $ abst t
     | app f arg => do
       let arg' ← check' fuel' ctx arg
       match f with
        | abs t body =>
          if t = arg' then
            check' fuel' (ctx.cons t) body
          else
            Except.error s!"Trying to apply {arg'} instead of {t}: {expr}"
        | var i =>
          match ctx.get? i with
           | none => Except.error s!"Variable not found: {i} inside {ctx}"
           | some t =>
             if t == abst arg' then
               check' fuel' (ctx.cons t) f
             else
               Except.error s!"!Trying to apply {arg'} instead of {t}: {expr}"
        | _ => Except.error s!"Trying to apply a non-closure value: {expr}"

def eval' (fuel : Nat) (ctx : List Value) (expr : Expr) : Except String Value :=
  if fuel = 0 then
    Except.error "Fuel not enough to evaluate: {expr} with {ctx}"
  else
    let fuel' := fuel - 1
    match expr with
     | val v => Except.ok $ value v
     | var i =>
       match ctx.get? i with
        | some v => Except.ok v
        | none => Except.error s!"Variable not found: {i} inside {ctx}"
     | abs _ body => Except.ok $ closure ctx body
     | app f arg => do
       let arg' ← eval' fuel' ctx arg
       match ← eval' fuel' ctx f with
        | closure ctx' body => eval' fuel' (ctx'.cons arg') body
        | _ => Except.error s!"Trying to apply a non-closure value: {expr}"

#eval size (app (abs intt (var 0)) (abs intt (app (var 0) (var 0))))
#eval size (app (abs intt (app (abs intt (var 0)) (val 5))) (val 3))

def check ctx expr := check' (size expr) ctx expr
def eval ctx expr := eval' (size expr) ctx expr

#eval check List.nil
      (abs intt (var 0))
#eval check List.nil
      (abs (abst intt) (app (var 0) (val 1)))
#eval check
      List.nil (app (abs (abst (abst intt)) (var 0))
                    (abs (abst intt) (app (var 0) (val 1))))
#eval check List.nil (app (abs intt (app (abs intt (var 0)) (val 5))) (val 3))

#eval eval List.nil (app (abs (abst (abst intt)) (var 0)) (abs intt (app (var 0) (val 1))))
#eval eval List.nil (app (abs intt (app (abs intt (var 0)) (val 5))) (val 3))

end Llean.Stlc
