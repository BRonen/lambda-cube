namespace LambdaCube.LambdaPi

inductive T where
| sort : T
| base : String → T
| pi   : T → T → T
deriving DecidableEq

open T

instance : ToString T where
  toString :=
    let rec f
    | sort => s!"*"
    | base s => s!"({s} :: *)"
    | pi a b => s!"(Π {f a}. {f b})"
    f

#eval (pi (pi (base "int") (base "int")) (base "int"))

inductive E where
| var  : Nat → E
| abs  : T → E → E
| app  : E → E → E
| type : T → E
| int  : Nat → E

open E

def size : E → Nat
| var _      => 1
| abs _ body => 1 + size body
| app f arg  => 1 + size f + size arg
| type _     => 1
| int _      => 1

instance : ToString E where
  toString :=
    let rec f
    | var v => s!"Var({v})"
    | abs t body => s!"(λ {t}. {f body})"
    | app ap arg => s!"({f ap} {f arg})"
    | type t => s!"[{t}]"
    | int v => s!"{v}"
    f

#eval (app (abs (pi (base "int") (base "int")) (var 0)) (abs (base "int") (var 0)))

def check (Γ : List T) (expr : E) : Except String T :=
  match expr with
  | int _ => Except.ok (base "int")
  | type _ => Except.ok sort
  | var i =>
    match getElem? Γ i with
    | some t => pure t
    | none => Except.error s!"Variable not found: {i} inside {Γ}"
  | abs t body => do
    let b ← check (t :: Γ) body
    pure $ pi t b
  | app f arg => do
    let arg' ← check Γ arg
    let f' ← check (arg' :: Γ) f
    match f' with
    | pi t b =>
      if t = arg'
      then pure b
      else Except.error s!"Expected to apply {t} but received {arg'}"
    | _ => Except.error s!"Trying to apply value {arg'} on a term of type {f'}"

#eval check [] (app (abs (base "int") (var 0)) (int 1))
#eval check [] (abs (pi (base "int") (base "int")) (var 0))
#eval check [] (app (abs (pi (base "int") (base "int")) (var 0)) (abs (base "int") (var 0)))
#eval check [] (app (app (abs (pi (base "int") (base "int")) (var 0)) (abs (base "int") (var 0))) (int 3))

end LambdaCube.LambdaPi
