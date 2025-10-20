namespace LambdaCube.LambdaPi

inductive E where
| sort  : E -- TODO enable multiple universes
| const : String → E
| lit   : Nat → E
| var   : Nat → E
| pi    : E → E → E
| abs   : E → E → E
| app   : E → E → E
deriving DecidableEq

open E

def size : E → Nat
| sort       => 1
| const _    => 1
| lit _      => 1
| var _      => 1
| pi a b     => 1 + size a + size b
| abs _ body => 1 + size body
| app f arg  => 1 + size f + size arg

instance : ToString E where
  toString :=
    let rec f
    | sort => s!"*"
    | const s => s!"{s} :: *"
    | lit v => s!"{v}"
    | var v => s!"Var<{v}>"
    | pi t body => s!"(Π {f t}. {f body})"
    | abs t body => s!"(λ {f t}. {f body})"
    | app ap arg => s!"{f ap} {f arg}"
    f

#eval (pi (pi sort sort) sort)
#eval (app (abs (pi sort sort) (var 0)) (abs sort (var 0)))

def subst (index : Nat) (e : E) : E → E
| var i => if i == index then e else (var i)
| pi t body => pi (subst index e t) (subst (1 + index) e body)
| abs t body => abs (subst index e t) (subst (1 + index) e body)
| app ap arg => app (subst index e ap) (subst index e arg)
| other => other

def check (Γ : List E) (expr : E) : Except String E :=
  match expr with
  | sort => return sort
  | const _ => return sort
  | lit _ => return const "int"
  | pi _ _ => return sort
  | var i =>
    match getElem? Γ i with
    | some t => pure t
    | none => Except.error s!"Variable not found: {i} inside {Γ}"
  | abs t body => do
    let t' ← check Γ t
    match t' with
    | sort =>
      let body ← check (t' :: Γ) body
      return pi t body
    | _ => Except.error "TODO"
  | app f arg => do
    match ← check Γ f with
    | pi t b =>
      let arg' ← check Γ arg
      if t = arg'
      then return subst 0 arg b
      else Except.error s!"Expected to apply {t} but received {arg'}"
    | f => Except.error s!"Trying to apply value {arg} on a term of type {f}"

-- (λ Int. Var<0>) -> (Π Int. Int)
#eval (abs (const "int") (var 0))
#eval check [] (abs (const "int") (var 0))

-- (λ Int. Var<0>)(1) -> Int :: *
#eval (app (abs (const "int") (var 0)) (lit 1))
#eval check [] (app (abs (const "int") (var 0)) (lit 1))

-- (λ *. (λ Var<0>. Var<0>)) -> (Π *. (Π Var<0>. Var<1>))
#eval (pi sort (pi (var 0) (var 1)))
#eval check [] (abs sort (abs (var 0) (var 1)))

-- (λ *. (λ Var<0>. Var<0>))(Int :: *) -> (Π Int :: *. Var<1>)
#eval (app (abs sort (abs (var 0) (var 1))) (const "int"))
#eval check [] (app (abs sort (abs (var 0) (var 1))) (const "int"))

-- (λ *. (λ Var<0>. Var<0>))(Int :: *)(2) -> Int :: *
#eval (app (app (abs sort (abs (var 0) (var 0))) (const "int")) (lit 2))
#eval check [] (app (app (abs sort (abs (var 0) (var 0))) (const "int")) (lit 2))

-- (λ (Π *. *). Var<0>) -> (Π (Π *. *). (Π *. *))
#eval (abs (pi sort sort) (var 0))
#eval check [] (abs (pi sort sort) (var 0))

-- (λ (Π *. *). Var<0>)(λ *. Var<0>) -> (Π *. *)
#eval (app (abs (pi sort sort) (var 0)) (abs sort (var 0)))
#eval check [] (app (abs (pi sort sort) (var 0)) (abs sort (var 0)))

-- the examples below still fail

-- (λ (Π *. *). Var<0>)(λ (Int :: *). Var<0>)(3) -> Int :: *
#eval (app (app (app (abs (pi sort (pi (var 0) (var 0)))
                          (var 0))
                     (abs sort (abs (var 0) (var 0))))
                (const "int"))
           (lit 3))


#eval check [] (app (app (abs (pi sort (pi (var 0) (var 0))) (var 0)) (abs sort (abs (var 0) (var 0)))) (const "int"))
#eval check [] (app (app (app (abs (pi sort (pi (var 0) (var 0))) (var 0)) (abs sort (abs (var 0) (var 0)))) (const "int")) (lit 3))

end LambdaCube.LambdaPi
