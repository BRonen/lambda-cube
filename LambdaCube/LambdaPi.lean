namespace LambdaCube.LambdaPi

inductive E where
| sort  : Nat → E
| const : String → E
| lit   : Nat → E
| var   : Nat → E
| pi    : E → E → E
| abs   : E → E → E
| app   : E → E → E
deriving DecidableEq

open E

def size : E → Nat
| sort _     => 1
| const _    => 1
| lit _      => 1
| var _      => 1
| pi a b     => 1 + size a + size b
| abs _ body => 1 + size body
| app f arg  => 1 + size f + size arg

instance : ToString E where
  toString :=
    let rec f
    | sort n => s!"Type_{n}"
    | const s => s!"Const_{s}"
    | lit v => s!"{v}"
    | var v => s!"Var<{v}>"
    | pi t body => s!"(Π {f t}. {f body})"
    | abs t body => s!"(λ {f t}. {f body})"
    | app ap arg => s!"{f ap} {f arg}"
    f

#eval (pi (pi (sort 0) (sort 0)) (sort 0))
#eval (app (abs (pi (sort 0) (sort 0)) (var 0)) (abs (sort 0) (var 0)))

def subst (index : Nat) (e : E) : E → E
| var i => if i == index then e else (var i)
| pi t body => pi (subst index e t) (subst index e body)
| abs t body => abs (subst index e t) (subst (1 + index) e body)
| app ap arg => app (subst index e ap) (subst index e arg)
| other => other

def norm (e : E) (gas : Nat) : E :=
  if gas = 0
  then e
  else match e with
  | app (abs _ body) arg =>
    let body := subst 0 arg body
    norm body (gas - 1)
  | app f arg => app (norm f gas) (norm arg gas)
  | abs t b => abs (norm t gas) (norm b gas)
  | pi t b => pi (norm t gas) (norm b gas)
  | other => other

def conv (a b : E) : Bool :=
  norm a (size a) = norm b (size b)

def check (Γ : List E) (expr : E) : Except String E :=
  match expr with
  | sort n => return sort (n + 1)
  | const _ => return sort 0
  | lit _ => return const "int"
  | pi a b => do
    let ka ← check Γ a
    let kb ← check (a :: Γ) b
    match ka, (subst 0 ka kb) with
    | sort i, sort j => return sort (max i j)
    | a, b => Except.error s!"Pi must connect types but received: {a} - {b}"
  | var i =>
    match getElem? Γ i with
    | some t => return t
    | none => Except.error s!"Variable not found: {i} inside {Γ}"
  | abs t body => do
    match ← check Γ t with
    | sort _ =>
      let body' ← check (t :: Γ) body
      return pi t body'
    | _ => Except.error "Abstraction first argument must be a Type"
  | app f arg => do
    match ← check Γ f with
    | pi t b =>
      let arg' ← check Γ arg
      if conv t arg'
      then let b := subst 0 arg b
           return norm b (size b)
      else Except.error s!"Expected to apply {t} but received {arg'}"
    | f => Except.error s!"Trying to apply value {arg} on a term of type {f}"

-- (λ Int. Var<0>) -> (Π Int. Int)
#eval (abs (const "int") (var 0))
#eval check [] (abs (const "int") (var 0))

-- (λ Int. Var<0>)(1) -> Int :: *
#eval (app (abs (const "int") (var 0)) (lit 1))
#eval check [] (app (abs (const "int") (var 0)) (lit 1))

-- (λ *. (λ Var<0>. Var<0>)) -> (Π *. (Π Var<0>. Var<0>))
#eval (pi (sort 0) (pi (var 0) (var 0)))
#eval check [] (abs (sort 0) (abs (var 0) (var 0)))

-- (λ *. (λ Var<0>. Var<0>))(Int :: *) -> (Π Int :: *. Int :: *)
#eval (app (abs (sort 0) (abs (var 0) (var 0))) (const "int"))
#eval check [] (app (abs (sort 0) (abs (var 0) (var 0))) (const "int"))

-- (λ *. (λ Var<0>. Var<0>))(Int :: *)(2) -> Int :: *
#eval (app (app (abs (sort 0) (abs (var 0) (var 0))) (const "int")) (lit 2))
#eval check [] (app (abs (const "int") (lit 3)) (app (app (abs (sort 0) (abs (var 0) (var 0))) (const "int")) (lit 2)))

-- (λ *. (λ Var<0>. Var<0>))(Int :: *) -> (Π Int :: *. Int :: *)
#eval (app (abs (sort 0) (abs (var 0) (var 0))) (const "int"))
#eval check [] (app (abs (sort 0) (abs (var 0) (var 0))) (const "int"))

-- (λ *. (λ Var<0>. Var<0>))(Int :: *)(3) -> Int :: *
#eval (app (app (abs (sort 0) (abs (var 0) (var 0))) (const "int")) (lit 3))
#eval check [] (app (app (abs (sort 0) (abs (var 0) (var 0))) (const "int")) (lit 3))

-- (λ (Π *. *). Var<0>) -> (Π (Π *. *). (Π *. *))
#eval (abs (pi (sort 0) (sort 0)) (var 0))
#eval check [] (abs (pi (sort 0) (sort 0)) (var 0))

-- (λ (Π *. *). Var<0>)(λ *. Var<0>) -> (Π *. *)
#eval (app (abs (pi (sort 0) (sort 0)) (var 0)) (abs (sort 0) (var 0)))
#eval check [] (app (abs (pi (sort 0) (sort 0)) (var 0)) (abs (sort 0) (var 0)))

-- (λ *. (λ (Π Var<0>. Var<0>). Var<0>))(Int :: *)(λ (Int :: *). Var<0>) -> (Π Int :: *. Int :: *)
#eval (app (app (abs (sort 0) (abs (pi (var 0) (var 0)) (var 0))) (const "int")) (abs (const "int") (var 0)))
#eval check [] (app (app (abs (sort 0) (abs (pi (var 0) (var 0)) (var 0))) (const "int")) (abs (const "int") (var 0)))

-- (λ *. (λ (Π Var<0>. Var<0>). Var<0>))(Int :: *)(λ (Int :: *). Var<0>)(3) -> Int :: *
#eval (app (app (app (abs (sort 0) (abs (pi (var 0) (var 0)) (var 0))) (const "int")) (abs (const "int") (var 0))) (lit 3))
#eval check [] (app (app (app (abs (sort 0) (abs (pi (var 0) (var 0)) (var 0))) (const "int")) (abs (const "int") (var 0))) (lit 3))

-- (λ (λ *. Var<0>)(Int :: *). Var<0>)(42)
#eval (app (abs (app (abs (sort 0) (var 0)) (const "int")) (var 0)) (lit 42))
#eval check [] (app (abs (app (abs (sort 0) (var 0)) (const "int")) (var 0)) (lit 42))

end LambdaCube.LambdaPi
