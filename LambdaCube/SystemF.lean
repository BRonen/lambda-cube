namespace LambdaCube.SystemF

-- types

inductive T where
| tint    : T
| tstr    : T
| tvar    : Nat → T
| tarrow  : T → T → T
| tforall : T → T
deriving DecidableEq

open T

def sizeT
| tint        => 1
| tstr        => 1
| tvar    _   => 1
| tarrow  a r => 1 + sizeT a + sizeT r
| tforall r   => 1 + sizeT r

def substT (i : Nat) (ty : T)
| tvar    n   => if n = i then ty else tvar n
| tarrow  t b => tarrow (substT i ty t) (substT i ty b)
| tforall b   => tforall $ substT (i + 1) ty b
| e => e

instance : ToString T where
  toString :=
    let rec f
    | tint        => "Int"
    | tstr        => "Str"
    | tvar    v   => s!"Var({v})"
    | tarrow  a r => s!"(λ{f a}. {f r})"
    | tforall r   => s!"(∀. {f r})"
    f

#eval (tforall (tarrow tint tstr))

-- terms

inductive E where
| eint    : Int → E
| estr    : String → E
| evar    : Nat → E
| eapp    : E → E → E
| eapt    : E → T → E
| earrow  : T → E → E
| eforall : E → E

open E

def sizeE
| eint    _   => 1
| estr    _   => 1
| evar    _   => 1
| eapp    f a => 1 + sizeE f + sizeE a
| eapt    t y => 1 + sizeE t + sizeT y
| earrow  t b => 1 + sizeT t + sizeE b
| eforall b   => 1 + sizeE b

instance : ToString E where
  toString :=
    let rec ts
    | eint    n   => s!"Nat({n})"
    | estr    s   => s!"String({s})"
    | evar    v   => s!"Var({v})"
    | eapp    f a => s!"({ts f} {ts a})"
    | eapt    t y => s!"[{ts t} {toString y}]"
    | earrow  t b => s!"(λ {toString t}. {ts b})"
    | eforall b   => s!"(∀. {ts b})"
    ts

#eval (eforall (earrow tint (estr "hello world")))

def check (Γ : List T) (term : E) : Except String T :=
  match term with
  | eint _ => pure tint
  | estr _ => pure tstr
  | earrow t b => do
    pure $ tarrow t (← check (t :: Γ) b)
  | eforall b => do
    pure $ tforall (← check Γ b)
  | evar v =>
    match Γ.get? v with
    | some v => pure v
    | none   => Except.error s!"Trying to access not defined variable: {term}"
  | eapp f a => do
    let f ← check Γ f
    let a ← check Γ a
    match f with
    | tarrow t b =>
      if t = a
      then pure b
      else Except.error s!"Expected to apply {t} but received {a}"
    | _        => Except.error s!"Trying to apply value {a} on a term of type {f}"
  | eapt f a => do
    let f ← check Γ f
    match f with
    | tforall b => pure (substT 0 a b)
    | _        => Except.error s!"Trying to apply value {a} on a term of type {f}"

#eval check [] (eapp (earrow tstr (eint 2)) (estr "hello world"))
#eval check [] (eapp (earrow tint (eint 2)) (estr "hello world"))
#eval check [] (eforall (earrow (tvar 0) (eint 1)))
#eval check [] (eapt (eforall (earrow (tvar 0) (eint 1))) tint)
#eval check [] (eapp (eapt (eforall (earrow (tvar 0) (evar 0))) tint) (eint 3))
#eval check [] (eapp (eapt (eforall (earrow (tvar 0) (evar 0))) tstr) (eint 3))
#eval check [] (eapp (eapt (eforall (earrow (tvar 0) (evar 0))) tint) (estr "3"))
#eval check [] (eapp (earrow (tarrow tint tint) (eapp (evar 0) (eapp (evar 0) (eint 3)))) (earrow tint (eint 3)))
#eval check [] (eapp (eapp (earrow tint (earrow (tarrow tint tint) (eapp (evar 0) (evar 1)))) (eint 3)) (earrow tint (evar 0)))
