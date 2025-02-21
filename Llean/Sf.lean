namespace Llean.sf

-- typesystem values
inductive Ty where
  | int : Ty
  | str : Ty
  | abs : Ty → Ty → Ty
  | all : Ty → Ty
  | var : Nat → Ty
deriving DecidableEq

def measureTy t :=
  match t with
  | Ty.int     => 1
  | Ty.str     => 1
  | Ty.abs a r => 1 + measureTy a + measureTy r
  | Ty.all r   => 1 + measureTy r
  | Ty.var _   => 1

instance : ToString Ty where
  toString t :=
    let rec f := λ t =>
      match t with
      | Ty.int     => "Int"
      | Ty.str     => "Str"
      | Ty.abs a r => s!"(λ{f a}. {f r})"
      | Ty.all r   => s!"(∀. {f r})"
      | Ty.var v   => s!"Var({v})"
    f t

#eval (Ty.all (Ty.abs Ty.int Ty.str))

-- system terms
inductive Te where
  | int : Int → Te
  | str : String → Te
  | abs : Ty → Te → Te
  | all : Te → Te
  | var : Nat → Te
  | app : Te → Te → Te
  | apt : Te → Ty → Te

def measureTe t :=
  match t with
  | Te.int _   => 1
  | Te.str _   => 1
  | Te.abs t b => 1 + measureTy t + measureTe b
  | Te.all b   => 1 + measureTe b
  | Te.var _   => 1
  | Te.app f a => 1 + measureTe f + measureTe a
  | Te.apt t y => 1 + measureTe t + measureTy y

instance : ToString Te where
  toString t :=
    let rec ts := λ t =>
      match t with
      | Te.int n   => s!"Nat({n})"
      | Te.str s   => s!"String({s})"
      | Te.abs t b => s!"(λ {toString t}. {ts b}"
      | Te.all b   => s!"(∀. {ts b})"
      | Te.var v   => s!"Var({v})"
      | Te.app f a => s!"({ts f} {ts a})"
      | Te.apt t y => s!"[{ts t} {toString y}]"
    ts t

#eval (Te.all (Te.abs Ty.int (Te.str "hello world")))

def check (ctx : List Ty) (term : Te) : Except String Ty :=
  match term with
  | Te.int _   => pure Ty.int
  | Te.str _   => pure Ty.str
  | Te.abs t b => do
    let t ← match t with
            | Ty.var v => match ctx.get? v with
                          | some t => pure t
                          | none => Except.error s!"Trying to access not defined variable: {term}"
            | other    => pure other
    let b ←  check (ctx.cons t) b
    pure $ Ty.abs t b
  | Te.all b   => do
    let t ← check ctx b
    pure $ Ty.all t
  | Te.var v   =>
    match ctx.get? v with
    | some v => pure v
    | none   => Except.error s!"Trying to access not defined variable: {term}"
  | Te.app f a => do
    let a ← check ctx a
    let f' ← check ctx f
    match f' with
    | Ty.abs t b =>
      if t = a
      then pure b
      else Except.error s!"Expected to apply {t} but received {a}"
    | Ty.var v => do
      match ctx.get? v with
      | some (Ty.abs t r) =>
        if t = a
        then pure r
        else Except.error s!"Expected to apply {t} but received {a}"
      | some t => Except.error s!"Trying to apply value {a} on a term of type {t}"
      | none   => Except.error s!"Trying to access not defined variable: {term}"
    | _        => Except.error s!"Trying to apply value {a} on a term of type {f}"
  | Te.apt f a => do
    let f' ← check (ctx.cons a) f
    match f' with
    | Ty.all b => pure b
    | Ty.var v => do
      match ctx.get? v with
      | some (Ty.all r) => pure r
      | some t => Except.error s!"Trying to apply type {a} on a term of type {t}"
      | none   => Except.error s!"Trying to access not defined variable: {term}"
    | _        => Except.error s!"Trying to apply value {a} on a term of type {f}"

#eval check List.nil (Te.app (Te.abs Ty.str (Te.int 2)) (Te.str "hello world"))
#eval check List.nil (Te.all (Te.abs (Ty.var 0) (Te.int 1)))
#eval check List.nil (Te.apt (Te.all (Te.abs (Ty.var 0) (Te.int 1))) Ty.int)
#eval check List.nil (Te.app (Te.apt (Te.all (Te.abs (Ty.var 0) (Te.var 2))) Ty.int) (Te.int 3))

-- runtime values
inductive Expr where
  | clsr : Expr → Expr
  | int  : Int → Expr
  | str  : String → Expr
  | all  : Expr → Expr

instance : ToString Expr where
  toString e :=
    let rec ts := λ e =>
      match e with
      | Expr.int n  => s!"Int({n})"
      | Expr.str s  => s!"String({s})"
      | Expr.clsr b => s!"(λ. {ts b})"
      | Expr.all b  => s!"(∀. {ts b})"
    ts e

def evaluate (ctx : List Te) (term : Te) : Except String Te :=
  match term with
  | Te.int _   => pure term
  | Te.str _   => pure term
  | Te.abs _ b => sorry
  | Te.all b   => evaluate ctx b
  | Te.var v   => sorry
  | Te.app f a => sorry
  | Te.apt t a => sorry

end Llean.sf
