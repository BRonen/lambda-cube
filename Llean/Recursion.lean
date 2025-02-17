
inductive L (t : Type) where
  | n : L t
  | c : t → L t → L t
deriving Repr

open L

def a : L Nat := c 5 (c 4 n)
#check a
#eval a

def inc x := x + 1

def traverseL (f : Nat → Nat) (l : L Nat) : L Nat :=
  match l with
   | c v d => c (f v) (traverseL f d)
   | n => n

#eval traverseL inc a

inductive B (t : Type) where
  | leaf : B t
  | node : t → (left : B t) → (right : B t) → B t
deriving Repr

open B

def b : B Nat := node 3 (node 2 leaf leaf) (node 1 leaf leaf) 
#eval b

def traverseB (f : Nat → Nat) (b : B Nat) : B Nat :=
  match b with
   | leaf => leaf
   | node v l r => node (f v) (traverseB f l) (traverseB f r)

#check traverseB inc b
#eval traverseB inc b

def search (check : Nat → Bool) (base : Nat) :=
  if check base
  then base
  else search check (base + 1)
  decreasing_by sorry 

#eval search (fun n => n == 100) 0

