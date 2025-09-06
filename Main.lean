def double (f : Nat -> Nat) n := f (f n)
def inc n := n + 1

def main : IO Unit :=
  IO.println s!"Hello, {double inc 100}"

#eval main
