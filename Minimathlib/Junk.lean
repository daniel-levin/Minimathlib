universe u v

def something := Type u

def something_else := Sort u

/-- The partial keyword turns off Lean's termination checking --/
partial def collatz (n : Nat) : Nat :=
    if n = 1 then 1
    else if n % 2 = 0 then collatz (n / 2)
    else collatz (3 * n + 1)

class P (α : Type u) where
  a : α

structure S where
  number : Nat
  number_is_zero : ∀ n : Nat, number <= n

def must_be_zero: S := S.mk 0 Nat.zero_le

-- def must_be_zero_bad: S := S.mk 1 Nat.zero_le

#check must_be_zero

instance (s : S): P Nat where
  a := s.number

class Q {β : Type u} where
  a : β

-- the @ symbol turns off automatic implicit argument inference
instance : @Q Nat where
  a := 1
