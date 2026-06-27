-- Reference: Advanced Modern Algebra - Rotman

class Group (G: Type _) extends Mul G, Inv G where
  -- Following Rotman's convention we denote the identity as e
  e: G
  mul_assoc: ∀ a b c : G, (a * b) * c = a * (b * c)
  mul_one: ∀ a : G, a * e = a
  one_mul: ∀ a : G, e * a = a
  mul_inv: ∀ a : G, a * a⁻¹ = e

open Group

variable {G: Type _} [Group G]

class Abelian (G: Type _) extends Group G where
  mul_comm: ∀ a b : G, a * b = b * a

def gpow (a : G) : Nat → G
  | 0     => e
  | n + 1 => gpow a n * a

instance : NatPow G := ⟨gpow⟩

theorem npow_zero (a : G) : a ^ 0 = e := rfl
theorem npow_succ (a : G) (n : Nat) : a ^ (n + 1) = a ^ n * a := rfl

-- check that power notation works
example (a : G) (n : Nat): a^n = a^n := by rfl

-- check that we inherit sane properties
example (a : G) (n m : Nat): a^(n+m) = a^n * a^m := by
  induction m with
  | zero => rw [Nat.add_zero, npow_zero, mul_one]
  | succ k ih => rw [← Nat.add_assoc, npow_succ, npow_succ, ih, mul_assoc]

def lmul (a : G) {b c : G} (h : b = c) : a*b = a*c := by
  rw [h]

def rmul {b c : G} (h : b = c) (a : G)  : b*a = c*a := by
  rw [h]

variable (a b c d : G)

theorem inv_inv : (a⁻¹)⁻¹ = a := by
  have h := lmul a (mul_inv a⁻¹)
  rwa [mul_one, ← mul_assoc, mul_inv, one_mul] at h

theorem inv_mul : a⁻¹ * a = e := by
  have l := mul_inv a⁻¹
  rwa [inv_inv] at l

attribute [simp] Group.mul_assoc Group.mul_one Group.one_mul Group.mul_inv
attribute [simp] inv_inv inv_mul

@[simp] theorem mul_inv_cancel_left : a * (a⁻¹ * b) = b := by
  rw [← mul_assoc, mul_inv, one_mul]

@[simp] theorem inv_mul_cancel_left : a⁻¹ * (a * b) = b := by
  rw [← mul_assoc, inv_mul, one_mul]

section rotman_lemma_2_16

theorem right_cancellation_law (h: a * c = b * c): a = b := by
  simpa using rmul h c⁻¹

theorem left_cancellation_law (h: c * a = c * b): a = b := by
  simpa using lmul c⁻¹ h

-- The element e is the unique element in G with e ∗ x = x = x ∗ e for all x ∈ G.
theorem identity_unique (h : ∀ x : G, d * x = x ∧ x * d = x) : d = e := by
    have : d * e = e := (h e).1
    rw [mul_one] at this
    exact this

example (h: ∀ x : G, d * x = x ∧ x * d = x) : d = e := by
  have k := (h e).1
  rw [mul_one] at k
  exact k

example (h1 : ∀ x : G, d * x = x): d = e := by
  have k := (h1 e)
  rw [mul_one] at k
  exact k

example (h1 : ∀ x : G, d * x = x): d = e := by
  have k := (h1 e)
  rw [mul_one] at k
  assumption

end rotman_lemma_2_16

/-- Rotman: exercise 2.21 --/
theorem no_nonidentity_self_square (h: a*a = a): a = e := by
  simpa using rmul h a⁻¹

theorem mul_inv_rev : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  apply left_cancellation_law _ _ (a * b)
  simp

-- Term-mode proof of the same theorem
theorem mul_inv_rev_term : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
  left_cancellation_law _ _ (a * b)
    (calc (a * b) * (a * b)⁻¹
      = e                     := mul_inv (a * b)
    _ = (a * b) * (b⁻¹ * a⁻¹) := Eq.symm (calc (a * b) * (b⁻¹ * a⁻¹)
        = a * (b * (b⁻¹ * a⁻¹))     := mul_assoc a b (b⁻¹ * a⁻¹)
      _ = a * (b * b⁻¹ * a⁻¹)       := lmul a (Eq.symm (mul_assoc b b⁻¹ a⁻¹))
      _ = a * (e * a⁻¹)             := lmul a (rmul (mul_inv b) a⁻¹)
      _ = a * a⁻¹                   := lmul a (one_mul a⁻¹)
      _ = e                         := mul_inv a))

-- Another term-mode proof of the same theorem
example: (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
  left_cancellation_law _ _ (a * b) (Eq.trans (mul_inv (a * b)) (Eq.symm
    (Eq.trans (mul_assoc a b (b⁻¹ * a⁻¹))
    (Eq.trans (lmul a (Eq.symm (mul_assoc b b⁻¹ a⁻¹)))
    (Eq.trans (lmul a (rmul (mul_inv b) a⁻¹))
    (Eq.trans (lmul a (one_mul a⁻¹)) (mul_inv a)))))))

class Hom (G: Type _) (H: Type _) [Group G] [Group H] where
  map: G → H
  homs: ∀ a b : G, map (a*b) = map a * map b

def is_abelian (G: Type _) [Group G]: Prop := ∀ a b : G, a * b = b * a

/-- Rotman Exercise 2.26 --/
example (G1 : Type _) [Group G1] (h: ∀ a : G1, a * a = e): is_abelian G1 := by
  unfold is_abelian
  have self_inverse: (p : G1) → p = p⁻¹ := by
    intro p
    simpa using rmul (h p) p⁻¹
  intro a b
  rw [self_inverse (a*b), mul_inv_rev, self_inverse a⁻¹, self_inverse b⁻¹, inv_inv, inv_inv]
