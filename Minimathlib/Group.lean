universe u v

-- Reference: Advanced Modern Algebra - Rotman

class Group (G: Type u) extends Mul G, Inv G where
  -- Following Rotman's convention we denote the identity as e
  e: G
  mul_assoc: ∀ a b c : G, (a * b) * c = a * (b * c)
  mul_one: ∀ a : G, a * e = a
  one_mul: ∀ a : G, e * a = a
  mul_inv: ∀ a : G, a * a⁻¹ = e

open Group

variable {G: Type u} [Group G]

class Abelian (G: Type u) extends Group G where
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

theorem inv_inv (a : G): (a⁻¹)⁻¹ = a := by
  have h := lmul a (mul_inv a⁻¹)
  rwa [mul_one, ← mul_assoc, mul_inv, one_mul] at h

theorem inv_mul (a : G): a⁻¹ * a = e := by
  have l := mul_inv a⁻¹
  rwa [inv_inv] at l

section rotman_lemma_2_16

theorem right_cancellation_law (a b x: G) (h: a * x = b * x): a = b := by
  have p := rmul h x⁻¹
  rwa [mul_assoc, mul_assoc, mul_inv, mul_one, mul_one] at p

theorem left_cancellation_law (a b x: G) (h: x * a = x * b): a = b := by
  have p := lmul x⁻¹ h
  rwa [← mul_assoc, ← mul_assoc, inv_mul, one_mul, one_mul] at p

-- The element e is the unique element in G with e ∗ x = x = x ∗ e for all x ∈ G.
theorem identity_unique (d : G) (h : ∀ x : G, d * x = x ∧ x * d = x) : d = e := by
    have : d * e = e := (h e).1
    rw [mul_one] at this
    exact this

theorem identity_unique2 (d : G) (h: ∀ x : G, d * x = x ∧ x * d = x) : d = e := by
  have k := (h e).1
  rw [mul_one] at k
  exact k

theorem identity_unique3 (d : G) (h1 : ∀ x : G, d * x = x): d = e := by
  have k := (h1 e)
  rw [mul_one] at k
  exact k

theorem identity_unique4 (d : G) (h1 : ∀ x : G, d * x = x): d = e := by
  have k := (h1 e)
  rw [mul_one] at k
  assumption

end rotman_lemma_2_16

/-- Rotman: exercise 2.21 --/
theorem no_nonidentity_self_square (a : G) (h: a*a = a): a = e := by
  have l := rmul h a⁻¹
  rwa [mul_assoc, mul_inv, mul_one] at l

theorem no_nonidentity_self_square2 (a : G): a * a = a → a = e := by
  intro h
  exact no_nonidentity_self_square a h

theorem mul_inv_rev (a b : G): (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  apply left_cancellation_law _ _ (a * b)
  rw [mul_inv, ← mul_assoc, mul_assoc a, mul_inv, mul_one, mul_inv]

-- Term-mode proof of the same theorem
theorem mul_inv_rev_term (a b : G): (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
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
theorem mul_inv_rev_term2 (a b : G): (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
  left_cancellation_law _ _ (a * b) (Eq.trans (mul_inv (a * b)) (Eq.symm
    (Eq.trans (mul_assoc a b (b⁻¹ * a⁻¹))
    (Eq.trans (lmul a (Eq.symm (mul_assoc b b⁻¹ a⁻¹)))
    (Eq.trans (lmul a (rmul (mul_inv b) a⁻¹))
    (Eq.trans (lmul a (one_mul a⁻¹)) (mul_inv a)))))))

class Hom (G: Type u) (H: Type v) [Group G] [Group H] where
  map: G → H
  homs: ∀ a b : G, map (a*b) = map a * map b

def is_abelian (G: Type u) [Group G]: Prop := ∀ a b : G, a * b = b * a

/-- Rotman Exercise 2.26 --/
example (G1 : Type u) [Group G1] (h: ∀ a : G1, a * a = e): is_abelian G1 := by
  unfold is_abelian
  have self_inverse: (p : G1) → p = p⁻¹ := by
    intro p
    have r := rmul (h p) p⁻¹
    rw [mul_assoc, mul_inv, mul_one, one_mul] at r
    assumption
  intro a b
  rw [self_inverse (a*b), mul_inv_rev, self_inverse a⁻¹, self_inverse b⁻¹, inv_inv, inv_inv]
