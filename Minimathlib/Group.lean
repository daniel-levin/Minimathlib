universe u v

-- Reference: Advanced Modern Algebra - Rotman

class Group (G: Type u) extends Mul G, Inv G where
  -- Following Rotman's convention we denote the identity as e
  e: G
  mul_assoc: ∀ a b c : G, (a * b) * c = a * (b * c)
  mul_one: ∀ a : G, a * e = a
  one_mul: ∀ a : G, e * a = a
  mul_inv: ∀ a : G, a * a⁻¹ = e

class Abelian (G: Type u) extends Group G where
  mul_comm: ∀ a b : G, a * b = b * a

open Group
variable {G: Type u} [Group G]

theorem inv_inv (a : G): (a⁻¹)⁻¹ = a := by
  have term := congrArg (a*.) (mul_inv a⁻¹)
  simp at term
  rw [← @mul_assoc, @mul_inv, @mul_one, @one_mul] at term
  exact term

theorem inv_mul (a : G): a⁻¹ * a = e := by
  have l := mul_inv a⁻¹
  rw [inv_inv] at l
  assumption

section rotman_lemma_2_16

theorem right_cancellation_law (a b x: G) (h: a * x = b * x): a = b := by
  have p := congrArg (. * x⁻¹) h
  simp at p
  repeat rw [mul_assoc] at p
  rw [mul_inv, @mul_one, mul_one] at p
  assumption

theorem left_cancellation_law (a b x: G) (h: x * a = x * b): a = b := by
  have p := congrArg (x⁻¹ * .) h
  simp at p
  repeat rw [← mul_assoc] at p
  rw [inv_mul, one_mul, one_mul] at p
  assumption

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

theorem no_nonidentity_self_square (a : G) (h: a*a = a): a = e := by
  have l := congrArg (. * a⁻¹) h
  simp at l
  rw [mul_assoc, mul_inv, mul_one] at l
  assumption

theorem no_nonidentity_self_square2 (a : G): a * a = a → a = e := by
  intro h
  exact no_nonidentity_self_square a h

theorem mul_inv_rev (a b : G): (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  have x := congrArg (. * a⁻¹) (congrArg (. * b⁻¹) (inv_mul (a * b)))
  simp at x
  conv at x =>
    lhs
    congr
    repeat rw [mul_assoc]
    rw [mul_inv b, mul_one]
  rw [mul_assoc, mul_inv, mul_one, one_mul] at x
  assumption

class Hom (G: Type u) (H: Type v) [Group G] [Group H] where
  map: G → H
  homs: ∀ a b : G, map (a*b) = map a * map b
