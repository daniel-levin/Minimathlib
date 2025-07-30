universe u v
variable {α : Type u}

-- See also: Halmos's Naive Set Theory.

-- This definition is lifted almost verbatim from Mathlib.
-- Despite being the foundation of a _mathematics_ library, Lean has no notion of sets.
-- Instead, we will develop a satisfactory naive set theory in the language of Lean.
-- In this case, a set is just defined as its characteristic function over the underlying type and with a Prop as an output, rather than 0 or 1.
-- This corresponds to the "axiom of specification".
def Set (X : Type u) : Type u := X → Prop

namespace Set

-- The empty set: no element satisfies the predicate
-- Example: ∅ : Set ℕ means fun n => False (no natural number is in ∅)
def empty {X : Type u} : Set X := fun _ => False

-- The universal set: every element satisfies the predicate
-- Example: 𝒰 : Set ℕ means fun n => True (every natural number is in 𝒰)
def univ {X : Type u} : Set X := fun _ => True

-- Intersection: element is in both sets
-- Example: if evens := fun n => n % 2 = 0 and odds := fun n => n % 2 = 1
-- then (evens ∩ odds) x = evens x ∧ odds x = False (no number is both even and odd)
def inter {X : Type u} (s t : Set X) : Set X := fun x => s x ∧ t x

-- Union: element is in at least one set
-- Example: (evens ∪ odds) x = evens x ∨ odds x = True (every number is even or odd)
def union {X : Type u} (s t : Set X) : Set X := fun x => s x ∨ t x

-- Complement: element is not in the original set
-- Example: if pos := fun n => n > 0, then posᶜ x = ¬(pos x) = ¬(x > 0) = x ≤ 0
def compl {X : Type u} (s : Set X) : Set X := fun x => ¬s x

-- Indexed union: element is in at least one set from the family
-- Example: if intervals i := fun x => i ≤ x ∧ x ≤ i+1, then
-- (⋃ intervals) x = ∃ i, intervals i x = ∃ i, i ≤ x ∧ x ≤ i+1 (covers all reals)
def iUnion {X : Type u} {ι : Type u} (s : ι → Set X) : Set X := fun x => ∃ i : ι, s i x

-- Indexed intersection: element is in all sets from the family
-- Example: if halflines i := fun x => x ≥ i, then
-- (⋂ halflines) x = ∀ i, halflines i x = ∀ i, x ≥ i (only satisfied by no real number)
def iInter {X : Type u} {ι : Type u} (s : ι → Set X) : Set X := fun x => ∀ i : ι, s i x

protected def Mem (s : Set α) (a : α) : Prop := s a

instance : Membership α (Set α) := ⟨Set.Mem⟩

notation "∅" => Set.empty
notation "𝒰" => Set.univ
infixl:70 " ∩ " => Set.inter
infixl:65 " ∪ " => Set.union
postfix:max "ᶜ" => Set.compl
notation "⋃ " f => Set.iUnion f
notation "⋂ " f => Set.iInter f
notation "⋃[" i "] " f => Set.iUnion (fun i => f)
notation "⋂[" i "] " f => Set.iInter (fun i => f)

#check Set.iUnion

-- Basic subset relation
def subset (s t : Set X) : Prop := ∀ x, x ∈ s → x ∈ t

infixl:50 " ⊆ " => subset

macro "ode_to_grind" : tactic =>
    `(tactic| (
      try unfold Set.compl
      try unfold Set.inter
      try unfold Set.union
      try unfold Set.empty
      try unfold Set.univ
      grind))

example : 1 ∈ 𝒰 := by trivial

-- Functions in Lean are intensional, which means we need to prove that Set satisfies the axiom of extensionality.
-- https://lean-lang.org/doc/reference/latest//The-Type-System/Functions/#function-extensionality
theorem ext {a b : Set α} (h : ∀ (x : α), x ∈ a ↔ x ∈ b) : a = b := by
  have q := λ x => propext (h x)
  have r := funext q
  assumption

theorem compl_empty {X : Type u} : (∅ : Set X)ᶜ = 𝒰 := by ode_to_grind

theorem compl_univ {X : Type u} : (𝒰 : Set X)ᶜ = ∅ := by ode_to_grind

theorem compl_inter {X : Type u} (s t : Set X) : (s ∩ t)ᶜ = sᶜ ∪ tᶜ := by ode_to_grind

theorem compl_union {X : Type u} (s t : Set X) : (s ∪ t)ᶜ = sᶜ ∩ tᶜ := by ode_to_grind

-- De Morgan's laws for indexed unions and intersections
theorem compl_iUnion {X : Type u} {ι : Type u} (s : ι → Set X) : (⋃ s)ᶜ = ⋂[i] (s i)ᶜ := by
  apply ext
  intro x
  constructor
  · intro h i hi
    -- h : ¬∃ i, s i x, hi : s i x, goal: False
    exact h ⟨i, hi⟩
  · intro h ⟨i, hi⟩
    -- h : ∀ i, ¬s i x, hi : s i x, goal: False
    exact h i hi

theorem compl_iInter {X : Type u} {ι : Type u} (s : ι → Set X) : (⋂ s)ᶜ = ⋃[i] (s i)ᶜ := by
  apply ext
  intro x
  constructor
  · intro h
    -- h : ¬∀ i, s i x, goal: ∃ i, ¬s i x
    -- Use classical logic via excluded middle
    classical
    have em : (∃ i, ¬s i x) ∨ ¬(∃ i, ¬s i x) := Classical.em (∃ i, ¬s i x)
    cases em with
    | inl hex => exact hex
    | inr hnex =>
      -- hnex : ¬∃ i, ¬s i x, which means ∀ i, s i x
      exfalso
      apply h
      intro i
      -- Need to show s i x from ¬∃ i, ¬s i x
      have : ¬¬s i x := fun hi => hnex ⟨i, hi⟩
      exact Classical.not_not.mp this
  · intro ⟨i, hi⟩ h
    -- hi : ¬s i x, h : ∀ i, s i x, goal: False
    exact hi (h i)


end Set
