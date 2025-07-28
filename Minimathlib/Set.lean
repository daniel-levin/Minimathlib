universe u v
variable {α : Type u}

-- Sets as characteristic functions (predicates)
-- A set is represented as a function from elements to propositions
-- For any element x : X, the set s contains x iff (s x) is true
-- This is equivalent to the mathematical notion of a characteristic function
-- χ_S(x) = True if x ∈ S, False otherwise
--
-- Examples:
-- • evens : (set of even natural numbers)
-- • primes : Set ℕ := fun n => Nat.Prime n  (set of prime numbers)
-- • interval : Set ℝ := fun x => 0 ≤ x ∧ x ≤ 1  (unit interval [0,1])
--
-- Benefits of this representation:
-- 1. Natural: membership is just function application (s x)
--    Example: (evens 4) evaluates to True, (evens 3) evaluates to False
-- 2. Extensional: two sets are equal iff they have the same members
--    Example: fun n => n < 5 = fun n => n ∈ {0,1,2,3,4} by funext
-- 3. Higher-order: can quantify over sets, define families of sets
--    Example: ∀ s : Set ℕ, s ⊆ univ (all sets are subsets of the universal set)
-- 4. Uniform: all set operations reduce to logical operations on predicates
--    Example: (s ∩ t) x = s x ∧ t x, (s ∪ t) x = s x ∨ t x
-- 5. Type-safe: impossible to have membership between incompatible types
--    Example: can't ask if "hello" ∈ (Set ℕ), prevented at compile time
def Set (X : Type u) : Type u := X → Prop

theorem extensional {β : α → Sort v} {f g : (x : α) → β x}
  (h :  ∀ (x : α), f x = g x) : f = g := by
    funext x
    exact h x

theorem extensional2 {β : α → Sort v} {f g : (x : α) → β x}
  (h: f = g): ∀ (x : α), f x = g x := by
  exact fun x => congrFun h x

theorem extensionality {β : α → Sort v} {f g : (x : α) → β x} :
    f = g ↔ ∀ (x : α), f x = g x :=
    ⟨extensional2, extensional⟩

namespace Set

def evens : Set Nat := fun n => n % 2 = 0

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
def iUnion {X : Type u} {ι : Type u} (s : ι → Set X) : Set X := fun x => ∃ i, s i x

protected def Mem (s : Set α) (a : α) : Prop :=
  s a

instance : Membership α (Set α) :=
  ⟨Set.Mem⟩

notation "∅" => Set.empty
notation "𝒰" => Set.univ
infixl:70 " ∩ " => Set.inter
infixl:65 " ∪ " => Set.union
postfix:max "ᶜ" => Set.compl
notation "⋃ " f => Set.iUnion f

theorem hmmm (a : α): a ∈ Set.univ := by trivial

theorem one_is_in_set_nat : 1 ∈ 𝒰 := by trivial

theorem compl_empty {X : Type u} : (∅ : Set X)ᶜ = 𝒰 := by
  funext x
  simp [compl, empty, univ]

theorem compl_univ {X : Type u} : (𝒰 : Set X)ᶜ = ∅ := by
  funext x
  simp [compl, empty, univ]

-- De Morgan's law: complement of intersection equals union of complements
theorem compl_inter {X : Type u} (s t : Set X) : (s ∩ t)ᶜ = sᶜ ∪ tᶜ := by
  -- Two sets are equal if they contain the same elements
  -- funext proves equality of functions by proving pointwise equality
  funext x

  -- Unfold definitions: compl, inter, union
  -- This transforms the goal to: ¬(s x ∧ t x) = (¬s x ∨ ¬t x)
  simp only [compl, inter, union]

  -- Convert propositional equality to logical equivalence (iff)
  -- We need this because = on Prop means iff, but we need to prove it
  apply propext

  -- Split the iff into two directions: → and ←
  constructor

  -- First direction: ¬(s x ∧ t x) → (¬s x ∨ ¬t x)
  -- If x is not in both sets, then x is not in at least one set
  · intro h  -- h : ¬(s x ∧ t x)
    -- Case analysis on whether x ∈ s
    by_cases h1 : s x

    -- Case 1: x ∈ s, so if x were also in t, we'd have s x ∧ t x, contradicting h
    · right  -- We'll prove ¬t x
      intro ht  -- Assume t x
      -- But then we have s x ∧ t x (since h1 : s x and ht : t x)
      exact h ⟨h1, ht⟩  -- This contradicts h : ¬(s x ∧ t x)

    -- Case 2: x ∉ s, so we can immediately conclude ¬s x ∨ ¬t x
    · left   -- We'll prove ¬s x
      exact h1  -- h1 : ¬s x is exactly what we need

  -- Second direction: (¬s x ∨ ¬t x) → ¬(s x ∧ t x)
  -- If x is not in at least one set, then x is not in both sets
  · intro h  -- h : ¬s x ∨ ¬t x
    -- To prove ¬(s x ∧ t x), assume s x ∧ t x and derive contradiction
    intro ⟨hs, ht⟩  -- Assume both s x and t x

    -- Case analysis on which disjunct of h holds
    cases h with
    | inl h => exact h hs  -- If h : ¬s x, then h contradicts hs : s x
    | inr h => exact h ht  -- If h : ¬t x, then h contradicts ht : t x

end Set
