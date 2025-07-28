universe u
variable {α : Type u}

def Set (X : Type u) : Type u := X → Prop

namespace Set

def empty {X : Type u} : Set X := fun _ => False

def univ {X : Type u} : Set X := fun _ => True

def inter {X : Type u} (s t : Set X) : Set X := fun x => s x ∧ t x

def union {X : Type u} (s t : Set X) : Set X := fun x => s x ∨ t x

def compl {X : Type u} (s : Set X) : Set X := fun x => ¬s x

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
