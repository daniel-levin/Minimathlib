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

theorem compl_inter {X : Type u} (s t : Set X) : (s ∩ t)ᶜ = sᶜ ∪ tᶜ := by
  funext x
  simp only [compl, inter, union]
  apply propext
  constructor
  · intro h
    by_cases h1 : s x
    · right
      intro ht
      exact h ⟨h1, ht⟩
    · left
      exact h1
  · intro h
    intro ⟨hs, ht⟩
    cases h with
    | inl h => exact h hs
    | inr h => exact h ht

end Set
