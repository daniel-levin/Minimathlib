universe u

def Set (X : Type u) : Type u := X → Prop

namespace Set

def empty {X : Type u} : Set X := fun _ => False

def univ {X : Type u} : Set X := fun _ => True

def inter {X : Type u} (s t : Set X) : Set X := fun x => s x ∧ t x

def union {X : Type u} (s t : Set X) : Set X := fun x => s x ∨ t x

def compl {X : Type u} (s : Set X) : Set X := fun x => ¬s x

def iUnion {X : Type u} {ι : Type u} (s : ι → Set X) : Set X := fun x => ∃ i, s i x

notation "∅" => Set.empty
notation "𝒰" => Set.univ
infixl:70 " ∩ " => Set.inter
infixl:65 " ∪ " => Set.union
postfix:max "ᶜ" => Set.compl
notation "⋃ " f => Set.iUnion f

theorem compl_empty {X : Type u} : (∅ : Set X)ᶜ = 𝒰 := by
  funext x
  simp [compl, empty, univ]

theorem compl_univ {X : Type u} : (𝒰 : Set X)ᶜ = ∅ := by
  funext x
  simp [compl, empty, univ]

end Set
