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

class TopologicalSpace (X : Type u) where
  -- A collection of subsets of X called open sets
  isOpen : Set X → Prop
  -- The empty set and X are open
  isOpen_empty : isOpen ∅
  isOpen_univ : isOpen 𝒰
  -- Any union of open sets is open
  isOpen_union : ∀ {ι : Type u} (s : ι → Set X), (∀ i, isOpen (s i)) → isOpen (⋃ s)
  -- The intersection of finitely many open sets is open
  isOpen_inter : ∀ s t, isOpen s → isOpen t → isOpen (s ∩ t)

variable {X : Type u} [TopologicalSpace X]

def isClosed (s : Set X) : Prop := @TopologicalSpace.isOpen X _ (sᶜ)

theorem isClosed_empty : isClosed (∅ : Set X) := by
  unfold isClosed
  rw [@Set.compl_empty]
  exact TopologicalSpace.isOpen_univ

theorem isClosed_univ : isClosed (𝒰 : Set X) := by
  unfold isClosed
  rw [@Set.compl_univ]
  exact TopologicalSpace.isOpen_empty
