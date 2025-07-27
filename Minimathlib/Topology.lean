import Minimathlib.Set

universe u

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
