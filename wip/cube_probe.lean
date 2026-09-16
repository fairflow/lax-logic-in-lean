import Mathlib.Order.Cover
import Mathlib.Data.Finset.Lattice.Fold

-- name probe: the interval-collapse lemma and the Finset distribution law
example {α : Type*} [PartialOrder α] {a b c : α} (h : a ⋖ b) (h1 : a ≤ c) (h2 : c ≤ b) :
    c = a ∨ c = b := h.eq_or_eq h1 h2

example {α : Type*} [DistribLattice α] [OrderBot α] (s : Finset α) (f : α → α) (a : α) :
    a ⊓ s.sup f = s.sup fun i => a ⊓ f i := by
  exact Finset.sup_inf_distrib_left s f a
