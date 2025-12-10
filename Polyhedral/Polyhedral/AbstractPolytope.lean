
import Mathlib.Order.Grade
import Mathlib.Order.CompleteLattice.Defs
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

open SimpleGraph Preorder

def DiamondLattice : Set Nat := {0, 1}

def Preorder.flagFlipGraph (α : Type*) [Preorder α] : SimpleGraph (Flag α) := sorry

class AbstractPolytope (P : Type*) [PartialOrder P] [BoundedOrder P] [GradeBoundedOrder ℕ P] where
  diamond : ∀ a b : P, a ≤ b → grade ℤ a + 2 = grade ℤ b → Set.Icc a b ≃o DiamondLattice
  flagConnected : ∀ a b : P, a ≤ b → Connected (flagFlipGraph (Set.Icc a b))

variable {P : Type*} [PartialOrder P] [GradeOrder ℤ P] [AbstractPolytope P]

instance : AbstractPolytope Pᵒᵖ := sorry

instance {a b : P} : AbstractPolytope (Set.Icc a b) := sorry
