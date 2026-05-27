/-
Copyright (c) 2019 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter, Olivia Röhrig
-/

import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Lattice
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.Basic

/-! ... -/

namespace Convexity

open ConvexSpace

variable {R X Y V : Type*}

section Semiring

variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [ConvexSpace R X]

variable (R X) in
structure Polytope where
  carrier : Set X
  isPolytope : IsPolytope R carrier

end Semiring

namespace Polytope

section Semiring

variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [ConvexSpace R X]

instance : SetLike (Polytope R X) X where
  coe := Polytope.carrier
  coe_injective' P₁ P₂ _ := by cases P₁; cases P₂; congr

variable {P P₁ P₂ : Polytope R X}

variable (K) in
@[simp] lemma carrier_eq_coe : P.carrier = P := rfl

@[ext] theorem ext (h : ∀ x, x ∈ P₁ ↔ x ∈ P₂) : P₁ = P₂ := SetLike.ext h

@[simp] theorem mem_mk {s h x} : x ∈ (⟨s, h⟩ : Polytope R X) ↔ x ∈ s := .rfl

@[simp] theorem mk_eq {s h} : (⟨s, h⟩ : Polytope R X) = s := by ext; simp

instance : PartialOrder (Polytope R X) := .ofSetLike ..

instance : Coe (Polytope R X) (ConvexSet R X) where
  coe P := ⟨P, P.isPolytope.isConvexSet⟩

instance : OrderBot (Polytope R X) where
  bot := ⟨∅, IsPolytope.empty R X⟩
  bot_le _ _ hx := by simp at hx

instance : Inhabited (Polytope R X) := ⟨⊥⟩
variable (R) in
/-- The convex hull of a `Finset s` as a `Polytope`. -/
def convexHull (s : Finset X) : Polytope R X :=
  ⟨_, IsPolytope.convexHull_finite R s.finite_toSet⟩

instance : Max (Polytope R X) where
  max P₁ P₂ := ⟨_, P₁.isPolytope.convexHull_union P₂.isPolytope⟩

lemma coe_sup_eq_convexHull_union :
  ((P₁ ⊔ P₂ : Polytope R X) : Set X) = Convexity.convexHull R (P₁ ∪ P₂) := rfl

instance : SemilatticeSup (Polytope R X) where
  sup := max
  le_sup_left _ _ := by
    rw [← SetLike.coe_subset_coe, coe_sup_eq_convexHull_union]
    exact subset_trans Set.subset_union_left subset_convexHull_self
  le_sup_right _ _ := by
    rw [← SetLike.coe_subset_coe, coe_sup_eq_convexHull_union]
    exact subset_trans Set.subset_union_right subset_convexHull_self
  sup_le a b c ha hb := by
    rw [← SetLike.coe_subset_coe, coe_sup_eq_convexHull_union]
    have : IsConvexSet R (c : Set X) := c.isPolytope.isConvexSet
    rw [← convexHull_eq_self.mpr this]
    apply convexHull_mono
    simp_all only [SetLike.coe_subset_coe, Set.union_subset_iff, and_self]

end Semiring

section Field

variable [Field R] [PartialOrder R] [IsStrictOrderedRing R]
variable [ConvexSpace R X]
variable [AddCommGroup V] [Module R V]
variable [AddTorsor V X]

attribute [local instance] AddTorsor.toConvexSpace

/-- The infimum of two convex sets is a convex set. -/
instance : Min (Polytope R X) where
  min P₁ P₂ := ⟨_, P₁.isPolytope.inter P₂.isPolytope⟩

variable {P P₁ P₂ : Polytope R X}

instance : Lattice (Polytope R X) where
  inf := min
  inf_le_left _ _ _ hx := hx.1
  inf_le_right _ _ _ hx := hx.2
  le_inf _ _ _ h₁₂ h₂₃ _ hx := ⟨h₁₂ hx, h₂₃ hx⟩

end Field

end Polytope

end Convexity
