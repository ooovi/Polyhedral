/-
Copyright (c) 2019 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter, Olivia Röhrig
-/

import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
import Mathlib.Geometry.Convex.ConvexSpace.AffineSpace
import Mathlib.Algebra.Group.Pointwise.Finset.Scalar

import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Hull
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.Basic

/-! This file defines the pointwise operations on convex polytopes. -/

noncomputable section

namespace Convexity

namespace IsPolytope

variable {R X Y V A : Type*}

open ConvexSpace

section Pointwise

open Pointwise

section Semiring

variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [AddCommGroup V] [Module R V] [ConvexSpace R V] [IsModuleConvexSpace R V]

variable {P P₁ P₂ : Set V}

protected lemma neg (hP : IsPolytope R P) : IsPolytope R (-P) := by classical
  obtain ⟨s, rfl⟩ := hP
  -- use -s -- TODO: `Neg (Finset V)` seems to be not implemented
  -- rw [convexHull_neg]
  sorry

end Semiring

section Ring

variable [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [AddCommGroup V] [Module R V] [ConvexSpace R V] [IsModuleConvexSpace R V]
variable [AddTorsor V A]

local instance : ConvexSpace R A := AddTorsor.toConvexSpace
-- TODO: add class expressing compatibility between the convex structures on A and V

/- The Minkowski sum of two polytopes is a polytope. -/
protected lemma vadd {P₁ : Set V} {P₂ : Set A} (hP₁ : IsPolytope R P₁) (hP₂ : IsPolytope R P₂) :
    IsPolytope R (P₁ +ᵥ P₂) := by classical
  obtain ⟨s₁, rfl⟩ := hP₁
  obtain ⟨s₂, rfl⟩ := hP₂
  use s₁ +ᵥ s₂
  rw [Finset.coe_vadd, convexHull_vadd]

/- Minkowski addition preserves convexity. -/
lemma translate (t : V) {K : Set A} (hK : IsPolytope R K) : IsPolytope R (t +ᵥ K) := by
  sorry

/- The Minkowski addition of two polytopes is a polytope. -/
protected lemma add {P₁ : Set V} {P₂ : Set V}
    (hP₁ : IsPolytope R P₁) (hP₂ : IsPolytope R P₂) : IsPolytope R (P₁ + P₂) :=
  -- TODO: use `IsPolytope.vadd hP₁ hP₂`
  -- this likely requires a compatbility class between affine and linear convexity
  sorry

/- The Minkowski addition of two polytopes is a polytope. -/
protected lemma sub {P₁ : Set V} {P₂ : Set V}
    (hP₁ : IsPolytope R P₁) (hP₂ : IsPolytope R P₂) : IsPolytope R (P₁ - P₂) :=
  sorry

protected lemma smul (r : R) {K : Set V} (hK : IsPolytope R K) :
    IsPolytope R (r • K) := by
  sorry

end Ring

end Pointwise

end IsPolytope

end Convexity
