/-
Copyright (c) 2026 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter, Olivia Röhrig
-/
module

public import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.Basic

import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
import Mathlib.Geometry.Convex.ConvexSpace.AffineSpace
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Algebra.Group.Pointwise.Finset.Scalar
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.AffineSpace
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Hull

/-! This file defines the pointwise operations on convex polytopes. -/

public section

noncomputable section

namespace Convexity

namespace IsPolytope

variable {R X Y V A : Type*}

open ConvexSpace

section Pointwise

open Pointwise

section AddCommMonoid

variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [AddCommMonoid V] [Module R V] [ConvexSpace R V] [IsModuleConvexSpace R V]

/-- The Minkowski sum of two polytopes is a polytope. -/
protected lemma add {P₁ : Set V} {P₂ : Set V}
    (hP₁ : IsPolytope R P₁) (hP₂ : IsPolytope R P₂) : IsPolytope R (P₁ + P₂) := by
  rw [← Set.add_image_prod]
  exact (hP₁.prod hP₂).image isAffineMap_add

/-- Scaling preserves polytopes. -/
protected lemma smul [SMulCommClass R R V] (r : R) {K : Set V} (hK : IsPolytope R K) :
    IsPolytope R (r • K) := by
  rw [← Set.image_smul]
  exact hK.image (isAffineMap_smul r)

end AddCommMonoid

section AddCommGroup

variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [AddCommGroup V] [Module R V] [ConvexSpace R V] [IsModuleConvexSpace R V]

protected lemma neg {P : Set V} (hP : IsPolytope R P) : IsPolytope R (-P) := by classical
  obtain ⟨s, rfl⟩ := hP
  use -s
  simp only [convexHull_neg, Finset.coe_neg]

/-- The Minkowski difference of two polytopes is a polytope. -/
protected lemma sub {P₁ : Set V} {P₂ : Set V}
    (hP₁ : IsPolytope R P₁) (hP₂ : IsPolytope R P₂) : IsPolytope R (P₁ - P₂) := by
  rw [sub_eq_add_neg]
  exact hP₁.add hP₂.neg

end AddCommGroup

section Ring

variable [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [AddCommGroup V] [Module R V] [ConvexSpace R V] [IsModuleConvexSpace R V]
variable [AddTorsor V A] [ConvexSpace R A] [IsAffineConvexSpace R V A]

/-- The Minkowski sum of two polytopes is a polytope, since translation is an affine map
on the product convex space (`isAffineMap_vadd`). -/
protected lemma vadd {P₁ : Set V} {P₂ : Set A} (hP₁ : IsPolytope R P₁) (hP₂ : IsPolytope R P₂) :
    IsPolytope R (P₁ +ᵥ P₂) := by
  rw [← Set.vadd_image_prod]
  exact (hP₁.prod hP₂).image isAffineMap_vadd

/-- Translation preserves polytopes. -/
lemma translate (t : V) {K : Set A} (hK : IsPolytope R K) : IsPolytope R (t +ᵥ K) := by
  exact hK.image (by fun_prop)

end Ring

end Pointwise

end IsPolytope

end Convexity
