/-
Copyright (c) 2026 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/

import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.Geometry.Convex.ConvexSpace.Module
import Mathlib.Geometry.Convex.ConvexSpace.AffineSpace
import Mathlib.LinearAlgebra.AffineSpace.AffineMap

import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Basic
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.AffineMap

/-! This file proves basic pointwise properties of convex sets. -/

noncomputable section

variable {ι R K X Y V A W B : Type*}

namespace Convexity

section Pointwise

open Pointwise

section Semiring

variable [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [AddCommGroup V] [Module R V] [ConvexSpace R V] [IsModuleConvexSpace R V]

variable {K K₁ K₂ : Set V}

protected lemma IsConvexSet.neg (hK : IsConvexSet R K) : IsConvexSet R (-K) := by
  rw [← Set.image_neg_eq_neg]
  exact hK.image (LinearEquiv.neg R).toLinearMap.isAffineMap

@[simp] lemma IsConvexSet.neg_iff : IsConvexSet R (-K) ↔ IsConvexSet R K where
  mp := by nth_rw 2 [← neg_neg K]; exact .neg
  mpr := .neg

end Semiring

section Ring

variable [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [AddCommGroup V] [Module R V] [ConvexSpace R V] [IsModuleConvexSpace R V]
variable [AddTorsor V A]

local instance : ConvexSpace R A := AddTorsor.toConvexSpace
-- TODO: add class expressing compatibility between the convex structures on A and V

/- Minkowski addition preserves convexity. -/
protected lemma IsConvexSet.vadd {K₁ : Set V} {K₂ : Set A}
    (hK₁ : IsConvexSet R K₁) (hK₂ : IsConvexSet R K₂) : IsConvexSet R (K₁ +ᵥ K₂) := by
  -- TODO: use `AddTorsor.sConvexComb_eq_affineCombination`
  sorry

/- Minkowski addition preserves convexity. -/
lemma IsConvexSet.translate (t : V) {K : Set A} (hK : IsConvexSet R K) :
    IsConvexSet R (t +ᵥ K) := by
  -- TODO: use `IsConvexSet.vadd hK₁ hK₂` by setting `K₁ := {t}` and
  --  some missing vadd lemmas
  -- this likely requires a compatbility class between affine and linear convexity
  sorry

/- Minkowski addition preserves convexity. -/
protected lemma IsConvexSet.add {K₁ : Set V} {K₂ : Set V}
    (hK₁ : IsConvexSet R K₁) (hK₂ : IsConvexSet R K₂) : IsConvexSet R (K₁ + K₂) :=
  -- TODO: use `IsConvexSet.vadd hK₁ hK₂`
  -- this likely requires a compatbility class between affine and linear convexity
  sorry

/- Minkowski addition preserves convexity. -/
protected lemma IsConvexSet.sub {K₁ : Set V} {K₂ : Set V}
    (hK₁ : IsConvexSet R K₁) (hK₂ : IsConvexSet R K₂) : IsConvexSet R (K₁ - K₂) :=
  -- TODO: use `IsConvexSet.vadd` and `IsConvexSet.neg`
  sorry

protected lemma IsConvexSet.smul (r : R) {K : Set V} (hK : IsConvexSet R K) :
    IsConvexSet R (r • K) := by
  sorry

end Ring

end Pointwise

end Convexity
