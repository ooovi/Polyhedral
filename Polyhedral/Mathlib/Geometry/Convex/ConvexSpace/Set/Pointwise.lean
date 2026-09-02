/-
Copyright (c) 2026 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/
module

public import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.AffineMap

import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.Geometry.Convex.ConvexSpace.Module
import Mathlib.Geometry.Convex.ConvexSpace.AffineSpace
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Basic
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.AffineMap
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.AffineSpace

/-! This file proves basic pointwise properties of convex sets. -/

public section

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
variable [AddTorsor V A] [ConvexSpace R A] [IsAffineConvexSpace R V A]

/-- Minkowski addition preserves convexity, since translation is an affine map on the
product convex space (`isAffineMap_vadd`). -/
protected lemma IsConvexSet.vadd {K₁ : Set V} {K₂ : Set A}
    (hK₁ : IsConvexSet R K₁) (hK₂ : IsConvexSet R K₂) : IsConvexSet R (K₁ +ᵥ K₂) := by
  rw [← Set.vadd_image_prod]
  exact (hK₁.prod hK₂).image isAffineMap_vadd

/-- Translation preserves convexity. -/
lemma IsConvexSet.translate (t : V) {K : Set A} (hK : IsConvexSet R K) :
    IsConvexSet R (t +ᵥ K) := by
  rw [← Set.singleton_vadd]
  exact .vadd .singleton hK

/- TODO: there should also be a version `(K : ConvexSet R V) +ᵥ (p : A)`, but there is not even
a version for sets yet. -/

/-- Minkowski addition preserves convexity. -/
protected lemma IsConvexSet.add {K₁ : Set V} {K₂ : Set V}
    (hK₁ : IsConvexSet R K₁) (hK₂ : IsConvexSet R K₂) : IsConvexSet R (K₁ + K₂) := hK₁.vadd hK₂

/-- Pointwise subtraction of two convex sets of an affine space is convex, since point
subtraction is an affine map on the product convex space (`isAffineMap_vsub`). -/
protected lemma IsConvexSet.vsub {K₁ K₂ : Set A}
    (hK₁ : IsConvexSet R K₁) (hK₂ : IsConvexSet R K₂) : IsConvexSet R (K₁ -ᵥ K₂) := by
  rw [← Set.image_vsub_prod]
  exact (hK₁.prod hK₂).image isAffineMap_vsub

/-- Minkowski difference preserves convexity. -/
protected lemma IsConvexSet.sub {K₁ : Set V} {K₂ : Set V}
    (hK₁ : IsConvexSet R K₁) (hK₂ : IsConvexSet R K₂) : IsConvexSet R (K₁ - K₂) := by
  rw [sub_eq_add_neg]
  exact hK₁.add hK₂.neg

/-- Scalar multiplication is an affine map. -/
lemma isAffineMap_smul [SMulCommClass R R V] (r : R) :
    IsAffineMap R fun x : V => r • x := by
  refine ⟨fun w => ?_⟩
  rw [sConvexComb_eq_sum, sConvexComb_eq_sum, StdSimplex.weights_map,
    Finsupp.sum_mapDomain_index (by simp) (fun _ b₁ b₂ => add_smul b₁ b₂ _), Finsupp.smul_sum]
  exact Finsupp.sum_congr fun i _ => smul_comm r _ _

/-- Scaling preserves convexity. -/
protected lemma IsConvexSet.smul [SMulCommClass R R V] (r : R) {K : Set V}
    (hK : IsConvexSet R K) : IsConvexSet R (r • K) := by
  rw [← Set.image_smul]
  exact hK.image (isAffineMap_smul r)

end Ring

end Pointwise

end Convexity
