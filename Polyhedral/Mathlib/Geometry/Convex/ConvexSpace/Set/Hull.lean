/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Geometry.Convex.Hull
public import Mathlib.Geometry.Convex.ConvexSpace.Prod
public import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Pointwise

import Mathlib.Geometry.Convex.ConvexSpace.Module
import Mathlib.Order.Closure
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.AffineSpace
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Prod

/-!
# IsConvexSet hull

This file defines the convex hull of a set in a convex space. `convexHull R s` is the smallest
convex set containing `s`. In order theory speak, this is a closure operator.
-/

public section

public section

open Set

namespace Convexity

variable {R X Y : Type*} [Semiring R] [PartialOrder R] [IsStrictOrderedRing R] [ConvexSpace R X]
  [ConvexSpace R Y] {C s t : Set X} {x y : X}

/-- The convex hull of a product is the product of the convex hulls. -/
lemma convexHull_prod (s : Set X) (t : Set Y) :
    convexHull R (s ×ˢ t) = convexHull R s ×ˢ convexHull R t := by
  refine Subset.antisymm (convexHull_min
    (prod_mono subset_convexHull_self subset_convexHull_self)
    (.prod .convexHull .convexHull)) ?_
  rintro ⟨x, y⟩ ⟨hx, hy⟩
  have step : ∀ y ∈ t, (x, y) ∈ convexHull R (s ×ˢ t) := by
    intro y hy
    have hcvx : IsConvexSet R ((fun x => (x, y)) ⁻¹' convexHull R (s ×ˢ t)) :=
      .preimage (by fun_prop) .convexHull
    exact hcvx.convexHull_subset_iff.mpr
      (fun x hx => subset_convexHull_self (mk_mem_prod hx hy)) hx
  have hcvx : IsConvexSet R ((fun y => (x, y)) ⁻¹' convexHull R (s ×ˢ t)) :=
      .preimage (by fun_prop) .convexHull
  exact hcvx.convexHull_subset_iff.mpr step hy

section Pointwise

open Pointwise

variable {R V A : Type*}

variable [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [AddCommGroup V] [Module R V] [ConvexSpace R V] [IsModuleConvexSpace R V]

@[simp] lemma convexHull_neg (s : Set V) : -convexHull R s = convexHull R (-s) := by
  ext x
  simp only [mem_neg, mem_convexHull_iff]
  constructor <;> intro h t hst hcvx
  · exact neg_mem_neg.mp <| h (-t) (neg_subset.mp hst) hcvx.neg
  · exact mem_neg.mp <| h (-t) (neg_subset_neg.mpr hst) hcvx.neg

variable [AddTorsor V A] [ConvexSpace R A] [IsAffineConvexSpace R V A]

/-- The convex hull of a Minkowski sum is the Minkowski sum of the convex hulls, since
translation is an affine map on the product convex space (`isAffineMap_vadd`). -/
lemma convexHull_vadd (s₁ : Set V) (s₂ : Set A) :
    convexHull R (s₁ +ᵥ s₂) = convexHull R s₁ +ᵥ convexHull R s₂ := by
  rw [← Set.vadd_image_prod, ← Set.vadd_image_prod, ← convexHull_prod]
  exact (isAffineMap_vadd.image_convexHull _).symm

end Pointwise

end Convexity

end
