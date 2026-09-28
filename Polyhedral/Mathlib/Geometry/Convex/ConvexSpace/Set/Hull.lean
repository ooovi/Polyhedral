module

public import Polyhedral.Mathlib.Geometry.Convex.AffineMap.Module
public import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.AffineSpace
public import Polyhedral.Mathlib.Geometry.Convex.Hull

public section

open Set
open scoped Pointwise

namespace Convexity
variable {R V A : Type*}

variable [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [AddCommGroup V] [Module R V]
variable [AddTorsor V A] [ConvexSpace R A] [IsAffineConvexSpace R V A]

@[simp]
theorem affineSpan_convexHull (s : Set A) :
    affineSpan R (convexHull R s : Set A) = affineSpan R s := by
  refine le_antisymm ?_ (affineSpan_mono R subset_convexHull_self)
  grw [affineSpan_mono, affineSpan_le_of_subset_coe le_rfl]
  exact convexHull_min (subset_affineSpan R s) (AffineSubspace.isConvexSet _)

@[simp]
theorem vectorSpan_convexHull (s : Set A) :
    vectorSpan R (convexHull R s : Set A) = vectorSpan R s := by
  rw [← direction_affineSpan, affineSpan_convexHull, direction_affineSpan]

variable [ConvexSpace R V] [IsModuleConvexSpace R V]

@[simp]
theorem span_convexHull (s : Set V) :
    Submodule.span R (convexHull R s : Set V) = Submodule.span R s := by
  ext x
  grind [Submodule.mem_span, mem_convexHull_iff, isConvexSet_coe]

@[simp] lemma convexHull_neg (s : Set V) : -convexHull R s = convexHull R (-s) := by
  ext x
  simp only [mem_neg, mem_convexHull_iff]
  constructor <;> intro h t hst hcvx
  · exact neg_mem_neg.mp <| h (-t) (neg_subset.mp hst) hcvx.neg
  · exact mem_neg.mp <| h (-t) (neg_subset_neg.mpr hst) hcvx.neg

/-- The convex hull of a Minkowski sum is the Minkowski sum of the convex hulls, since
translation is an affine map on the product convex space (`isAffineMap_vadd`). -/
lemma convexHull_vadd (s₁ : Set V) (s₂ : Set A) :
    convexHull R (s₁ +ᵥ s₂) = convexHull R s₁ +ᵥ convexHull R s₂ := by
  rw [← Set.vadd_image_prod, ← Set.vadd_image_prod, ← convexHull_prod]
  exact (isAffineMap_vadd.image_convexHull _).symm

end Convexity
