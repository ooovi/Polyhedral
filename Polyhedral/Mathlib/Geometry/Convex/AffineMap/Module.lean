module

public import Mathlib.Geometry.Convex.AffineMap.Module
public import Polyhedral.Mathlib.Geometry.Convex.Set

public section

open Convexity
open scoped Pointwise

namespace Convexity
variable {R S M : Type*}

section Semiring
variable [Ring R] [PartialOrder R] [IsStrictOrderedRing R] [AddCommGroup M]
  [Module R M] [ConvexSpace R M] [IsModuleConvexSpace R M] {K K₁ K₂ : Set M}

protected lemma IsConvexSet.add (hK₁ : IsConvexSet R K₁) (hK₂ : IsConvexSet R K₂) :
    IsConvexSet R (K₁ + K₂) := by rw [← Set.image2_add]; exact hK₁.image2 (by fun_prop) hK₂

variable [DistribSMul S M] [SMulCommClass R S M]

lemma isAffineMap_smul (s : S) : IsAffineMap R fun x : M ↦ s • x :=
  IsAffineMap.linearMap (s • LinearMap.id : M →ₗ[R] M)

protected lemma IsConvexSet.smul (s : S) {K : Set M} (hK : IsConvexSet R K) :
    IsConvexSet R (s • K) := by rw [← Set.image_smul]; exact hK.image (isAffineMap_smul s)

end Semiring

section Ring
variable [Ring R] [PartialOrder R] [IsStrictOrderedRing R] [AddCommGroup M]
  [Module R M] [ConvexSpace R M] [IsModuleConvexSpace R M] {K K₁ K₂ : Set M}

protected lemma IsConvexSet.neg (hK : IsConvexSet R K) : IsConvexSet R (-K) := by
  rw [← Set.image_neg_eq_neg]
  exact hK.image (.linearMap (LinearEquiv.neg R).toLinearMap)

@[simp] lemma isConvexSet_neg : IsConvexSet R (-K) ↔ IsConvexSet R K where
  mp h := by simpa using h.neg
  mpr := .neg

protected lemma IsConvexSet.sub (hK₁ : IsConvexSet R K₁) (hK₂ : IsConvexSet R K₂) :
    IsConvexSet R (K₁ - K₂) := by rw [← Set.image2_sub]; exact hK₁.image2 (by fun_prop) hK₂

end Ring
end Convexity
