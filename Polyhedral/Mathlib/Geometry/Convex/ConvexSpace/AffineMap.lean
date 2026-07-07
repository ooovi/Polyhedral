import Mathlib.Geometry.Convex.ConvexSpace.AffineSpace
import Mathlib.Geometry.Convex.Set

import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Basic
import Polyhedral.Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.AffineSpace

/-! This file proves results about affine maps and convexity. -/

open Affine Convexity

variable {R V V₁ V₂ P P₁ P₂ I : Type*}
variable [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [AddCommGroup V] [Module R V] [AddTorsor V P]
variable [AddCommGroup V₁] [Module R V₁] [AddTorsor V₁ P₁]
variable [AddCommGroup V₂] [Module R V₂] [AddTorsor V₂ P₂]

open Convexity

namespace AffineMap

attribute [local instance] AddTorsor.toConvexSpace

-- TODO: eventually replace local instance by:
-- variable [ConvexSpace R P] [IsAffineConvexSpace R V P]
-- variable [ConvexSpace R P₁] [IsAffineConvexSpace R V₁ P₁]
-- variable [ConvexSpace R P₂] [IsAffineConvexSpace R V₂ P₂]

variable (f : P₁ →ᵃ[R] P₂)

-- PR #39437
open Finset AddTorsor in
lemma isAffineMap : IsAffineMap R f where
  map_sConvexComb s:= by classical
    simp_rw [sConvexComb_eq_affineCombination, StdSimplex.weights_map, Finsupp.mapDomain,
      map_affineCombination _ _ _ s.total, Finsupp.sum, Finsupp.coe_finsetSum]
    simp only [affineCombination_apply, weightedVSubOfPoint_apply, map_sum]
    congr
    ext i
    rw [sum_eq_single (f i) fun _ _ hx ↦ by simp [hx.symm]]
    · simp
    · intro h
      simp only [Finsupp.mem_support_iff, Finsupp.coe_finsetSum, sum_apply,
        Decidable.not_not, Finsupp.single_apply] at h
      have hwi : s.weights i = 0 := by
        by_contra hi
        have := sum_eq_zero_iff_of_nonneg (fun _ _ ↦ ?_) |>.mp h i (Finsupp.mem_support_iff.mpr hi)
        · simp at this
          contradiction
        · split_ifs <;> simp
      simp [hwi]

@[simp] lemma map_sConvexComb (w : StdSimplex R P₁) :
    f (sConvexComb w) = sConvexComb (w.map f) := f.isAffineMap.map_sConvexComb w

lemma image_isConvexSet {s : Set P₁} (hs : IsConvexSet R s) : IsConvexSet R (f '' s) :=
  hs.image f.isAffineMap

lemma range_isConvexSet : IsConvexSet R (Set.range f) := by
  rw [← Set.image_univ]
  exact f.image_isConvexSet .univ

end AffineMap

namespace LinearMap

variable [ConvexSpace R V₁] [IsModuleConvexSpace R V₁]
variable [ConvexSpace R V₂] [IsModuleConvexSpace R V₂]

variable (f : V₁ →ₗ[R] V₂)

-- TODO: This must hold. But currently the obvious proof fails due to some instance diamonds
lemma isAffineMap (f : V₁ →ₗ[R] V₂) : IsAffineMap R f := sorry -- f.toAffineMap.isAffineMap

@[simp] lemma map_sConvexComb (w : StdSimplex R V₁) :
    f (sConvexComb w) = sConvexComb (w.map f) := f.isAffineMap.map_sConvexComb w

lemma image_isConvexSet {s : Set V₁} (hs : IsConvexSet R s) : IsConvexSet R (f '' s) :=
  hs.image f.isAffineMap

lemma range_isConvexSet : IsConvexSet R (Set.range f) := by
  rw [← Set.image_univ]
  exact f.image_isConvexSet .univ

end LinearMap
