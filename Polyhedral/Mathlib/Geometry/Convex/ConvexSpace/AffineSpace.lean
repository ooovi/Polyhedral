import Mathlib.Geometry.Convex.ConvexSpace.AffineSpace
import Mathlib.Geometry.Convex.Set
import Polyhedral.Mathlib.LinearAlgebra.AffineSpace.AffineMap

open Affine Convexity

variable {R V V2 P P2 I : Type*}
variable [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [AddCommGroup V] [Module R V] [AddTorsor V P]
variable [AddCommGroup V2] [Module R V2] [AffineSpace V2 P2]

attribute [local instance] AddTorsor.toConvexSpace

open Convexity

namespace AffineMap

-- PR #39437
open Finset AddTorsor in
lemma isAffineMap (f : P →ᵃ[R] P2) : IsAffineMap R f where
  map_sConvexComb s:= by
    classical
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

lemma range_isConvexSet (f : P →ᵃ[R] P2) : IsConvexSet R (f.range : Set P2) := by
  simpa [range, SetLike.coe, ← Set.image_univ] using IsConvexSet.univ.image (f.isAffineMap)

end AffineMap
