import Mathlib.Geometry.Convex.ConvexSpace.AffineSpace
import Mathlib.Geometry.Convex.ConvexSpace.Module

variable {R V A : Type*}

open Convexity Affine

section Ring

variable [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [AddCommGroup V] [Module R V] [AddTorsor V A]
attribute [local instance] AddTorsor.toConvexSpace

-- TODO we need this because IsModuleConvexSpace.ofModule uses the wrong convex space
-- hopefully this problem will go away at some point...
attribute [local instance] AddTorsor.toConvexSpace in
lemma IsModuleConvexSpace.ofAddTorsor : IsModuleConvexSpace R V where
  sConvexComb_eq_sum c := by
    simp only [AddTorsor.sConvexComb_eq_affineCombination, Finset.affineCombination,
      Finset.weightedVSubOfPoint_apply, id_eq, vsub_eq_sub, vadd_eq_add, AffineMap.coe_mk,
      Finsupp.sum, smul_sub, Finset.sum_sub_distrib]
    have := c.total
    rw [Finsupp.sum] at this
    rw [← Finset.sum_smul, this, one_smul]
    abel
