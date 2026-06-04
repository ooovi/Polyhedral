module

public import Mathlib.Geometry.Convex.ConvexSpace.Module
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.AffineSpace

namespace Convexity

section Ring

open Function Submodule

variable {R : Type*} [Ring R]
variable {W : Type*} [AddCommGroup W] [Module R W]

variable [PartialOrder R] [IsStrictOrderedRing R] in
instance : IsModuleConvexSpace R W where
  sConvexComb_eq_sum c := by
    simp only [AddTorsor.sConvexComb_eq_affineCombination, Finset.affineCombination,
      Finset.weightedVSubOfPoint_apply, id_eq, vsub_eq_sub, vadd_eq_add, AffineMap.coe_mk,
      Finsupp.sum, smul_sub, Finset.sum_sub_distrib]
    have := c.total
    rw [Finsupp.sum] at this
    rw [← Finset.sum_smul, this, one_smul]
    abel

end Convexity.Ring
