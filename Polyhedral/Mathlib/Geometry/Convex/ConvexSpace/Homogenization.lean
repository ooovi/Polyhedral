import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Convexity
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.AffineMap
import Polyhedral.Mathlib.LinearAlgebra.AffineSpace.Homogenization.Basic

open Convexity Pointwise Set PointedCone Submodule

namespace Convexity

section Ring

variable {R : Type*} [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
variable {V : Type*} [AddCommGroup V] [Module R V]
variable {A : Type*} [AddTorsor V A]
variable {W : Type*} [AddCommGroup W] [Module R W]
variable [hom : Affine.IsHomogenization R A W]

attribute [local instance] AddTorsor.toConvexSpace

section Module

variable [IsModuleConvexSpace R W]

/-- If the homogenization of a point lies in the conic hull of a subset `s` of the homogenization
plane, the point can be written as a convex combination of points in the preimage of `s` under the
homogenization embedding. -/
theorem exists_sConvexComb_preimage_of_mem_hull {x} {s : Set W} (hs : s ⊆ Set.range hom.ofPoint)
    (hx : hom.ofPoint x ∈ hull R s) : ∃ c' : StdSimplex R A,
      sConvexComb c' = x ∧ (c'.weights.support : Set A) ⊆ (hom.ofPoint ⁻¹' s) := by
  obtain ⟨c, ha, hb, hc⟩ := mem_hull_set.mp hx
  -- use the same weights, just un-embed the domain
  use StdSimplex.mk (c.comapDomain hom.ofPoint hom.ofPoint_injective.injOn) ?_ ?_
  constructor
  · -- the convex combo yields x
    apply hom.ofPoint_injective
    rw [hom.ofPoint.isAffineMap.map_sConvexComb, sConvexComb_eq_sum,
      StdSimplex.weights_map, ← hc, Finsupp.mapDomain_comapDomain _ hom.ofPoint_injective]
    exact ha.trans hs
  · -- the weights are a subset of the preimage of s
    simpa using (Set.preimage_mono ha)
  · -- they're always nonneg
    intro y
    simpa using hb (hom.ofPoint y)
  · -- its actually a convex combo, i.e. weights sum to 1
    have hsum : c.sum (fun a b => b * hom.weight a) = c.sum (fun a b => b) := by
        refine Finsupp.sum_congr (fun a h => ?_)
        obtain ⟨_, _, rfl⟩ := (ha.trans hs) h
        simp [hom.weight_one]
    -- apply weights map to both sides
    have := congrArg hom.weight hc
    simp only [map_finsuppSum, map_smul, smul_eq_mul, hsum, hom.weight_one] at this
    rw [← this]
    simp only [Finsupp.sum, Finsupp.comapDomain_support, Finsupp.comapDomain_apply]
    rw [Finset.sum_preimage hom.ofPoint _ (hom.ofPoint_injective.injOn)]
    exact fun _ hx hnx ↦ Finsupp.notMem_support_iff.mp fun _ ↦ hnx (hs (ha hx))

/-- The preimage of the conic hull of a set in the homogenization plane is the convex hull of the
preimage of the set. -/
theorem preimage_hull_eq_convexHull_preimage {s : Set W} (hs : s ⊆ Set.range hom.ofPoint) :
    hom.ofPoint ⁻¹' hull R s = Convexity.convexHull R (hom.ofPoint ⁻¹' s) := by
  refine subset_antisymm ?_ ?_
  · intro x hx
    obtain ⟨c', rfl, hs⟩ := exists_sConvexComb_preimage_of_mem_hull hs hx
    exact IsConvexSet.convexHull.sConvexComb_mem (le_trans hs subset_convexHull_self)
  · apply Set.image_subset_iff.mp
    rw [hom.ofPoint.isAffineMap.image_convexHull, Set.image_preimage_eq_iff.mpr hs]
    exact (hull R s).isConvexSet.convexHull_subset_iff.mpr subset_hull

/-- The homogenization embedding of the convex hull of a set is contained in the hull of the
embedding of the set. -/
theorem preimage_hull_eq_convexHull_preimagke {s : Set A} :
    hom.ofPoint '' Convexity.convexHull R s ⊆ hull R (hom.ofPoint '' s) := by
  apply Set.image_subset_iff.mp
  rw [hom.ofPoint.isAffineMap.image_convexHull]
  simpa using (hull R _).isConvexSet.convexHull_subset_iff.mpr subset_hull

end Module

end Ring

end Convexity
