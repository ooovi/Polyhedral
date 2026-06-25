import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Homogenization
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.Basic
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Homogenization

/-! This file proves results about the relation between polytopes and FG cones via
homogenization. -/

variable {R V W A : Type*}

open Convexity ConvexSet Affine IsHomogenization

section Ring

variable [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [AddCommGroup V] [Module R V] [AddTorsor V A]
variable [AddCommGroup W] [Module R W]
variable [hom : IsHomogenization R A W]

attribute [local instance] AddTorsor.toConvexSpace
variable [IsModuleConvexSpace R W]

open PointedCone

/-- The homogenization of a polytope is a finitely generated cone. -/
theorem IsPolytope.homogenize_FG {C : ConvexSet R A} (hCfg : IsPolytope R (C : Set A)) :
    (homogenize W C).FG := by
  obtain ⟨t, ht⟩ := hCfg
  have : C = ⟨convexHull R t, IsConvexSet.convexHull⟩ := SetLike.ext' ht
  have := congrArg (ConvexSet.homogenize W) this
  rw [this]
  use t.map ⟨_, hom.ofPoint_injective⟩
  simp only [Finset.coe_map, Function.Embedding.coeFn_mk, homogenize,
    PointedCone.hull, ConvexSet.mk_eq]
  rw [hom.ofPoint.isAffineMap.image_convexHull t]
  exact (PointedCone.hull_convexHull_eq_hull (hom.ofPoint '' t)).symm

/-- A convex set is a polytope iff its homogenization is a finitely generated cone. -/
theorem IsPolytope.iff_homogenize_FG {C : ConvexSet R A} :
    IsPolytope R (C : Set A) ↔ (homogenize W C).FG := by classical
  refine ⟨homogenize_FG, fun hfg ↦ ?_⟩
  -- get cone generators that lie in the embedding of A
  obtain ⟨g, hg, hs⟩ := homogenize_FG_ofPoint_range hfg
  -- un-embed them
  use g.preimage hom.ofPoint hom.ofPoint_injective.injOn
  -- show they generate C
  simp only [Finset.coe_preimage]
  apply le_antisymm
  · intro x hx
    rw [← preimage_hull_eq_convexHull_preimage hs]
    simp only [hg, homogenize]
    exact Submodule.mem_span_of_mem <| Set.mem_image_of_mem hom.ofPoint hx
  · apply C.isConvexSet.convexHull_subset_iff.mpr
    intro x hx
    simp only [Set.mem_preimage, SetLike.mem_coe] at hx
    have := Set.mem_preimage.mpr <| Submodule.mem_span_of_mem (R := {c : R // 0 ≤ c}) hx
    simp_rw [hg, homogenize] at this
    rw [preimage_hull_eq_convexHull_preimage (Set.image_subset_range hom.ofPoint C)] at this
    rw [← C.isConvexSet.convexHull_eq_self]
    simpa [← C.isConvexSet.convexHull_eq_self, Set.preimage_image_eq _ hom.ofPoint_injective]

end Ring

section Field

variable [LinearOrder R] [Field R] [IsStrictOrderedRing R]
variable [AddCommGroup V] [Module R V] [AddTorsor V A]
variable [AddCommGroup W] [Module R W]
variable [hom : IsHomogenization R A W]

attribute [local instance] AddTorsor.toConvexSpace
variable [IsModuleConvexSpace R W]

open Pointwise Submodule in
/-- Dehomogenizing a finitely generated positive cone yields a polytope. -/
theorem FG.dehomogenize_isPolytope {C : PointedCone R W} (h : C.FG)
    (hc : C ≤ hom.weight.positive) : IsPolytope R (dehomogenize A C : Set A) := by
  rw [IsPolytope.iff_homogenize_FG (W := W)]
  simpa [homogenize_dehomogenize_of_le_positive hc]

end Field
