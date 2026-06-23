import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Finite.Face.Grade
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.Basic
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Homogenization
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Face.Basic
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Module
import Mathlib.Data.Finset.SDiff

/-! This file proves results about polytopes, FG cones and homogenization. -/

variable {R V W A : Type*}

open Convexity ConvexSet Affine IsHomogenization

section Ring

variable [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [AddCommGroup V] [Module R V] [AddTorsor V A]

attribute [local instance] AddTorsor.toConvexSpace
variable [AddCommGroup W] [Module R W] [IsModuleConvexSpace R W] [hom : IsHomogenization R A W]

open PointedCone

/-- The Homogenization cone of a polytope is finitely generated. -/
theorem IsPolytope.of_homogenize_FG {C : ConvexSet R A} (hCfg : IsPolytope R (C : Set A)) :
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

/-- A convex set is a polytope iff its homogenization cone is finitely generated. -/
theorem IsPolytope.iff_homogenize_FG {C : ConvexSet R A} :
    IsPolytope R (C : Set A) ↔ (homogenize W C).FG := by
  refine ⟨fun P ↦ IsPolytope.of_homogenize_FG P, fun hfg ↦ ?_⟩
  -- get cone generators that lie in the embedding of A
  obtain ⟨g, hg, hs⟩ := homogenize_FG_ofPoint_range hfg
  classical
  -- un-embed them
  use g.preimage hom.ofPoint hom.ofPoint_injective.injOn
  -- show they generate C
  simp only [Finset.coe_preimage]
  apply le_antisymm
  · intro x hx
    apply mem_convexHull_preimage_of_apply_mem_hull hs
    simp only [hg, homogenize]
    exact Submodule.mem_span_of_mem <| Set.mem_image_of_mem hom.ofPoint hx
  · apply C.isConvexSet.convexHull_subset_iff.mpr
    rw [← C.isConvexSet.convexHull_eq_self]
    intro x hx
    simp only [Set.mem_preimage, SetLike.mem_coe] at hx
    have := Submodule.mem_span_of_mem (R := {c : R // 0 ≤ c}) hx
    simp_rw [hg] at this
    have := mem_convexHull_preimage_of_apply_mem_hull (Set.image_subset_range _ _) this
    simpa [Set.preimage_image_eq _ hom.ofPoint_injective]

end Ring

section Field

variable [LinearOrder R] [Field R] [IsStrictOrderedRing R]
variable [AddCommGroup V] [Module R V] [AddTorsor V A]
attribute [local instance] AddTorsor.toConvexSpace
variable [AddCommGroup W] [Module R W] [IsModuleConvexSpace R W] [hom : IsHomogenization R A W]

open Pointwise Submodule in
/-- Dehomogenizing a finitely generated positive cone yields a polytope. -/
theorem FG.dehomogenize_isPolytope {C : PointedCone R W} (h : C.FG)
    (hc : ∀ c ∈ C, c ≠ 0 → 0 < hom.weight c) :
    IsPolytope R (dehomogenize A C : Set A) := by
  apply (IsPolytope.iff_homogenize_FG (hom := hom)).mpr
  simpa [homogenize_dehomogenize_of_le_positive hc]

end Field
