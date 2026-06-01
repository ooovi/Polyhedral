import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Finite.Face.Grade
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.Basic
import Polyhedral.Mathlib.LinearAlgebra.AffineSpace.Homogenization


variable {R V W A : Type*}

open Convexity Affine

section Ring

variable [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [AddCommGroup V] [Module R V] [AddTorsor V A]
variable [IsModuleConvexSpace R (Homogenization R A)]
variable {C : ConvexSet R A}

open PointedCone Homogenization

/-- The homogenization cone of a polytope is finitely generated. -/
theorem IsPolytope.homogenize_FG (hCfg : IsPolytope R (C : Set A)) :
    (homogenize C).FG := by
  obtain ⟨t, ht⟩ := hCfg
  have : C = ⟨convexHull R t, IsConvexSet.convexHull⟩ := SetLike.ext' ht
  rw [congrArg homogenize this]
  use t.map ⟨_, ofPoint_injective⟩
  simp only [Finset.coe_map, Function.Embedding.coeFn_mk, homogenize, hull, ConvexSet.mk_eq]
  rw [ofPoint.isAffineMap.image_convexHull (t : Set A)]
  exact (PointedCone.hull_convexHull_eq_hull (ofPoint '' (t : Set A))).symm

end Ring

section Field

open Homogenization

variable [LinearOrder R] [Field R] [IsStrictOrderedRing R]
variable [AddCommGroup V] [Module R V] [AddTorsor V A]
variable [IsModuleConvexSpace R (Homogenization R A)]
variable {C : ConvexSet R A}

variable (W) in
/-- The face lattice of a polytope is graded by homogenization cone face dimension. -/
@[reducible]
private noncomputable def Polytope.faceHomogenizationGradeOrder
    (hCfg : IsPolytope R (C : Set A)) : GradeOrder ℕ C.Face := by
  have : PointedCone.FG (homogenize C) := IsPolytope.homogenize_FG hCfg
  letI := PointedCone.FG.gradeOrder_finrank this
  -- we just lift the grading we have for PointedCone.Face already
  refine GradeOrder.liftRight (β := (homogenize C).Face) _
    Homogenization.Face.homogenizationIso.strictMono ?_
  exact fun x y ↦ (apply_covBy_apply_iff _).mpr

end Field
