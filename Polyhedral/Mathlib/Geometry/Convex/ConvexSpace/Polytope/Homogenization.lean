import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Finite.Face.Grade
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.Basic
import Polyhedral.Mathlib.LinearAlgebra.AffineSpace.Homogenization


variable {R V W A : Type*}

open Convexity Affine

section Ring

variable [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [AddCommGroup V] [Module R V] [AddTorsor V A]
variable [AddCommGroup W] [Module R W] [hom : Homogenization R A W] [IsModuleConvexSpace R W]
variable {C : ConvexSet R A}

open PointedCone

/-- The homogenization cone of a polytope is finitely generated. -/
theorem IsPolytope.homogenize_FG (hCfg : IsPolytope R (C : Set A)) :
    (Homogenization.homogenize W C).FG := by
  obtain ⟨t, ht⟩ := hCfg
  have : C = ⟨convexHull R t, IsConvexSet.convexHull⟩ := SetLike.ext' ht
  rw [congrArg hom.homogenize this]
  use t.map ⟨_, hom.inj⟩
  simp only [Finset.coe_map, Function.Embedding.coeFn_mk, Homogenization.homogenize,
    PointedCone.hull, ConvexSet.mk_eq]
  rw [hom.isAffineMap.image_convexHull t]
  exact (PointedCone.hull_convexHull_eq_hull (hom.embed '' t)).symm

end Ring

section Field

variable [LinearOrder R] [Field R] [IsStrictOrderedRing R]
variable [AddCommGroup V] [Module R V] [AddTorsor V A]
variable [AddCommGroup W] [Module R W] [hom : Homogenization R A W] [IsModuleConvexSpace R W]
variable {C : ConvexSet R A}

variable (W) in
/-- The face lattice of a polytope is graded by homogenization cone face dimension. -/
@[reducible]
private noncomputable def Polytope.faceHomogenizationGradeOrder
    (hCfg : IsPolytope R (C : Set A)) : GradeOrder ℕ C.Face := by
  have : PointedCone.FG (hom.homogenize W C) := IsPolytope.homogenize_FG hCfg
  letI := PointedCone.FG.gradeOrder_finrank this
  -- we just lift the grading we have for PointedCone.Face already
  refine GradeOrder.liftRight (β := (hom.homogenize W C).Face) _
    Homogenization.Face.homogenizationIso.strictMono ?_
  exact fun x y ↦ (apply_covBy_apply_iff _).mpr

end Field
