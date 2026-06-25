import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Finite.Face.Grade
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.Homogenization
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Face.Homogenization
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Homogenization
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Module

variable {R V W A : Type*}

open Convexity ConvexSet Affine

section Field

variable [LinearOrder R] [Field R] [IsStrictOrderedRing R]
variable [AddCommGroup V] [Module R V] [AddTorsor V A]
attribute [local instance] AddTorsor.toConvexSpace
variable {C : ConvexSet R A}

/-- Faces of polytopes are polytopes. -/
theorem face_isPolytope (hCfg : IsPolytope R (C : Set A)) (F : C.Face) :
    IsPolytope R (F : Set A) := by
  letI hom : IsHomogenization R A (CanonicalHomogenization R A) := inferInstance
  letI := IsModuleConvexSpace.ofAddTorsor (R := R) (V := (CanonicalHomogenization R A))
  have homC := IsPolytope.of_homogenize_FG (W := (CanonicalHomogenization R A)) hCfg
  have homF := hom.homogenize_isFaceOf F.isFaceOf
  have := PointedCone.IsFaceOf.fg homC homF
  convert FG.dehomogenize_isPolytope this (fun _ a b ↦ weight_pos_of_mem_homogenize a b)
  simp [dehomogenize_homogenize]

/-- The face lattice of a polytope as a graded order with grading given by the dimensions of
homogenization cones. -/
@[reducible]
private noncomputable def Polytope.faceHomogenizationGradeOrder
    (hCfg : IsPolytope R (C : Set A)) : GradeOrder ℕ C.Face := by
  letI hom : IsHomogenization R A (CanonicalHomogenization R A) := inferInstance
  letI := IsModuleConvexSpace.ofAddTorsor (R := R) (V := (CanonicalHomogenization R A))
  have : PointedCone.FG (C.homogenize (CanonicalHomogenization R A)) :=
    IsPolytope.of_homogenize_FG hCfg
  letI := PointedCone.FG.gradeOrder_finrank this
  -- we just lift the grading we have for PointedCone.Face already
  refine GradeOrder.liftRight (β := (homogenize  (CanonicalHomogenization R A) C).Face) _
    IsHomogenization.Face.homogenizeIso.strictMono ?_
  exact fun x y ↦ (apply_covBy_apply_iff _).mpr

end Field
