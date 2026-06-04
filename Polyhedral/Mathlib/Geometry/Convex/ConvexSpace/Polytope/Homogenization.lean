import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Finite.Face.Grade
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.Basic
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Face
import Polyhedral.Mathlib.LinearAlgebra.AffineSpace.Homogenization.ConvexSet

variable {R V W A : Type*}

open Convexity Affine

section Ring

variable [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [AddCommGroup V] [Module R V] [AddTorsor V A]
variable {C : ConvexSet R A}

open PointedCone

variable [AddCommGroup W] [Module R W] [hom : Homogenization R A W] in
/-- The Homogenization cone of a polytope is finitely generated. -/
theorem IsPolytope.homogenize_FG (hCfg : IsPolytope R (C : Set A)) :
    (Homogenization.homogenize W C).FG := by
  obtain ⟨t, ht⟩ := hCfg
  have : C = ⟨convexHull R t, IsConvexSet.convexHull⟩ := SetLike.ext' ht
  rw [congrArg hom.homogenize this]
  use t.map ⟨_, hom.ofPoint_injective⟩
  simp only [Finset.coe_map, Function.Embedding.coeFn_mk, Homogenization.homogenize,
    PointedCone.hull, ConvexSet.mk_eq]
  rw [hom.ofPoint.isAffineMap.image_convexHull t]
  exact (PointedCone.hull_convexHull_eq_hull (hom.ofPoint '' t)).symm

end Ring

section Field

variable [LinearOrder R] [Field R] [IsStrictOrderedRing R]
variable [AddCommGroup V] [Module R V] [AddTorsor V A]
variable {C : ConvexSet R A}

variable [AddCommGroup W] [Module R W] [hom : Homogenization R A W] in
open Pointwise Submodule in
/-- Dehomogenizing a finitely generated salient cone yields a polytope. -/
theorem FG.dehomogenize_isPolytope {C : PointedCone R W} (h : C.FG)
    (hc : ∀ c ∈ C, c ≠ 0 → 0 < hom.weight c) :
    IsPolytope R (hom.dehomogenize A C : Set A) := by sorry

/-- Faces of polytopes are polytopes. -/
theorem face_isPolytope (hCfg : IsPolytope R (C : Set A)) (F : C.Face) : IsPolytope R (F : Set A) :=
    by
  letI hom : Homogenization R A (CanonicalHomogenization R A) := inferInstance
  have homC := IsPolytope.homogenize_FG (W := (CanonicalHomogenization R A)) hCfg
  have homF := hom.homogenize_isFaceOf F.isFaceOf
  have := PointedCone.IsFaceOf.fg homC homF
  convert FG.dehomogenize_isPolytope this (fun _ a b ↦ hom.weight_pos_of_mem_homogenize a b)
  simp [hom.dehomogenize_homogenize_eq_id]

variable [AddCommGroup W] [Module R W] [hom : Homogenization R A W]

variable (W) in
/-- The face lattice of a polytope is graded by Homogenization cone face dimension. -/
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
