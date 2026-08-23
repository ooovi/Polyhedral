/-
Copyright (c) 2026 Olivia Röhrig, Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter, Olivia Röhrig
-/

import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Finite.Face.Grade
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.Homogenization
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.Lattice
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Face.Homogenization
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Homogenization
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Module

/-! This file proves results about polytopes and faces. -/

variable {R V A : Type*}

open Convexity ConvexSet Affine

section Field

variable [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable [AddCommGroup V] [Module R V]
variable [AddTorsor V A]

attribute [local instance] AddTorsor.toConvexSpace

variable {C F : ConvexSet R A}

/-- Faces of polytopes are polytopes. -/
theorem IsPolytope.face_isPolytope (hC : IsPolytope R (C : Set A)) (hF : IsFaceOf F C) :
    IsPolytope R (F : Set A) := by
  let W := CanonicalHomogenization R A
  let := IsModuleConvexSpace.ofAddTorsor (R := R) (V := W)
  have homC := IsPolytope.homogenize_FG (W := W) hC
  have homF := IsHomogenization.homogenize_isFaceOf (W := W) hF
  have := PointedCone.IsFaceOf.fg homC homF
  convert FG.dehomogenize_isPolytope this (fun _ a b ↦ weight_pos_of_mem_homogenize a b)
  simp [dehomogenize_homogenize]

instance {P : Polytope R A} : CoeOut (Face (P : ConvexSet R A)) (Polytope R A) where
  coe F := ⟨_, IsPolytope.face_isPolytope P.isPolytope F.isFaceOf⟩

/- NOTE: We suppress a linter warning only relevant for classes accessible by instance
search. This one is not accessible, since the hypothesis of being a polytope is not. -/
set_option warn.classDefReducibility false
/-- The face lattice of a polytope as a graded order with grading given by the dimensions of
homogenization cones.

This is private since it does not yet have the correct grading (off-by-one).
-/
private noncomputable def Polytope.faceHomogenizationGradeOrder (P : Polytope R A) :
    GradeOrder ℕ (Face (P : ConvexSet R A)) := by
  let W := CanonicalHomogenization R A
  let := IsModuleConvexSpace.ofAddTorsor (R := R) (V := W)
  have : PointedCone.FG (homogenize W (P : ConvexSet R A)) :=
    IsPolytope.homogenize_FG (W := W) P.isPolytope
  let := PointedCone.FG.gradeOrder_finrank this
  refine GradeOrder.liftRight (β := (homogenize W (P : ConvexSet R A)).Face) _
    IsHomogenization.Face.homogenizeIso.strictMono ?_
  exact fun x y ↦ (apply_covBy_apply_iff _).mpr

end Field
