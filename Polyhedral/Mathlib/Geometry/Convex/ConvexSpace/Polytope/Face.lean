/-
Copyright (c) 2026 Olivia Röhrig, Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter, Olivia Röhrig
-/
module

public import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.Lattice
public import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Face.Homogenization

import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Finite.Face.Grade
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.Homogenization

/-! This file proves results about faces of polytopes by transporting results from FG
cones along a homogenization. -/

public section

variable {R V A : Type*}

open Convexity ConvexSet Affine

section Field

variable [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable [AddCommGroup V] [Module R V]
variable [AddTorsor V A] [ConvexSpace R A] [IsAffineConvexSpace R V A]

variable {C F : ConvexSet R A}

include V in
/-- Faces of polytopes are polytopes. -/
theorem IsPolytope.face_isPolytope (hC : IsPolytope R (C : Set A)) (hF : IsFaceOf F C) :
    IsPolytope R (F : Set A) := by
  let : ConvexSpace R (Homogenization R A) := ConvexSpace.ofModule
  have homF := (IsHomogenization.canonical R A).homogenize_isFaceOf hF
  have := PointedCone.IsFaceOf.fg (IsPolytope.homogenize_fg _ hC) homF
  convert FG.dehomogenize_isPolytope this (fun _ a b ↦ weight_pos_of_mem_homogenize a b)
  simp [dehomogenize_homogenize]

include V in
instance {P : Polytope R A} : CoeOut (Face (P : ConvexSet R A)) (Polytope R A) where
  coe F := ⟨_, IsPolytope.face_isPolytope P.isPolytope F.isFaceOf⟩

include V in
/-- The face lattice of a polytope as a graded order with grading given by the dimensions of
homogenization cones.

This is private since it does not yet have the correct grading (off-by-one).
-/
private noncomputable instance Polytope.faceHomogenizationGradeOrder (P : Polytope R A) :
    GradeOrder ℕ (Face (P : ConvexSet R A)) := by
  let : ConvexSpace R (Homogenization R A) := ConvexSpace.ofModule
  have : PointedCone.FG (homogenize _ (P : ConvexSet R A)) :=
    IsPolytope.homogenize_fg (IsHomogenization.canonical R A) P.isPolytope
  let := PointedCone.FG.gradeOrder_finrank this
  refine GradeOrder.liftRight _
    (IsHomogenization.Face.homogenizeIso (IsHomogenization.canonical R A) _).strictMono ?_
  exact fun x y ↦ (apply_covBy_apply_iff _).mpr

end Field
