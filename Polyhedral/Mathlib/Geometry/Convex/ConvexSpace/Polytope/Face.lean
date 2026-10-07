/-
Copyright (c) 2026 Olivia Röhrig, Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter, Olivia Röhrig
-/
module

public import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.Lattice
public import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Face.Homogenization
public import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Face.Lattice

import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Finite.Face.Grade
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.Homogenization

/-! This file proves results about faces of polytopes by transporting results from FG
cones along a homogenization. -/

public section

variable {R V A : Type*}

open Convexity IsConvexSet Affine

section Field

variable [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable [AddCommGroup V] [Module R V]
variable [AddTorsor V A] [ConvexSpace R A] [IsAffineConvexSpace R V A]

variable {C F : Set A}

include V in
/-- Faces of polytopes are polytopes. -/
theorem IsPolytope.face_isPolytope
    (hC : IsPolytope R C) (hF : IsFaceOf R F C) (hcF : IsConvexSet R F) :
    IsPolytope R (F : Set A) := by
  let : ConvexSpace R (Homogenization R A) := ConvexSpace.ofModule
  have homF := (IsHomogenization.canonical R A).homogenize_isFaceOf hcF hC.isConvexSet hF
  have := PointedCone.IsFaceOf.fg (IsPolytope.homogenize_fg _ hC) homF
  convert FG.dehomogenize_isPolytope this (fun _ a b ↦ weight_pos_of_mem_homogenize a b)
  rw [dehomogenize_homogenize _  hcF]

include V in
instance {P : Polytope R A} : CoeOut (Face P.isPolytope.isConvexSet) (Polytope R A) where
  coe F := ⟨_, IsPolytope.face_isPolytope P.isPolytope F.isFaceOf F.isConvexSet⟩

include V in
/-- The face lattice of a polytope as a graded order with grading given by the dimensions of
homogenization cones.

This is private since it does not yet have the correct grading (off-by-one).
-/
private noncomputable instance Polytope.faceHomogenizationGradeOrder (P : Polytope R A) :
    GradeOrder ℕ (Face P.isPolytope.isConvexSet) := by
  let : ConvexSpace R (Homogenization R A) := ConvexSpace.ofModule
  let ℋ := IsHomogenization.canonical R A
  have : (homogenize _ P).FG := IsPolytope.homogenize_fg ℋ P.isPolytope
  let := PointedCone.FG.gradeOrder_finrank this
  refine GradeOrder.liftRight _ (face_homogenizeIso ℋ P.isPolytope.isConvexSet).strictMono ?_
  exact fun x y ↦ (apply_covBy_apply_iff _).mpr

end Field
