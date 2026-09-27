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
import Polyhedral.Mathlib.Order.WithBot

/-! This file proves results about faces of polytopes by transporting results from FG
cones along a homogenization. -/

public section

variable {R V W A : Type*}

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
  let W := Homogenization R A
  let : ConvexSpace R W := ConvexSpace.ofModule
  have homC := IsPolytope.homogenize_fg (W := W) hC
  have homF := IsHomogenization.homogenize_isFaceOf (W := W) hF
  have := PointedCone.IsFaceOf.fg homC homF
  convert FG.dehomogenize_isPolytope this (fun _ a b ↦ weight_pos_of_mem_homogenize a b)
  simp [dehomogenize_homogenize]

include V in
instance {P : Polytope R A} : CoeOut (Face (P : ConvexSet R A)) (Polytope R A) where
  coe F := ⟨_, IsPolytope.face_isPolytope P.isPolytope F.isFaceOf⟩

instance {P : Polytope R A} (F : Face (P : ConvexSet R A)) :
    Module.Finite R (vectorSpan R (F.toConvexSet : Set A)) :=
  IsPolytope.finite_vectorSpan (IsPolytope.face_isPolytope P.isPolytope F.isFaceOf)

/-- The face lattice of a polytope is graded by the dimension of the affine span of each face,
with the empty face receiving the grade `⊥`. -/
noncomputable instance (P : Polytope R A) :
    GradeMinOrder (WithBot ℕ) (Face (P : ConvexSet R A)) where
  grade F := (affineSpan R F.carrier).finDim
  grade_strictMono x y h := by
    let : ConvexSpace R (Homogenization R A) := ConvexSpace.ofModule
    simp only [Face.carrier_eq_coe, Face.coe_eq_toConvexSet_coe,
      finDim_affineSpan_eq_pred_finrank_homogenize (W := Homogenization R A)]
    refine Order.pred_lt_pred_of_not_isMin ?_ (by simp)
    exact_mod_cast PointedCone.FG.finrank_strictMono (IsPolytope.homogenize_fg P.isPolytope)
      (IsHomogenization.Face.homogenizeIso.strictMono h)
  covBy_grade x y h := by
    let : ConvexSpace R (Homogenization R A) := ConvexSpace.ofModule
    have := PointedCone.FG.finrank_covBy (IsPolytope.homogenize_fg P.isPolytope)
      ((apply_covBy_apply_iff
        (IsHomogenization.Face.homogenizeIso (W := Homogenization R A))).mpr h)
    have : (homogenize (Homogenization R A) x.toConvexSet).finrank + 1
        = (homogenize (Homogenization R A) y.toConvexSet).finrank :=
      Nat.covBy_iff_add_one_eq.mp this
    simp only [Face.carrier_eq_coe, Face.coe_eq_toConvexSet_coe,
      finDim_affineSpan_eq_pred_finrank_homogenize (W := Homogenization R A), ← this]
    exact Order.succ_eq_iff_covBy.mp (by simp)
  isMin_grade f h := by simp [isMin_iff_eq_bot.mp h]

section Homogenization

variable [AddCommGroup W] [Module R W] [hom : IsHomogenization R A W]

theorem Polytope.grade_eq_pred_finrank_homogenize {P : Polytope R A}
    (f : Face (P : ConvexSet R A)) :
    GradeOrder.grade f = Order.pred ((homogenize W f.toConvexSet).finrank : WithBot ℕ) :=
  finDim_affineSpan_eq_pred_finrank_homogenize _

theorem Polytope.succ_grade_eq_finrank_homogenize {P : Polytope R A}
    (f : Face (P : ConvexSet R A)) :
    Order.succ (GradeOrder.grade f : WithBot ℕ) = (homogenize W f.toConvexSet).finrank := by
  rw [Polytope.grade_eq_pred_finrank_homogenize (W := W), Order.succ_pred_of_not_isMin (by simp)]

end Homogenization

end Field
