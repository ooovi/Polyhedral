/-
Copyright (c) 2025 Olivia Röhrig, Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Olivia Röhrig, Martin Winter
-/

import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Subdual
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Face.Lattice

/-!
This file defines the dual face of a face of `C` as a face of `dual p C`, and proves basic lemmas.
-/

namespace PointedCone

variable {R M N : Type*}

section Field

variable [Field R] [LinearOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]

variable (p : M →ₗ[R] N →ₗ[R] R) {C F F₁ F₂ : PointedCone R M}

/-- The subdual of a face of the cone is a face of the dual cone. -/
lemma IsFaceOf.subdual_dual (hF : F.IsFaceOf C) :
    (subdual p C F).IsFaceOf (dual p C) := by
  unfold subdual
  refine of_mem_of_add_mem_left (by simp) ?_
  intro x y hxC
  simp only [mem_dual, SetLike.mem_coe, Submodule.mem_inf, map_add, Submodule.restrictScalars_mem,
    Submodule.mem_dual, hxC, true_and, and_imp]
  intro hy _ h _ hxF
  refine eq_of_le_of_ge (hxC (hF.le hxF)) ?_
  rw [h hxF]
  exact (le_add_iff_nonneg_right _).mpr <| hy (hF.le hxF)

/-- The subdual of a face of the dual cone is a face of the cone. -/
lemma IsFaceOf.subdual_flip_dual (hC : C.DualClosed p) {F : PointedCone R N}
    (hF : F.IsFaceOf (dual p C)) : (subdual p.flip (dual p C) F).IsFaceOf C := by
  nth_rw 2 [← LinearMap.flip_flip p]
  rw [← dual_flip_dual_dual_flip]
  simp only [LinearMap.flip_flip, dual_dual_flip_dual]
  convert hF.subdual_dual p.flip
  exact hC.symm

/-- The face of the dual cone that is dual to `F` in the face lattice of the cone. -/
def Face.dual (F : Face C) : Face (dual p C) := ⟨_, F.isFaceOf.subdual_dual p⟩

/-- The face of the cone that is dual to `F` in the face lattice of the dual cone, or ⊥ if
the cone is not dual closed.

Note that naturally the dual of `F` lies in `dual p.flip (dual p C)`, which is `C` only if `C`
is dual closed. Hence, the face
We chose this definition so that it can be used without passing additional argument.
Most lemmas using this definition will need to assume dual closed or some stronger assumption.
-/
noncomputable def Face.dual_flip (F : Face (.dual p C)) : Face C :=
  if hC : DualClosed p C
    then ⟨_, F.isFaceOf.subdual_flip_dual p hC⟩
    else ⊥

@[simp] lemma Face.dual_flip_of_dualClosed (F : Face (.dual p C)) (hC : C.DualClosed p) :
    (F.dual_flip p : PointedCone R M) = subdual p.flip (.dual p C) F := by
  rw [dual_flip, dite_eq_left hC]

lemma Face.dual_flip_eq_dual_flip (F : Face (.dual p C)) (hC : C.DualClosed p) :
    (F.dual p.flip : PointedCone R M) = F.dual_flip p := by
  rw [dual_flip_of_dualClosed _ _ hC]; rfl

lemma Face.dual_antitone : Antitone (dual p : Face C → Face _) :=
  fun _ _ hF _ xd => subdual_antitone p hF xd

section FG

variable (hC : C.FG)

/-- The subdual is injective. -/
lemma Face.dual_inj : Function.Injective (Face.dual p : Face C → _) := sorry

/-- The subdual is involutive. -/
lemma Face.dual_dual_flip (F : Face C) : (F.dual p).dual_flip p = F := sorry

/-- The subdual is strictly antitone. -/
lemma subdual_antitone_iff {F₁ F₂ : PointedCone R M} :
    subdual p C F₁ ≤ subdual p C F₂ ↔ F₂ ≤ F₁ where
  mpr := fun h => subdual_antitone p h
  mp := sorry

end FG

end Field

end PointedCone
