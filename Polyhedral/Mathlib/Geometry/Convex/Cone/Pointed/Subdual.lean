/-
Copyright (c) 2025 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/

import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.DualClosed
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Face.Basic

/-!
This file defines the subdual of a cone w.r.t. another cone.
-/

namespace PointedCone

variable {R M N : Type*}

section CommRing

variable [CommRing R] [PartialOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]

variable (p : M →ₗ[R] N →ₗ[R] R) {C F : PointedCone R M}

/-- If `F` is a face of the cone `C`, then the subdual of `F` w.r.t. `C` is a face of the dual
of `C`, and is called the "dual face" to `F`. -/
def subdual (C F : PointedCone R M) : PointedCone R N :=
  (dual p C) ⊓ (.dual p F : Submodule R N)

variable {p} in
lemma subdual_def {C F : PointedCone R M} :
    subdual p C F = (dual p C) ⊓ (.dual p F : Submodule R N) := rfl

variable {p} in
lemma mem_subdual {C F : PointedCone R M} {x : N} :
    x ∈ subdual p C F ↔ x ∈ dual p C ∧ x ∈ Submodule.dual p F := by simp [subdual_def]

lemma subdual_antitone : Antitone (subdual p C) := by
  intro _ _ hF
  unfold subdual
  gcongr
  exact Submodule.dual_le_dual hF

end CommRing

section Field

variable [Field R] [LinearOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]

variable (p : M →ₗ[R] N →ₗ[R] R) {C F F₁ F₂ : PointedCone R M}

@[simp] lemma subdual_lineal : subdual p C C.lineal = dual p C := by
  rw [subdual_def, inf_eq_left]
  intro _ hx
  exact span_dual_le_dual_lineal (Submodule.subset_span hx)

@[simp] lemma subdual_bot : subdual p C ⊥ = dual p C := by
  simp [subdual_def]

lemma subdual_self : subdual p C C = (dual p C).lineal := by
  rw [subdual_def, ← dual_lineal_eq_submodule_dual]
  exact inf_eq_right.mpr (lineal_le (dual p C))

section DualClosed

variable (hC : C.DualClosed p)

/-- The subdual is injective. -/
-- only for fg
lemma subdual_inj : Function.Injective (subdual p C) := sorry

/-- The subdual is involutive. -/
-- only for fg
lemma subdual_subdual : subdual p.flip (dual p C) (subdual p C F) = F := sorry

/-- The subdual is strictly antitone. -/
lemma subdual_antitone_iff {F₁ F₂ : PointedCone R M} :
    subdual p C F₁ ≤ subdual p C F₂ ↔ F₂ ≤ F₁ where
  mpr := fun h => subdual_antitone p h
  mp := sorry

end DualClosed

end Field

end PointedCone
