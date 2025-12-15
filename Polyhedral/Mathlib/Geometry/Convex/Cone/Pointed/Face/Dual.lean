/-
Copyright (c) 2025 Olivia Röhrig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Olivia Röhrig
-- -/

import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Dual
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Face.Basic


/-!
# Faces of pointed cones
-/

namespace PointedCone

variable {R M N : Type*}


/-!
### Faces of the dual cone
-/

section CommRing

variable [CommRing R] [PartialOrder R] [IsOrderedRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] (p : M →ₗ[R] N →ₗ[R] R) {C : PointedCone R M}

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
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable (p : M →ₗ[R] N →ₗ[R] R) {C F F₁ F₂ : PointedCone R M}

/-- The subdual of a face is a face of the dual. -/
lemma IsFaceOf.subdual_dual (hF : F.IsFaceOf C) :
    (subdual p C F).IsFaceOf (dual p C) := by
  unfold subdual
  apply iff_mem_of_add_mem.mpr ⟨by simp, ?_⟩
  intro x y xd
  simp only [mem_dual, SetLike.mem_coe, Submodule.mem_inf, map_add, Submodule.restrictScalars_mem,
    Submodule.mem_dual, xd, true_and, and_imp]
  intro yC _ n'on _ mF
  apply eq_of_le_of_ge
  · exact xd (hF.le mF)
  · rw [n'on mF]
    exact (le_add_iff_nonneg_right _).mpr <| yC (hF.le mF)

-- ## RPIORITY
@[simp] lemma subdual_lineal : subdual p C C.lineal = dual p C := sorry
@[simp] lemma subdual_bot : subdual p C ⊥ = dual p C := sorry

lemma subdual_self : subdual p C C = (dual p C).lineal := sorry

section IsDualClosed

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

end IsDualClosed

end Field

end PointedCone
