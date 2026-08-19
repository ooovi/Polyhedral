/-
Copyright (c) 2025 Olivia Röhrig, Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Olivia Röhrig, Martin Winter
-/

import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.DualClosed
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Face.Exposed

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

/-- Intersecting a cone with the common kernel of a set of functionals in the dual cone produces a
face of the cone. -/
lemma IsFaceOf.inf_submodule_dual_of_le_dual {s : Set N} (hS : s ⊆ dual p C) :
    IsFaceOf (C ⊓ (.dual p.flip s : Submodule R M)) C := by
  refine .of_mem_of_add_mem_left (by simp) ?_
  intro x y hx hy hxy
  refine ⟨hx, fun f hf => ?_⟩
  have h : p x f + p y f = 0 := by
    simpa only [LinearMap.flip_apply, map_add] using (hxy.2 hf).symm
  rw [add_eq_zero_iff_of_nonneg (hS hf hx) (hS hf hy)] at h
  exact h.1.symm

/-- The dual face of a face. This is a face of the dual cone. -/
def Face.dual (F : Face C) : Face (dual p C) where
  __ := (.dual p C : PointedCone R N) ⊓ (.dual p F : Submodule R N)
  isFaceOf := by simpa only [LinearMap.flip_flip] using
    .inf_submodule_dual_of_le_dual (p := p.flip) (s := F) (F.isFaceOf.le.trans subset_dual_dual)

/-- The dual face of a face of the dual cone. This is a face of the primal cone. -/
def Face.dual_flip (F : Face (.dual p C)) : Face C where
  __ := C ⊓ (.dual p.flip F : Submodule R M)
  isFaceOf := .inf_submodule_dual_of_le_dual p F.isFaceOf.le

lemma Face.coe_dual (F : Face C) :
    F.dual p = (.dual p C : PointedCone R N) ⊓ (.dual p F : Submodule R N) := rfl

lemma Face.coe_dual_flip (F : Face (.dual p C)) :
    F.dual_flip p = C ⊓ (.dual p.flip F : Submodule R M) := rfl

lemma Face.dual_flip_eq_dual_flip (F : Face (.dual p C)) (hC : C.DualClosed p) :
    (F.dual p.flip : PointedCone R M) = F.dual_flip p := by
  change PointedCone.dual p.flip (PointedCone.dual p C) ⊓
    (.dual p.flip F : Submodule R M) = C ⊓ (.dual p.flip F : Submodule R M)
  rw [hC]

/-- Face duality is antitone. -/
lemma Face.dual_antitone : Antitone (dual p : Face C → Face _) :=
  fun _ _ hF _ xd ↦ ⟨xd.1, fun _ hx ↦ xd.2 (hF hx)⟩

/-- Face duality is antitone. -/
lemma Face.dual_flip_antitone : Antitone (dual_flip p : Face _ → Face C) :=
  fun _ _ hF _ xd ↦ ⟨xd.1, fun _ hx ↦ xd.2 (hF hx)⟩

end Field

end PointedCone
