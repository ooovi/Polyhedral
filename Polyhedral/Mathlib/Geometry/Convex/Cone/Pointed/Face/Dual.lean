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

open Function

variable {R M N : Type*}

section Field

variable [Field R] [LinearOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]

variable (p : M →ₗ[R] N →ₗ[R] R) {C F F₁ F₂ : PointedCone R M}

-- # ISFACEOF

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

variable [fact : Fact (Surjective p.flip)] in
/-- An exposed face of a dual closed cone is itself exposed. -/
theorem IsExposedFaceOf.isDualClosed (hC : C.DualClosed p) (hF : F.IsExposedFaceOf C) :
    DualClosed p F := by
  obtain ⟨H, -, rfl⟩ := hF
  obtain ⟨y, hy⟩ := fact.out H
  refine DualClosed.inf hC <| dualClosed_coe ?_
  rw [← hy, ← Submodule.dual_singleton]
  exact Submodule.dual_flip_dualClosed p {y}

-- # FACE

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

variable {p} in
lemma Face.coe_dual_flip (F : Face (.dual p C)) :
    F.dual_flip p = C ⊓ (.dual p.flip F : Submodule R M) := rfl

variable {p} in
lemma Face.dual_flip_eq_dual_flip (F : Face (.dual p C)) (hC : C.DualClosed p) :
    F.dual_flip p = (F.dual p.flip : PointedCone R M) := by
  rw [Face.coe_dual, Face.coe_dual_flip, hC]

/-- Face duality is antitone. -/
lemma Face.dual_antitone : Antitone (dual p : Face C → Face _) :=
  fun _ _ hF _ xd ↦ ⟨xd.1, fun _ hx ↦ xd.2 (hF hx)⟩

/-- Face duality is antitone. -/
lemma Face.dual_flip_antitone : Antitone (dual_flip p : Face _ → Face C) :=
  fun _ _ hF _ xd ↦ ⟨xd.1, fun _ hx ↦ xd.2 (hF hx)⟩

lemma Face.dual_top : (⊤ : Face C).dual p = ⊥ := by
  rw [← Face.toPointedCone_eq_iff]
  rw [Face.coe_dual, Face.lineal_eq_bot]
  rw [← dual_lineal_eq_submodule_dual]
  exact inf_eq_right.mpr (lineal_le _)

lemma Face.dual_bot : (⊥ : Face C).dual p = ⊤ := by
  rw [← Face.toPointedCone_eq_iff]
  rw [Face.coe_dual]
  rw [show ((⊥ : Face C) : Set M) = ((⊥ : Face C) : PointedCone R M) from rfl]
  rw [Face.lineal_eq_bot]
  refine inf_eq_left.mpr ?_
  exact fun _ hy ↦ span_dual_le_dual_lineal (Submodule.subset_span hy)

lemma Face.dual_flip_top (hC : C.DualClosed p) :
    (⊤ : Face (.dual p C)).dual_flip p = ⊥ := by
  rw [← Face.toPointedCone_eq_iff, dual_flip_eq_dual_flip _ hC, dual_top, hC]

lemma Face.dual_flip_bot : (⊥ : Face (.dual p C)).dual_flip p = ⊤ := by
  rw [← Face.toPointedCone_eq_iff]
  rw [Face.coe_dual_flip]
  rw [show ((⊥ : Face (.dual p C)) : Set N) =
    ((⊥ : Face (.dual p C)) : PointedCone R N) from rfl]
  rw [Face.lineal_eq_bot]
  refine inf_eq_left.mpr ?_
  intro _ hx _ hy
  have hn := hy.2 hx
  simp at hn
  simpa using le_antisymm (hy.1 hx) hn

/-- If a face has nonempty relint, then its dual face is exposed. -/
lemma Face.dual_isExposed_of_nonempty_relint {F : Face C}
    (hF : Nonempty (relint (F : PointedCone R M))) : IsExposed (F.dual p) := by
  obtain ⟨x, hx⟩ := hF
  refine ⟨p x, fun _ hy ↦ hy (F.isFaceOf.le (relint_le hx)), ?_⟩
  ext y
  rw [Submodule.mem_inf]
  refine ⟨fun ⟨hyC, hyF⟩ ↦ ⟨hyC, (hyF (relint_le hx)).symm⟩,
    fun ⟨hyC, hxy⟩ => ⟨hyC, fun z hz ↦ ?_⟩⟩
  obtain ⟨c, hc, hxc⟩ :=
    (mem_relint_iff_forall_exists_gt_zero_forall_le_add_smul_mem.mp hx).2 (-z)
      (Submodule.neg_mem _ (Submodule.subset_span hz))
  have hpy := hyC (F.isFaceOf.le hxc)
  simp at hpy
  rw [gt_iff_lt, ← Nat.cast_pos (α := R)] at hc
  nlinarith [hyC (F.isFaceOf.le hz), show p x y = 0 from hxy]

end Field

end PointedCone
