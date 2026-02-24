/-
Copyright (c) 2025 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Order.Partition.Basic

import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.MinkowskiWeyl
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Face.Lattice
-- import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Face.Lattice2
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Relint
-- import Polyhedral.Hyperplane
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Halfspace

open Module
open Submodule

namespace PointedCone

/- TODO: basically we need to copy almost everything from `IsFaceOf ` and reprove it for
  `IsExposedFaceOf`. -/

variable {R : Type*} [Field R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}
variable {C F F₁ F₂ : PointedCone R M}

def IsExposedFaceOf (F C : PointedCone R M) :=
  ∃ φ : M →ₗ[R] R, (∀ x ∈ C, φ x ≥ 0) ∧ (∀ x ∈ C, φ x = 0 ↔ x ∈ F)
  -- ∃ φ : M →ₗ[R] R, ∀ x ∈ C, φ x ≥ 0 ∧ (φ x = 0 ↔ x ∈ F)

-- variable (p) in
-- def IsExposedFaceOf' (F C : PointedCone R M) :=
--   ∃ φ : N, (∀ x ∈ C, p x φ ≥ 0) ∧ (∀ x ∈ C, p x φ = 0 ↔ x ∈ F)

-- lemma IsExposedFaceOf.def_iff :
--     F.IsExposedFaceOf C ↔ ∃ φ : M →ₗ[R] R, (∀ x ∈ C, φ x ≥ 0) ∧ (∀ x ∈ C, φ x = 0 ↔ x ∈ F) := by rfl

@[refl] lemma IsExposedFaceOf.refl (C : PointedCone R M) : C.IsExposedFaceOf C := ⟨0, by simp⟩
lemma IsExposedFaceOf.rfl {C : PointedCone R M} : C.IsExposedFaceOf C := refl C

lemma IsExposedFaceOf.le (hF : F.IsExposedFaceOf C) : F ≤ C := sorry

lemma IsExposedFaceOf.inf {hF₁ : F₁.IsExposedFaceOf C} {hF₂ : F₂.IsExposedFaceOf C} :
    (F₁ ⊓ F₂).IsExposedFaceOf C := by
  obtain ⟨φ₁, hφ₁, hφ₁'⟩ := hF₁
  obtain ⟨φ₂, hφ₂, hφ₂'⟩ := hF₂
  use φ₁ + φ₂
  simp only [LinearMap.add_apply, ge_iff_le, Submodule.mem_inf]
  constructor
  · intro x hx
    exact add_nonneg (hφ₁ x hx) (hφ₂ x hx)
  · intro x hx
    constructor
    · intro H
      have h := eq_zero_of_add_nonpos_left (hφ₁ x hx) (hφ₂ x hx) (le_of_eq H)
      simp only [h, zero_add] at H
      exact ⟨(hφ₁' x hx).mp h, (hφ₂' x hx).mp H⟩
    · intro H
      have h₁ := (hφ₁' x hx).mpr H.1
      have h₂ := (hφ₂' x hx).mpr H.2
      linarith

-- NOTE: Consider the dual of positive orthant in the space of finitely supported sequences.
--  Here the lineality space is {0} and is exposed, but not using a linear form of
--  the form p x. There are too few linear forms with finite support.
-- TODO: add FinRank (or FinSalRank) as condition.
variable (p) in
lemma IsExposedFaceOf.subdual_dual (hF : F.IsFaceOf C) :
    (subdual p C F).IsExposedFaceOf (dual p C) := by
  obtain ⟨φ, hφ⟩ := F.relint_nonempty sorry -- currently requires FinRank (or FinSalRank later)
  use p φ
  constructor <;> intro x hx
  · exact hx <| hF.le (F.relint_le hφ)
  constructor <;> intro h
  · rw [mem_subdual]
    constructor
    · exact hx
    simp only [Submodule.mem_dual, SetLike.mem_coe]
    intro ψ hψ
    -- here we need to use that φ is in the relint. I think we need more relint lemmas first!
    replace hφ := F.relint_le hφ
    simp at hφ
    sorry
  · simpa using (h.2 <| F.relint_le hφ).symm

alias subdual_exposed := IsExposedFaceOf.subdual_dual

/-- The lineality space of a dual closed cone is an exposed face. -/
lemma IsExposedFaceOf.lineal {C : PointedCone R M} (hC : C.DualClosed p) :
    IsExposedFaceOf C.lineal C := by classical
  rw [← hC]
  nth_rw 1 [← subdual_self]
  apply subdual_dual
  rfl

-- lemma exists_dual_pos' {C : PointedCone R M} (hC : C.Salient) :
--     ∃ φ : M →ₗ[R] R, ∀ x ∈ C, φ x ≥ 0 ∧ (φ x = 0 → x = 0) := sorry

-- States that a pointed cone minus its origin is contained in the interior of a halfspace.
variable (p) in
lemma exists_dual_pos (C : PointedCone R M) : -- only true when FinSalRank
    ∃ φ : N, ∀ x ∈ C, 0 ≤ p x φ ∧ (p x φ = 0 → x ∈ C.lineal) :=
  -- Idea: choose φ from relint of dual cone.
  --  (we need to show that relints of dual cones are nonempty)
  sorry

-- States that a pointed cone minus its origin is contained in the interior of a halfspace.
variable (p) in
lemma exists_dual_pos₀ {C : PointedCone R M} (hC : C.Salient) :
    ∃ φ : N, ∀ x ∈ C, 0 ≤ p x φ ∧ (p x φ = 0 → x = 0) :=
  -- Idea: choose φ from relint of dual cone.
  --  (we need to show that relints of dual cones are nonempty)
    sorry

/-- An exposed face is a face. -/
lemma IsExposedFaceOf.isFaceOf (hF : F.IsExposedFaceOf C) : F.IsFaceOf C := by
  rw [isFaceOf_iff_mem_of_add_mem]
  refine ⟨hF.le, ?_⟩
  intro _ _ hx hy hcxy
  let ⟨φ, hφ, H⟩ := hF
  rw [← H _ hx]
  have h := (H _ <| hF.le hcxy).mpr hcxy
  rw [map_add] at h
  exact eq_zero_of_add_nonpos_left (hφ _ hx) (hφ _ hy) (le_of_eq h)

lemma IsExposedFaceOf.quot_iff (hF₁ : F₁.IsFaceOf C) (hF₂ : F₂.IsFaceOf C) (hF : F₂ ≤ F₁) :
    F₁.IsExposedFaceOf C ↔ (F₁.quot F₂.linSpan).IsExposedFaceOf (C.quot F₂.linSpan) := sorry

variable {S : Submodule R M}

variable (S) in
lemma IsExposedFaceOf.restrict (hF : F.IsExposedFaceOf C) :
    (restrict S F).IsExposedFaceOf (restrict S C) := sorry

lemma IsExposedFaceOf.embed {C F : PointedCone R S} (hF : F.IsExposedFaceOf C) :
    (embed F).IsExposedFaceOf (embed C) := sorry






--------------------------------------

def HalfspaceOrTop.IsSupportAt (H : HalfspaceOrTop R M) (F : Face C) :=
    C ≤ H ∧ C ⊓ H.boundary = F

-- def HyperplaneOrTop.IsSupportAt (H : HyperplaneOrTop R M) (F : Face C) :=
--     ∃ H' : HalfspaceOrTop R M, H'.boundary = H ∧ C ≤ H' ∧ C ⊓ H = F

def Face.IsExposed (F : Face C) := ∃ H : HalfspaceOrTop R M, H.IsSupportAt F
-- def Face.IsExposed (F : Face C) := ∃ H : HalfspaceOrTop R M, C ≤ H ∧ C ⊓ H.boundary = F

lemma Face.isExpose_def (F : Face C) :
    F.IsExposed ↔ ∃ φ : M →ₗ[R] R, (∀ x ∈ C, φ x ≥ 0) ∧ (∀ x ∈ C, φ x = 0 ↔ x ∈ F) := sorry

-- theorem bot_isExposed (hC : C.IsDualClosed p) : (⊥ : Face C).IsExposed := by
--   -- reduce to salient case via quotients
--   wlog h : C.Salient
--   · sorry
--   rw [Face.isExpose_def]
--   have hC : C.IsDualClosed (Dual.eval R M) := hC.to_eval
--   obtain ⟨D, hD, hDC⟩ := hC.exists_of_dual_flip
--   let φ := D.relint_nonempty'.some
--   use φ
--   constructor
--   · sorry
--   · sorry

-- theorem IsExposed.of_isExposed_face_quot {F : Face C} {G : Face (F.quot)} (hG : G.IsExposed) :
--     F.IsExposed := by
--   -- idea: the comap of a supporting halfspace is again a supporting halfspace.
--   sorry

-- variable (p) [Fact (Surjective p.flip)] in
-- lemma HyperplaneOrTop.isDualClosed (H : HyperplaneOrTop R M) : IsDualClosed p H := sorry

-- variable [Fact (Surjective p.flip)] in
-- theorem IsExposed.isDualClosed (hC : C.IsDualClosed p) {F : Face C} (hF : F.IsExposed) :
--     IsDualClosed p F := by
--   obtain ⟨H, h, hH⟩ := hF
--   rw [← hH]
--   exact IsDualClosed.inf hC (HyperplaneOrTop.isDualClosed p _)

/-- The dual of a face is an exposed face. -/
def Face.dual_isExposed (F : Face C) : IsExposed (F.dual p) := by
  sorry -- obvious by definition of dual face

-- def foo''''' (F : Face C) :
--     ∃ φ ∈ dual (Dual.eval R M) C, φ ∉ (dual (Dual.eval R M) C).lineal ∧ F.span ≤ ker φ :=
--   sorry

/-
 * The double dual face of F gives a face F' that is exposed and contains F.
 * The dual of a proper face cannot be bot (true?)
 * The double dual F' is then not top.
 * The double dual is then a proper exposed face that contains F
 * In particula, all top proper faces are exposed
-/

def IsDualClosed.face_dual_flip (F : Face (dual p C)) (hC : C.IsDualClosed p) : Face C :=
  sorry -- ⟨C ⊓ Submodule.dual (M := N) p.flip F, sorry⟩

-- theorem Face.dual_dual (F : Face C) : F ≤ dual_flip p (dual p F) := sorry

variable (p) in
lemma Face.dual_neq_bot_of_neq_top {F : Face C} (hF : F ≠ ⊤) :
    F.dual p ≠ ⊥ := sorry

theorem Face.exists_proper_exposed_le (F : Face C) (hF : F ≠ ⊤) :
    ∃ F' : Face C, F' ≠ ⊤ ∧ F'.IsExposed ∧ F ≤ F' := by
  -- Since F not top, dual face is not bot (??, use Face.Nontrivial.dual)
  -- choose a non-zero point from the dual face
  -- this yield a supporting hyperplane to C
  -- this defines a face F'
  -- this face contains F
  -- this face is exposed by def
  -- this face is not top by def
  sorry



-- theorem IsDualClosed.quot (hC : C.IsDualClosed p) (F : Face C) :
--     F.quot.IsDualClosed (Dual.eval R (M ⧸ F.span)) := sorry

end PointedCone
