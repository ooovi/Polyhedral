/-
Copyright (c) 2025 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Halfspace
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Relint

/-! This file defines exposed faces of cones, namely ones that are the intersection of the cone with
a supporting hyperplane. This notion differs from the more general definition using positive
combinations, as given by `PointedCone.IsFaceOf`. The two agree on finitely generated cones, which
is proven elsewhere as `IsFaceOf.FG.exposed`. -/

open Module
open Submodule

namespace PointedCone

/- TODO: Reprove `IsFaceOf` theory here. -/

variable {R : Type*} [Field R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}
variable {C F F₁ F₂ : PointedCone R M}

/-- A face of a cone is exposed if it is the intersection of the cone with the zero set of a
linear functional that is nonnegative on the cone. -/
def IsExposedFaceOf (F C : PointedCone R M) :=
  ∃ φ : Dual R M, C ≤ φ.nonneg ∧ F = C ⊓ φ.ker

@[refl] lemma IsExposedFaceOf.refl (C : PointedCone R M) :
    C.IsExposedFaceOf C := ⟨0, by simp⟩

lemma IsExposedFaceOf.rfl {C : PointedCone R M} : C.IsExposedFaceOf C := refl C

lemma IsExposedFaceOf.le (hF : F.IsExposedFaceOf C) : F ≤ C := by
  obtain ⟨_, _, rfl⟩ := hF
  simp

/-- The intersection of two exposed faces is an exposed face. -/
lemma IsExposedFaceOf.inf {hF₁ : F₁.IsExposedFaceOf C} {hF₂ : F₂.IsExposedFaceOf C} :
    (F₁ ⊓ F₂).IsExposedFaceOf C := by
  obtain ⟨φ₁, hφ₁, rfl⟩ := hF₁
  obtain ⟨φ₂, hφ₂, rfl⟩ := hF₂
  use φ₁ + φ₂
  constructor
  · exact LinearMap.le_nonneg_add hφ₁ hφ₂
  · ext x
    simp only [Submodule.mem_inf]
    constructor
    · rintro ⟨⟨hx, h₁⟩, -, h₂⟩
      simp only [restrictScalars_mem, LinearMap.mem_ker] at h₁ h₂
      exact ⟨hx, by simp [h₁, h₂]⟩
    · rintro ⟨hx, hsum⟩
      have h₁ := eq_zero_of_add_nonpos_left (hφ₁ hx) (hφ₂ hx) (le_of_eq hsum)
      have h₂ : φ₂ x = 0 := by simpa [h₁] using hsum
      exact ⟨⟨hx, h₁⟩, hx, h₂⟩

/-- An exposed face is a face. -/
lemma IsExposedFaceOf.isFaceOf (hF : F.IsExposedFaceOf C) : F.IsFaceOf C := by
  obtain ⟨φ, hφ, rfl⟩ := hF
  refine IsFaceOf.of_mem_of_add_mem_left inf_le_left ?_
  rintro x y hx hy ⟨-, hxy⟩
  refine ⟨hx, ?_⟩
  change φ (x + y) = 0 at hxy
  rw [map_add] at hxy
  exact eq_zero_of_add_nonpos_left (hφ hx) (hφ hy) (le_of_eq hxy)


-- # QUOTIENTS

-- probably the better formulation of the below
lemma IsExposedFaceOf.quot_iff' {S : Submodule R M} (hF : F.IsFaceOf C) (hF : S ≤ span R F) :
    F.IsExposedFaceOf C ↔ (F.quot S).IsExposedFaceOf (C.quot S) := sorry

lemma IsExposedFaceOf.quot_iff (hF₁ : F₁.IsFaceOf C) (hF₂ : F₂.IsFaceOf C) (hF : F₂ ≤ F₁) :
    F₁.IsExposedFaceOf C ↔ (F₁.quot (span R F₂)).IsExposedFaceOf (C.quot (span R F₂)) := sorry

variable {S : Submodule R M}

variable (S) in
lemma IsExposedFaceOf.restrict (hF : F.IsExposedFaceOf C) :
    (restrict S F).IsExposedFaceOf (restrict S C) := sorry

lemma IsExposedFaceOf.embed {C F : PointedCone R S} (hF : F.IsExposedFaceOf C) :
    (embed F).IsExposedFaceOf (embed C) := sorry


-- # LATTICE

def Face.IsExposed (F : Face C) := (F : PointedCone R M).IsExposedFaceOf C

lemma Face.isExpose_def (F : Face C) :
   F.IsExposed ↔ (F : PointedCone R M).IsExposedFaceOf C := by rfl

end PointedCone
