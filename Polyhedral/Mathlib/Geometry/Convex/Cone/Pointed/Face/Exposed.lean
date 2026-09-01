/-
Copyright (c) 2025 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/
module

public import Mathlib.Geometry.Convex.Cone.Face.Lattice
public import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.LinearMap
public import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Restrict

/-! This file defines exposed faces of cones, namely ones that are the intersection of the cone with
a supporting hyperplane. This notion differs from the more general definition using positive
combinations, as given by `PointedCone.IsFaceOf`. The two agree on finitely generated cones, which
is proven elsewhere as `IsFaceOf.FG.exposed`. -/

@[expose] public section

open Module
open Submodule

namespace PointedCone

/- TODO: Reprove `IsFaceOf` theory here. -/

variable {R : Type*} [Field R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}
variable {C F F₁ F₂ : PointedCone R M}

/- NOTE: the current implementation of `IsExposedFaceOf` might benefit from including a pairing
`p` that restrict the possible functionals available for exposing a face. This might be useful
since exposed faces are particularly interesting in the context of duality and separation where the
current code basis works intensively with general pairings. The definition would change to:

  `∃ y : N, C ≤ (p.flip y).nonneg ∧ F = C ⊓ (p.flip y).ker`

Currently lemmas such as `IsExposedFaceOf.dualClosed` mix notions of duality and exposedness, and
need to assume `Surjective p.flip` in order to work properly. This is a very strong assumption not
satisfies by many pairing in infinite dimensional spaces.
-/

/-- A face of a cone is exposed if it is the intersection of the cone with the zero set of a
linear functional that is nonnegative on the cone. -/
def IsExposedFaceOf (F C : PointedCone R M) :=
  ∃ φ : Dual R M, C ≤ φ.nonneg ∧ F = C ⊓ φ.ker

@[refl] lemma IsExposedFaceOf.refl (C : PointedCone R M) :
    C.IsExposedFaceOf C := ⟨0, by simp⟩

lemma IsExposedFaceOf.rfl {C : PointedCone R M} : C.IsExposedFaceOf C := refl C

alias IsExposedFaceOf.self := IsExposedFaceOf.rfl
alias IsExposedFaceOf.top := IsExposedFaceOf.rfl

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

-- # QUOTIENT

-- probably the better formulation of `IsExposedFaceOf.quot_iff`.
lemma IsExposedFaceOf.quot_iff' {S : Submodule R M} (hF : F.IsFaceOf C) (hF : S ≤ span R F) :
    F.IsExposedFaceOf C ↔ (F.quot S).IsExposedFaceOf (C.quot S) := sorry

lemma IsExposedFaceOf.quot_iff (hF₁ : F₁.IsFaceOf C) (hF₂ : F₂.IsFaceOf C) (hF : F₂ ≤ F₁) :
    F₁.IsExposedFaceOf C ↔ (F₁.quot (span R F₂)).IsExposedFaceOf (C.quot (span R F₂)) := sorry

-- # RESTRICT / EMBED

variable {S : Submodule R M}

variable (S) in
lemma IsExposedFaceOf.restrict (hF : F.IsExposedFaceOf C) :
    (restrict S F).IsExposedFaceOf (restrict S C) := sorry

lemma IsExposedFaceOf.embed {C F : PointedCone R S} (hF : F.IsExposedFaceOf C) :
    (embed F).IsExposedFaceOf (embed C) := sorry

-- # FACE

def Face.IsExposed (F : Face C) := (F : PointedCone R M).IsExposedFaceOf C

lemma Face.isExposed_def (F : Face C) :
   F.IsExposed ↔ (F : PointedCone R M).IsExposedFaceOf C := by rfl

lemma Face.top_isExposed : (⊤ : Face C).IsExposed := IsExposedFaceOf.top

end PointedCone
