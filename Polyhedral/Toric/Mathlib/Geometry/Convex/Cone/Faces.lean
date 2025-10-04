/-
Copyright (c) 2025 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.LinearAlgebra.SesquilinearForm

import Polyhedral.Toric.Mathlib.Geometry.Convex.Cone.Primspace

/-!
# Polyhedral cones
...
-/

open Function Module

variable {𝕜 M N : Type*}

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup M] [Module 𝕜 M] [Module.Finite 𝕜 M]
  [AddCommGroup N] [Module 𝕜 N] [Module.Finite 𝕜 N]

namespace PointedCone

def IsFaceOf (F C : PointedCone 𝕜 M)
  := ∃ P : PolyhedralCone.Primspace 𝕜 M, C ≤ P ∧ F = C ⊓ P.boundary

lemma IsFaceOf.trans {C₁ C₂ C₃ : PointedCone 𝕜 M} (h12 : C₂.IsFaceOf C₁) (h23 : C₃.IsFaceOf C₂) :
  C₃.IsFaceOf C₁ := sorry

lemma IsFaceOf.le {F C : PointedCone 𝕜 M} (hF : F.IsFaceOf C) : F ≤ C := sorry

lemma IsFaceOf.lineal (C : PointedCone 𝕜 M) : IsFaceOf C.lineal C := sorry

lemma IsFaceOf.self (C : PointedCone 𝕜 M) : C.IsFaceOf C := by
  use PolyhedralCone.Primspace.top
  constructor
  · -- simp [PolyhedralCone.Primspace.top]
    sorry
  · simp
    sorry

lemma IsFaceOf.inf {C F₁ F₂ : PointedCone 𝕜 M} (h1 : F₁.IsFaceOf C) (h2 : F₂.IsFaceOf C) :
  (F₁ ⊓ F₂).IsFaceOf C := sorry

variable (p : M →ₗ[𝕜] N →ₗ[𝕜] 𝕜) [p.IsPerfPair] in
def subdual (C F : PointedCone 𝕜 M) : PointedCone 𝕜 N := dual p F ⊓ dual p C

variable (p : M →ₗ[𝕜] N →ₗ[𝕜] 𝕜) [p.IsPerfPair] in
lemma IsFaceOf.subdual_dual {C F : PointedCone 𝕜 M} (hF : F.IsFaceOf C) :
    (subdual p C F).IsFaceOf (dual p C) := by
  sorry

lemma IsFaceOf.sup {C F₁ F₂ : PointedCone 𝕜 M} (h1 : F₁.IsFaceOf C) (h2 : F₂.IsFaceOf C) :
    (subdual .id (dual (Dual.eval 𝕜 M) C)
      ((subdual (Dual.eval 𝕜 M) C F₁) ⊓ (subdual (Dual.eval 𝕜 M) C F₂))).IsFaceOf C := by
  sorry

structure Face (C : PointedCone 𝕜 M) extends PointedCone 𝕜 M where
  isFaceOf : IsFaceOf toSubmodule C

def of_isFaceOf {F C : PointedCone 𝕜 M} (hF : F.IsFaceOf C) : Face C := ⟨F, hF⟩

instance (C : PointedCone 𝕜 M) : Bot (Face C) := ⟨of_isFaceOf <| IsFaceOf.lineal C⟩
instance (C : PointedCone 𝕜 M) : Top (Face C) := ⟨of_isFaceOf <| IsFaceOf.self C⟩

instance (C : PointedCone 𝕜 M) : Min (Face C) where
  min F₁ F₂ := of_isFaceOf <| IsFaceOf.inf F₁.isFaceOf F₂.isFaceOf

variable (p : M →ₗ[𝕜] N →ₗ[𝕜] 𝕜) [p.IsPerfPair] in
instance (C : PointedCone 𝕜 M) : Max (Face C) where
  max F₁ F₂ := of_isFaceOf <| IsFaceOf.sup F₁.isFaceOf F₂.isFaceOf

end PointedCone
