/-
Copyright (c) 2025 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Mathlib.RingTheory.Finiteness.Basic

import Polyhedral.Halfspace

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

-- This is extreme face
def IsFaceOf' (F C : PointedCone 𝕜 M)
  := ∀ x ∈ C, ∀ y ∈ C, ∀ t ∈ Set.Icc 0 1, t • x  + (1 - t) • y ∈ F → (x ∈ F ∧ y ∈ F)

-- This is exposed face
def IsFaceOf (F C : PointedCone 𝕜 M)
  := ∃ H : HalfspaceOrTop 𝕜 M, C ≤ H ∧ C ⊓ H.boundary = F

lemma IsFaceOf.trans {C₁ C₂ C₃ : PointedCone 𝕜 M} (h12 : C₂.IsFaceOf C₁) (h23 : C₃.IsFaceOf C₂) :
  C₃.IsFaceOf C₁ := sorry

lemma IsFaceOf.le {F C : PointedCone 𝕜 M} (hF : F.IsFaceOf C) : F ≤ C := sorry

omit [Module.Finite 𝕜 M] in
lemma IsFaceOf.self (C : PointedCone 𝕜 M) : C.IsFaceOf C := ⟨⊤, by simp⟩

lemma IsFaceOf.lineal (C : PointedCone 𝕜 M) : IsFaceOf C.lineal C := by
  by_cases C.lineal ≥ C
  case pos h => rw [le_antisymm (PointedCone.lineal_le C) h]; exact self C
  case neg h =>
    simp at h
    obtain ⟨x, hx⟩ := Set.not_subset_iff_exists_mem_notMem.mp h
    -- use .of_dual_pt x -- DANG, need x from the dual space
    sorry

lemma IsFaceOf.inf {C F₁ F₂ : PointedCone 𝕜 M} (h₁ : F₁.IsFaceOf C) (h₂ : F₂.IsFaceOf C) :
    (F₁ ⊓ F₂).IsFaceOf C := by
  obtain ⟨⟨S₁, ⟨x₁, rfl⟩⟩, hCH₁, rfl⟩ := h₁
  obtain ⟨⟨S₂, ⟨x₂, rfl⟩⟩, hCH₂, rfl⟩ := h₂
  use .of_dual_pt (x₁ + x₂)
  constructor
  · rw [← SetLike.coe_subset_coe, Set.subset_def] at *
    intro x hx
    simp at *
    have h := add_le_add (hCH₁ x hx) (hCH₂ x hx)
    rw [add_zero] at h
    exact h
  · ext x
    simp [HalfspaceOrTop.boundary, PointedCone.lineal_mem]
    constructor
    · intro h
      specialize hCH₁ h.1
      specialize hCH₂ h.1
      simp at *
      sorry
    · intro h
      specialize hCH₁ h.1.1
      specialize hCH₂ h.1.1
      simp at *
      sorry

-- TODO: the subdual strategy for taking the sup of faces only works for polyhedral cones

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

lemma IsFaceOf.sSup {C : PointedCone 𝕜 M} {Fs : Set (PointedCone 𝕜 M)}
    (hFs : ∀ F ∈ Fs, F.IsFaceOf C) : (sSup Fs).IsFaceOf C := by
  sorry

-- lemma IsFaceOf.sup' {C F₁ F₂ : PointedCone 𝕜 M} (h1 : F₁.IsFaceOf C) (h2 : F₂.IsFaceOf C) :
--     (sSup {F : PointedCone 𝕜 M | F.IsFaceOf C ∧ F₁ ≤ F ∧ F₂ ≤ F}).IsFaceOf C := by
--   sorry

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

-- instance {C : PolyhedralCone 𝕜 M} : Coe (Face C) (PolyhedralCone 𝕜 M) := sorry

end PointedCone
