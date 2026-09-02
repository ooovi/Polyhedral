/-
Copyright (c) 2025 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/
module

public import Mathlib.RingTheory.LocalRing.Basic

import Mathlib.Algebra.Algebra.Basic

/-!
This file contains results about linear maps.
-/

public section

namespace LinearMap

open Function

variable {R M M₁ M₂ N : Type*}

section Ring

variable [Ring R]
variable [AddCommGroup M₁] [Module R M₁]
variable [AddCommGroup M₂] [Module R M₂]

@[simp]
lemma injective_neg_iff {f : M₂ →ₗ[R] M₁} : Injective (-f) ↔ Injective f := by
  simp [Function.Injective]

@[simp]
lemma surjective_neg_iff {f : M₂ →ₗ[R] M₁} : Surjective (-f) ↔ Surjective f := by
  constructor
  · intro h x
    simpa using h (-x)
  · intro h x
    obtain ⟨y, hy⟩ := h (-x)
    exact ⟨y, by simp [hy]⟩

end Ring

section Field

variable [Field R]
variable [AddCommGroup M] [Module R M]

lemma exists_smul_of_ker_le_ker {p q : M →ₗ[R] R} (h : p.ker ≤ q.ker) :
    ∃ a : R, q = a • p := by
  by_cases hp : p = 0
  · simpa [hp] using h
  · simp only [LinearMap.ext_iff, not_forall] at hp
    obtain ⟨x, hx⟩ := hp
    refine ⟨q x / p x, LinearMap.ext fun y ↦ ?_⟩
    rw [smul_apply, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff hx]
    have hxy := h (show p x • y - p y • x ∈ p.ker by simp [mul_comm])
    simpa [sub_eq_zero, mul_comm] using hxy

lemma ker_le_ker {p q : M →ₗ[R] R} (hq : q ≠ 0) :
    p.ker ≤ q.ker ↔ p.ker = q.ker where
  mp h := by
    obtain ⟨a, rfl⟩ := exists_smul_of_ker_le_ker h
    exact (ker_smul p a fun ha ↦ hq (by simp [ha])).symm
  mpr := le_of_eq

end Field

end LinearMap
