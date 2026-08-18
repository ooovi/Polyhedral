/-
Copyright (c) 2025 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.RingTheory.LocalRing.Basic

/-!
This file contains results about linear maps.
-/

namespace LinearMap

variable {R : Type*} [Field R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]

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

end LinearMap
