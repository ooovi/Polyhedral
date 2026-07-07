/-
Copyright (c) 2026 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/

import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.SubMulActionWithZero

/-!
This file proves results about sets closed under multiplication by non-negative scalars.
-/

@[expose] public section

namespace SubMulAction₀

open Function Set

variable {R M : Type*}

local notation3 "R≥0" => Nonneg R

section Ring

variable [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [AddCommGroup M] [Module R M]

lemma nonneg_smulSet_preimage_one_le_positive (f : M →ₗ[R] R) :
    R≥0 ∙ f ⁻¹' {1} ≤ f.positive := by
  intro x h hx0
  rw [mem_smulSet_of_ne_zero hx0] at h
  obtain ⟨y, hy, ⟨r, hr⟩, rfl⟩ := h
  rw [Set.mem_preimage, Set.mem_singleton_iff] at hy
  rw [Nonneg.mk_smul, map_smul, hy, smul_eq_mul, mul_one]
  by_cases hr0 : 0 = r
  · simp [← hr0] at hx0
  exact lt_of_le_of_ne hr hr0

end Ring

section DivisionRing

variable [DivisionRing R] [PartialOrder R] [IsStrictOrderedRing R]
variable [AddCommGroup M] [Module R M]

-- TODO: generalize to `c > 0` instead of 1?
lemma nonneg_smulSet_preimage_one_eq_positive (f : M →ₗ[R] R) :
    R≥0 ∙ (f ⁻¹' {1}) = f.positive := by
  apply le_antisymm
  · exact nonneg_smulSet_preimage_one_le_positive f
  intro x h
  by_cases hx0 : x = 0
  · simp [hx0]
  rw [mem_smulSet_of_ne_zero hx0]
  use (f x)⁻¹ • x
  specialize h hx0
  constructor
  · simp [inv_mul_cancel₀ h.ne.symm]
  · use ⟨_, h.le⟩
    simp [smul_smul, mul_inv_cancel₀ h.ne.symm]

end DivisionRing

end SubMulAction₀
