/-
Copyright (c) 2026 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/
module

public import Mathlib.Algebra.Module.Submodule.Map

/-! This file contains additional results about maps and comaps of submodules. -/

public section

open Function

namespace Submodule

variable {R M N : Type*}
variable [Ring R]
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]

-- This proof is AI generated
/-- Comap along a surjective linear map preserves binary suprema. -/
theorem comap_sup_eq (f : M →ₗ[R] N) (S T : Submodule R N) (hf : Surjective f) :
    comap f S ⊔ comap f T = comap f (S ⊔ T) := by
  apply le_antisymm
  · exact sup_le (comap_mono le_sup_left) (comap_mono le_sup_right)
  · intro x hx
    rw [mem_comap, ← map_sup_comap_of_surjective hf S T] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    have hker : x - y ∈ comap f S := by
      rw [mem_comap]
      simp [hxy]
    have hker' : x - y ∈ comap f S ⊔ comap f T :=
      (show comap f S ≤ comap f S ⊔ comap f T from le_sup_left) hker
    simpa [add_comm] using add_mem hy hker'

end Submodule
