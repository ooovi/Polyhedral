/-
Copyright (c) 2026 Olivia Röhrig, Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Olivia Röhrig, Martin Winter
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.Homogenization

/-! This file defines affine homogenization axiomatically and proves every object fulfilling the
axioms is linearly equivalent to `Homogenization`, the canonical homogenization from Mathlib.

## Implementation notes
* The axiomatization in the literature is redundant. The universal property can be proven solely
from the subset of axioms used in `IsHomogenization`, as is done in lemma `extend`. It is
convenient to use the linear equivalence between any homogenization and `Homogenization`
for the proof.

## References

* [J. Gallier, *Geometric Methods and Applications for Computer Science and
  Engineering*][Gallier2011GeometricMethods]
 -/

public noncomputable section

namespace Homogenization

open Function Homogenization

variable {R : Type*} [Ring R]
variable {V : Type*} [AddCommGroup V] [Module R V]
variable {A : Type*} [AddTorsor V A]
variable {W : Type*} [AddCommGroup W] [Module R W]

variable {f : A →ᵃ[R] W} {g : W →ₗ[R] R}

lemma comp_lift_eq_weight_of_range_preimage (f_range : Set.range f = g ⁻¹' {1}) :
    g ∘ₗ (lift f) = weight := by
  refine hom_ext (fun p ↦ ?_)
  have := f_range ▸ Set.mem_range_self p
  simpa [LinearMap.comp_apply, lift_apply_ofPoint, weight_ofPoint] using this

lemma lift_bijective_of_injective_of_range_preimage (f_inj : Injective f)
    (f_range : Set.range f = g ⁻¹' {1}) : Bijective (lift f) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro a ha
    have : weight a = 0 := by simp [← comp_lift_eq_weight_of_range_preimage f_range, ha]
    obtain ⟨_, rfl⟩ := weight_eq_zero_iff.mp this
    rw [lift_apply_ofVector] at ha
    simp [(map_eq_zero_iff _ (f.linear_injective_iff.mpr f_inj)).mp ha]
  · intro w
    obtain p₀ := Classical.arbitrary A
    obtain ⟨a, ha⟩ : w - g w • f p₀ + f p₀ ∈ Set.range f := by
      have hmem := f_range ▸ Set.mem_range_self p₀
      have : g (w - g w • f p₀ + f p₀) = 1 := by
        rw [map_add, map_sub, map_smul, hmem, smul_eq_mul, mul_one, sub_self, zero_add]
      rw [f_range]; simpa using this
    exact ⟨ofVector (a -ᵥ p₀) + g w • ofPoint p₀, by simp [ha]⟩

end Homogenization
