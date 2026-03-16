/-
Copyright (c) 2025 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/

import Mathlib.LinearAlgebra.PerfectPairing.Basic

namespace LinearMap

open Module

section CommSemiring

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
variable {R₁ M₁ : Type*} [CommSemiring R₁] [AddCommMonoid M₁] [Module R₁ M₁]
variable {R₂ M₂ : Type*} [CommSemiring R₂] [AddCommMonoid M₂] [Module R₂ M₂]
variable {I₁ : R₁ →+* R} {I₂ : R₂ →+* R}
variable {p : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] M}

/-- If a bilinear map is left-separating then it has a trivial kernel. -/
@[simp]
theorem SeparatingLeft.ker_eq_bot [inst : Fact p.SeparatingLeft] : ker p = ⊥ := by
  simpa [separatingLeft_iff_ker_eq_bot] using inst.elim

instance [inst : Fact p.Nondegenerate] : Fact p.SeparatingLeft := ⟨inst.elim.1⟩

instance [inst : Fact p.Nondegenerate] : Fact p.SeparatingRight := ⟨inst.elim.2⟩

instance [inst : Fact p.SeparatingLeft] : Fact p.flip.SeparatingRight :=
  ⟨flip_separatingLeft.mp inst.elim⟩

instance [inst : Fact p.SeparatingRight] : Fact p.flip.SeparatingLeft :=
  ⟨flip_separatingRight.mp inst.elim⟩

/-- The identitiy pairing is left-separating. -/
theorem SeparatingLeft.id : (.id : (M₁ →ₛₗ[I₁] M) →ₗ[R] _).SeparatingLeft :=
  fun _ hx => by ext y; exact hx y

/-- The identitiy pairing is right-separating. -/
theorem SeparatingRight.id [Module.Projective R M] : (.id : (M →ₗ[R] R) →ₗ[R] _).SeparatingRight :=
  -- by
  -- unfold SeparatingRight
  -- simp
  -- -- intro y h
  -- -- specialize h .id
  -- sorry
  fun _ hx => by simpa using (forall_dual_apply_eq_zero_iff R _).mp hx

/-- The identitiy pairing is non-degenerate. -/
theorem Nondegenerate.id [Module.Projective R M] :
    (.id : (M →ₗ[R] R) →ₗ[R] _).Nondegenerate := ⟨.id, .id⟩

instance : Fact (.id : (M₂ →ₛₗ[I₂] M) →ₗ[R] _).SeparatingLeft := ⟨.id⟩

instance [Module.Projective R M] : Fact (.id : (M →ₗ[R] R) →ₗ[R] _).SeparatingRight := ⟨.id⟩

instance [Module.Projective R M] : Fact (.id : (M →ₗ[R] R) →ₗ[R] _).Nondegenerate := ⟨.id⟩

/-- The pairing `Dual.eval` is left-separating. -/
theorem SeparatingLeft.eval [Module.Projective R M] : (Dual.eval R M).SeparatingLeft := by
  simp only [Dual.eval, flip_separatingLeft, SeparatingRight.id]

/-- The pairing `Dual.eval` is right-separating. -/
theorem SeparatingRight.eval : (Dual.eval R M).SeparatingRight := by
  simp only [Dual.eval, flip_separatingRight, SeparatingLeft.id]

/-- The pairing `Dual.eval` is non-degenerate. -/
theorem Nondegenerate.eval [Module.Projective R M] : (Dual.eval R M).Nondegenerate :=
  ⟨.eval, .eval⟩

instance [Module.Projective R M] : Fact (Dual.eval R M).SeparatingLeft := ⟨.eval⟩

instance : Fact (Dual.eval R M).SeparatingRight := ⟨.eval⟩

instance [Module.Projective R M] : Fact (Dual.eval R M).Nondegenerate := ⟨.eval⟩

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}

/-- A perfect pairing is non-degenerate. -/
theorem IsPerfPair.nondegenerate (hp : p.IsPerfPair) : p.Nondegenerate := by
  simpa only [Nondegenerate, ← flip_separatingLeft, separatingLeft_iff_ker_eq_bot, ker_eq_bot]
    using ⟨hp.bijective_left.injective, hp.bijective_right.injective⟩

instance [inst : p.IsPerfPair] : Fact p.Nondegenerate := ⟨inst.nondegenerate⟩

end CommRing

end LinearMap
