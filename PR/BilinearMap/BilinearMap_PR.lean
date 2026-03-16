/-
Copyright (c) 2025 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/

import Mathlib.LinearAlgebra.PerfectPairing.Basic

namespace LinearMap

open Module

section CommSemiring

variable {R : Type*} [CommSemiring R]
variable {M : Type*} [AddCommMonoid M] [Module R M]
variable {N : Type*} [AddCommMonoid N] [Module R N]

variable {p : M →ₗ[R] N →ₗ[R] R}

/-- The identitiy pairing is left-separating. -/
theorem SeparatingLeft.id : (.id : (N →ₗ[R] R) →ₗ[R] _).SeparatingLeft :=
  fun _ hx => by ext y; exact hx y

/-- The identitiy pairing is right-separating. -/
theorem SeparatingRight.id [Module.Projective R N] :
    (.id : (N →ₗ[R] R) →ₗ[R] _).SeparatingRight :=
  fun _ hx => by simpa using (forall_dual_apply_eq_zero_iff R _).mp hx

/-- The identitiy pairing is non-degenerate. -/
theorem Nondegenerate.id [Module.Projective R N] :
    (.id : (N →ₗ[R] R) →ₗ[R] _).Nondegenerate := ⟨.id, .id⟩

instance : Fact (.id : (N →ₗ[R] R) →ₗ[R] _).SeparatingLeft := ⟨.id⟩

instance [Module.Projective R N] : Fact (.id : (N →ₗ[R] R) →ₗ[R] _).SeparatingRight := ⟨.id⟩

instance [Module.Projective R N] : Fact (.id : (N →ₗ[R] R) →ₗ[R] _).Nondegenerate := ⟨.id⟩

/-- The pairing `Dual.eval` is left-separating. -/
theorem SeparatingLeft.eval [Module.Projective R M] : (Dual.eval R M).SeparatingLeft := by
  simp [separatingLeft_iff_linear_nontrivial, eval_apply_eq_zero_iff]

/-- The pairing `Dual.eval` is right-separating. -/
theorem SeparatingRight.eval : (Dual.eval R M).SeparatingRight := by
  simp [Dual.eval, separatingLeft_iff_linear_nontrivial]

/-- The pairing `Dual.eval` is non-degenerate. -/
theorem Nondegenerate.eval [Module.Projective R M] : (Dual.eval R M).Nondegenerate := ⟨.eval, .eval⟩

instance [Module.Projective R M] : Fact (Dual.eval R M).SeparatingLeft := ⟨.eval⟩

instance : Fact (Dual.eval R M).SeparatingRight := ⟨.eval⟩

instance [Module.Projective R M] : Fact (Dual.eval R M).Nondegenerate := ⟨.eval⟩

instance [inst : Fact p.Nondegenerate] : Fact p.SeparatingLeft := ⟨inst.elim.1⟩

instance [inst : Fact p.Nondegenerate] : Fact p.SeparatingRight := ⟨inst.elim.2⟩

instance [inst : Fact p.SeparatingLeft] : Fact p.flip.SeparatingRight :=
  ⟨flip_separatingLeft.mp inst.elim⟩

instance [inst : Fact p.SeparatingRight] : Fact p.flip.SeparatingLeft :=
  ⟨flip_separatingRight.mp inst.elim⟩

/-- A bilinear map is left-separating if and only if it has a trivial kernel. -/
@[simp]
theorem SeparatingLeft.iff_ker_eq_bot {B : M →ₗ[R] N →ₗ[R] R} :
    B.SeparatingLeft ↔ LinearMap.ker B = ⊥ :=
  Iff.trans separatingLeft_iff_linear_nontrivial LinearMap.ker_eq_bot'.symm

/-- If a bilinear map is left-separating then it has a trivial kernel. -/
@[simp]
lemma SeparatingLeft.ker_eq_bot [inst : Fact p.SeparatingLeft] : ker p = ⊥ := by
  simpa [iff_ker_eq_bot] using inst.elim

/-- If a bilinear map is left-separating then it has a trivial kernel. -/
@[simp]
lemma SeparatingLeft.ker_eq_bot' [inst : Fact p.SeparatingLeft] : ker p = ⊥ :=
  separatingLeft_iff_ker_eq_bot.mp inst.elim

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
