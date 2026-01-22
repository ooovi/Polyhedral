/-
Copyright (c) 2025 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/

-- PLAN: PR this together with `Submodule.dual_univ` to demonstrate usefulness

import Mathlib.LinearAlgebra.PerfectPairing.Basic

namespace LinearMap

open Module Function

section CommSemiring

variable {R : Type*} [CommSemiring R]
variable {M : Type*} [AddCommMonoid M] [Module R M]
variable {N : Type*} [AddCommMonoid N] [Module R N]

variable {p : M →ₗ[R] N →ₗ[R] R}

instance [Module.Projective R N] : Fact (.id : (N →ₗ[R] R) →ₗ[R] _).SeparatingRight :=
  ⟨fun _ hx => by simpa using (forall_dual_apply_eq_zero_iff R _).mp hx⟩

instance : Fact (.id : (N →ₗ[R] R) →ₗ[R] _).SeparatingLeft :=
  ⟨fun _ hx => by ext y; exact hx y⟩

instance [Module.Projective R M]  : Fact (Dual.eval R M).SeparatingLeft :=
  ⟨by simp [separatingLeft_iff_linear_nontrivial, eval_apply_eq_zero_iff]⟩

instance : Fact (Dual.eval R M).SeparatingRight :=
  ⟨by simp [Dual.eval, separatingLeft_iff_linear_nontrivial]⟩

-- instance [inst : Fact p.flip.SeparatingLeft] : Fact p.SeparatingRight :=
--     ⟨flip_separatingLeft.mp inst.elim⟩

-- instance [inst : Fact p.flip.SeparatingRight] : Fact p.SeparatingLeft :=
--     ⟨flip_separatingRight.mp inst.elim⟩

instance [inst : Fact p.SeparatingLeft] : Fact p.flip.SeparatingRight :=
  ⟨flip_separatingLeft.mp inst.elim⟩
instance [inst : Fact p.SeparatingRight] : Fact p.flip.SeparatingLeft :=
  ⟨flip_separatingRight.mp inst.elim⟩

instance [inst : Fact p.Nondegenerate] : Fact p.SeparatingLeft := ⟨inst.elim.1⟩
instance [inst : Fact p.Nondegenerate] : Fact p.SeparatingRight := ⟨inst.elim.2⟩

@[simp]
lemma SeparatingLeft.ker_eq_bot [inst : Fact p.SeparatingLeft] : ker p = ⊥ :=
  separatingLeft_iff_ker_eq_bot.mp inst.elim

instance [inst : Fact (Surjective p)] : Fact (Surjective p.flip.flip) := inst

instance [inst : Fact (Injective p)] : Fact (Injective p.flip.flip) := inst

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R]
variable {M : Type*} [AddCommGroup M] [Module R M] -- NOTE: AddCommMonoid suffices for some below
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}

-- ## PRIORITY!
instance [inst : p.IsPerfPair] : Fact p.Nondegenerate := ⟨sorry⟩

instance [inst : p.IsPerfPair] : Fact (Injective p) := ⟨inst.bijective_left.injective⟩
instance [inst : p.IsPerfPair] : Fact (Injective p.flip) := ⟨inst.bijective_right.injective⟩
instance [inst : p.flip.IsPerfPair] : Fact (Injective p) := ⟨inst.bijective_right.injective⟩
-- instance [inst : p.flip.IsPerfPair] : Fact (Injective p.flip) := inferInstance

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]

-- ## SEPARATING

variable [Fact p.SeparatingLeft] in
@[simp] lemma SeparatingLeft.injective : Injective p := LinearMap.ker_eq_bot.mp ker_eq_bot

variable [Fact p.SeparatingRight] in
lemma SeparatingRight.injective : Injective p.flip := by simp

end CommRing

section Field

variable {R : Type*} [Field R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}

instance instFactSurjectiveCoeIdId : Fact (Surjective (LinearMap.id (R := R) (M := M)))
  := ⟨surjective_id⟩
instance : Fact (Surjective (Dual.eval R M).flip)
  := instFactSurjectiveCoeIdId

instance [inst : p.IsPerfPair] : Fact (Surjective p) := ⟨inst.bijective_left.surjective⟩
instance [inst : p.IsPerfPair] : Fact (Surjective p.flip) := ⟨inst.bijective_right.surjective⟩

end Field

end LinearMap
