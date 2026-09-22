/-
Copyright (c) 2025 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/
module

public import Mathlib.LinearAlgebra.PerfectPairing.Basic

/-! This file provides instances for expressing that bilinear pairings are separating and
nondegenarate. This is needed in duality theory since many lemmas depend on these properties
of the pairing. -/

public section

open Module Function

namespace LinearMap

section CommSemiring

variable {R : Type*} [CommSemiring R]
variable {M : Type*} [AddCommMonoid M] [Module R M]
variable {N : Type*} [AddCommMonoid N] [Module R N]

variable {p : M →ₗ[R] N →ₗ[R] R}

lemma SeparatingLeft.of_injective (hp : Injective p) : p.SeparatingLeft := by
  simpa [separatingLeft_iff_ker_eq_bot] using ker_eq_bot_of_injective hp

instance [inst : Fact (Injective p)] : Fact p.SeparatingLeft :=
  ⟨SeparatingLeft.of_injective inst.elim⟩

variable [Module.Projective R N] in
instance : Fact (SeparatingRight (M₁ := N →ₗ[R] R) .id) :=
  ⟨fun x hx => by simpa using (forall_dual_apply_eq_zero_iff R x).mp hx⟩

variable [Module.Projective R M] in
instance : Fact (Dual.eval R M).SeparatingLeft :=
  ⟨by simp [separatingLeft_iff_linear_nontrivial, eval_apply_eq_zero_iff]⟩

instance : Fact (SeparatingLeft (M₁ := N →ₗ[R] R) .id) :=
  ⟨fun x hx => by ext y; exact hx y⟩

instance : Fact (Dual.eval R M).SeparatingRight :=
  ⟨by simp [Dual.eval, separatingLeft_iff_linear_nontrivial]⟩

instance instFactSurjectiveCoeIdId : Fact (Surjective (.id : M →ₗ[R] M)) :=
  ⟨surjective_id⟩

instance : Fact (Surjective (Dual.eval R M).flip) := instFactSurjectiveCoeIdId

variable [Module.Projective R N] in
lemma SeparatingRight.of_surjective (hp : Surjective p) : p.SeparatingRight := by
  intro x hx
  apply (Fact.elim (inferInstance : Fact (Dual.eval R N).SeparatingLeft)) x
  intro f
  obtain ⟨y, hy⟩ := hp f
  rw [← hy]
  exact hx y

instance [Module.Projective R N] [inst : Fact (Surjective p)] : Fact p.SeparatingRight :=
  ⟨SeparatingRight.of_surjective inst.elim⟩

variable [Module.Projective R M] in
lemma SeparatingLeft.of_surjective_flip (hp : Surjective p.flip) : p.SeparatingLeft :=
  flip_separatingRight.mp <| SeparatingRight.of_surjective hp

variable [Module.Projective R M] in
instance [inst : Fact (Surjective p.flip)] : Fact p.SeparatingLeft :=
  ⟨SeparatingLeft.of_surjective_flip inst.elim⟩

instance [inst : Fact p.SeparatingLeft] : Fact p.flip.SeparatingRight :=
    ⟨flip_separatingLeft.mp inst.elim⟩
instance [inst : Fact p.SeparatingRight] : Fact p.flip.SeparatingLeft :=
    ⟨flip_separatingRight.mp inst.elim⟩

instance [inst : Fact p.Nondegenerate] : Fact p.SeparatingLeft := ⟨inst.elim.1⟩
instance [inst : Fact p.Nondegenerate] : Fact p.SeparatingRight := ⟨inst.elim.2⟩

variable [inst : Fact p.SeparatingLeft] in
@[simp] lemma SeparatingLeft.ker_eq_bot : ker p = ⊥ :=
  separatingLeft_iff_ker_eq_bot.mp inst.elim

instance [inst : Fact (Surjective p)] : Fact (Surjective p.flip.flip) := inst

instance [inst : Fact (Injective p)] : Fact (Injective p.flip.flip) := inst

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R]

section SeparatingRight

variable {M : Type*} [AddCommMonoid M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}

variable [fact : Fact p.SeparatingRight] in
lemma SeparatingRight.injective : Injective p.flip := by
  intro x y hxy
  rw [← sub_eq_zero]
  refine fact.elim (x - y) fun z => ?_
  simpa [flip_apply, sub_eq_zero] using congrArg (· z) hxy

instance [Fact p.SeparatingRight] : Fact (Injective p.flip) :=
  ⟨SeparatingRight.injective⟩

end SeparatingRight

section IsPerfPair

variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}

instance [inst : p.IsPerfPair] : Fact p.Nondegenerate :=
  ⟨SeparatingLeft.of_injective inst.bijective_left.injective,
    flip_separatingLeft.mp <| SeparatingLeft.of_injective inst.bijective_right.injective⟩

instance [inst : p.IsPerfPair] : Fact (Injective p) := ⟨inst.bijective_left.injective⟩

instance [inst : p.IsPerfPair] : Fact (Surjective p) := ⟨inst.bijective_left.surjective⟩

end IsPerfPair

end CommRing

end LinearMap
