/-
Copyright (c) 2025 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/

import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Polyhedral.Mathlib.LinearAlgebra.Dual.Basis

open Module Function

namespace LinearMap

section CommSemiring

variable {R : Type*} [CommSemiring R]
variable {M : Type*} [AddCommMonoid M] [Module R M]
variable {N : Type*} [AddCommMonoid N] [Module R N]

/- For a field this is known as being 'formally real'. This is equivalent to the existence of an
  ordered field structure. This could ve relevant on field with no preferred order, e.g. the
  field of rational functions -/
def IsFaithfulPair (p : M →ₗ[R] N →ₗ[R] R)
    := ∃ g : N →ₗ[R] M, ∀ x : N, (p ∘ₗ g) x x = 0 → x = 0

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable (p : M →ₗ[R] N →ₗ[R] R)

lemma isFaithfulPair_of_toDual {ι : Type*} [DecidableEq ι] (b : Basis ι R M) :
    b.toDual.IsFaithfulPair := ⟨.id, fun _ => Dual.toDual_eq_zero⟩

end CommRing

section Field

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable (p : M →ₗ[R] N →ₗ[R] R)

lemma isFaithfulPair_of_surjective (hp : range p = ⊤) -- (hp : Surjective p)
    : p.IsFaithfulPair := by classical
  obtain ⟨_, b⟩ := Free.exists_basis R N
  obtain ⟨p', hp'⟩ := LinearMap.exists_rightInverse_of_surjective p hp -- needs [Field R]
  use p' ∘ₗ b.toDual
  simp [← LinearMap.comp_assoc, hp']

lemma isFaithfulPair_of_id : IsFaithfulPair (R := R) (N := M) .id
  := isFaithfulPair_of_surjective _ range_id

instance : Fact (IsFaithfulPair (R := R) (N := M) .id) := ⟨isFaithfulPair_of_id⟩

variable [Module.Finite R M] in
lemma isFaithfulPair_of_eval : IsFaithfulPair (Dual.eval R M)
  := sorry

variable [Module.Finite R M] in
instance : Fact (Dual.eval R M).IsFaithfulPair := ⟨isFaithfulPair_of_eval⟩

lemma isFaithfulPair_of_isPerfPair [p.IsPerfPair] : p.IsFaithfulPair := sorry

instance [p.IsPerfPair] : Fact p.IsFaithfulPair := ⟨isFaithfulPair_of_isPerfPair p⟩

end Field

end LinearMap
