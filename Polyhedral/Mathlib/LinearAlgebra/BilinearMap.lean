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
variable {p : M →ₗ[R] N →ₗ[R] R}

-- variable (p) in
-- lemma exists_restricted_pairing (S : Submodule R M) :
--     ∃ T : Submodule R N, ∃ q : S →ₗ[R] T →ₗ[R] R, ∀ s : S, ∀ t : T, q s t = p s t := by
--   sorry

end CommSemiring

section CommSemiring

variable {R : Type*} [CommSemiring R]
variable {M : Type*} [AddCommMonoid M] [Module R M]
variable {N : Type*} [AddCommMonoid N] [Module R N]

/- For a field this is known as being 'formally real'. This is equivalent to the existence of an
  ordered field structure. This could be relevant on field with no preferred order, e.g. the
  field of rational functions -/
def IsFaithfulPair (p : M →ₗ[R] N →ₗ[R] R)
    := ∃ g : N →ₗ[R] M, ∀ x : N, (p ∘ₗ g) x x = 0 → x = 0

/- Equivalenty: p is faithful iff there is an embedding of N in M on which p is injective.
  In prticular, N is smaller than M. So Dual.evel is not faithful for infinite spaces, while
  .id is always faithful.
  This is intentionally weaker than a perfect pairing. In this way one direction of the standard
  duality map can still be faithful, even in infinite dimensions.
-/

variable (p : M →ₗ[R] N →ₗ[R] R)

instance [inst : Fact p.IsFaithfulPair] : Fact p.flip.flip.IsFaithfulPair
    := by rw [flip_flip]; exact inst

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]

lemma isFaithfulPair_of_toDual {ι : Type*} [DecidableEq ι] (b : Basis ι R M) :
    b.toDual.IsFaithfulPair := ⟨.id, fun _ => Dual.toDual_eq_zero⟩

variable (p : M →ₗ[R] N →ₗ[R] R)

-- Q : True?
lemma isPerfPair_of_isFaithfulPair_both (hp : p.IsFaithfulPair) (hp' : p.flip.IsFaithfulPair) :
    p.IsPerfPair := by
  sorry

end CommRing

section Field

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}

lemma isFaithfulPair_of_range_top (hp : range p = ⊤)
    : p.IsFaithfulPair := by classical
  obtain ⟨_, b⟩ := Free.exists_basis R N
  obtain ⟨p', hp'⟩ := LinearMap.exists_rightInverse_of_surjective p hp -- needs [Field R]
  use p' ∘ₗ b.toDual
  simp [← LinearMap.comp_assoc, hp']

lemma isFaithfulPair_of_surjective (hp : Surjective p) : p.IsFaithfulPair
  := isFaithfulPair_of_range_top <| range_eq_top_of_surjective p hp

lemma isFaithfulPair_of_id : IsFaithfulPair (R := R) (N := M) .id
  := isFaithfulPair_of_range_top range_id

instance : Fact (IsFaithfulPair (R := R) (N := M) .id) := ⟨isFaithfulPair_of_id⟩
instance : Fact (Dual.eval R M).flip.IsFaithfulPair := ⟨isFaithfulPair_of_id⟩

lemma isFaithfulPair_of_isPerfPair [p.IsPerfPair] : p.IsFaithfulPair :=
    isFaithfulPair_of_surjective (IsPerfPair.bijective_left p).surjective

instance [p.IsPerfPair] : Fact p.IsFaithfulPair := ⟨isFaithfulPair_of_isPerfPair⟩

section IsReflexive

variable [IsReflexive R M]

lemma isFaithfulPair_of_eval : IsFaithfulPair (Dual.eval R M)
  := isFaithfulPair_of_surjective (bijective_dual_eval R M).surjective

instance : Fact (Dual.eval R M).IsFaithfulPair := ⟨isFaithfulPair_of_eval⟩

end IsReflexive

section Module.Finite

-- instance [Module.Finite R M] [Fact p.IsFaithfulPair] : Module.Finite R N := by
--   sorry

-- instance [Module.Finite R M] [Fact p.IsFaithfulPair] : p.flip.IsFaithfulPair := by
--   sorry

end Module.Finite

end Field

end LinearMap
