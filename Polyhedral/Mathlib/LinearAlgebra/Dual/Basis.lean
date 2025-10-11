import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.Algebra.Ring.SumsOfSquares

open Function

variable {R M N : Type*}
variable [CommSemiring R] -- comm needed for duality
variable [AddCommMonoid M] [Module R M]
variable [AddCommMonoid N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R} -- bilinear pairing

-- TODO: generalize (maybe IntegralDomain and IsTorsionFree)

variable (R M) [Module.Free R M] in
/-- There exists an injection from a module to its dual space. -/
lemma Module.Dual.exists_embed : ∃ f : M →ₗ[R] Dual R M, Injective f := by
  classical
  obtain ⟨_, b⟩ := Free.exists_basis R M
  exact ⟨Basis.toDual b, Basis.toDual_injective _⟩

section IsOrderedRing

variable {R M N : Type*}
variable [CommSemiring R] [PartialOrder R] [IsOrderedRing R] -- comm needed for duality
variable [AddCommMonoid M] [Module R M]
variable [AddCommMonoid N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R} -- bilinear pairing
variable {ι : Type*} [DecidableEq ι]

lemma Module.Dual.toDual_isSumSq (b : Basis ι R M) (x : M) :
    IsSumSq (Basis.toDual b x x) := by
  sorry

lemma Module.Dual.toDual_pos (b : Basis ι R M) (x : M) :
    Basis.toDual b x x ≥ 0 := by
  --have h := Module.Basis.sum_repr b x
  sorry

@[simp]
lemma Module.Dual.toDual_eq_zero_iff {b : Basis ι R M} {x : M} :
    Basis.toDual b x x = 0 ↔ x = 0 := by
  sorry

end IsOrderedRing
