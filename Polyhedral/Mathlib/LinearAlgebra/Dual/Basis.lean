import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.Algebra.Ring.SumsOfSquares
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

open Module Function

variable {ι : Type*} [DecidableEq ι]

section CommSemiring

variable {R M : Type*}
variable [CommSemiring R]
variable [AddCommMonoid M] [Module R M]

-- provided by Ruben Van de Velde
-- https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/.60Basis.2EtoDual.60.20positive.20and.20non-degenerate/near/544334164
lemma Module.Dual.toDual_isSumSq (b : Module.Basis ι R M) (x : M) :
    IsSumSq (b.toDual x x) := by
  rw [← b.linearCombination_repr x]
  simp [Finsupp.linearCombination_apply, Module.Basis.toDual_apply, Finsupp.sum]

variable {N : Type*}
variable [AddCommMonoid N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R} -- bilinear pairing

-- TODO: generalize (maybe IntegralDomain and IsTorsionFree)
variable (R M) [Module.Free R M] in
/-- There exists an injection from a module to its dual space. -/
lemma Module.Dual.exists_embed : ∃ f : M →ₗ[R] Dual R M, Injective f := by
  classical
  obtain ⟨_, b⟩ := Free.exists_basis R M
  exact ⟨Basis.toDual b, Basis.toDual_injective _⟩

end CommSemiring

section IsStrictOrderedRing

variable {R M : Type*}
variable [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
variable [AddCommMonoid M] [Module R M]

lemma Module.Dual.toDual_nonneg (b : Basis ι R M) (x : M) :
    0 ≤ Basis.toDual b x x := IsSumSq.nonneg (toDual_isSumSq b x)

@[simp]
lemma Module.Dual.toDual_eq_zero_iff_zero {b : Basis ι R M} {x : M} :
    Basis.toDual b x x = 0 ↔ x = 0 := by
  rw [← b.linearCombination_repr x]
  constructor <;>
  simp +contextual [Finsupp.linearCombination_apply, Finsupp.sum, Basis.toDual_apply,
      Finset.sum_mul_self_eq_zero_iff]

end IsStrictOrderedRing
