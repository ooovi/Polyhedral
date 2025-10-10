import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.FreeModule.Basic

open Function

variable {R E F : Type*}
variable [CommSemiring R] -- comm needed for duality
variable [AddCommMonoid E] [Module R E]
variable [AddCommMonoid F] [Module R F]
variable {p : E →ₗ[R] F →ₗ[R] R} -- bilinear pairing

-- TODO: generalize (maybe IntegralDomain and IsTorsionFree)

variable (R E) [Module.Free R E] in
/-- There exists an injection from a module to its dual space. -/
lemma Module.Dual.exists_embed : ∃ f : E →ₗ[R] Dual R E, Injective f := by
  classical
  obtain ⟨_, b⟩ := Free.exists_basis R E
  exact ⟨Basis.toDual b, Basis.toDual_injective _⟩
