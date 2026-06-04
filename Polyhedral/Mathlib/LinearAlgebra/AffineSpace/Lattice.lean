import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

import Polyhedral.Mathlib.Data.SetLike.IsConcrete

namespace Affine

section Semiring

variable {R : Type*} [Ring R]
variable {V : Type*} [AddCommGroup V] [Module R V]
variable {A : Type*} [AddTorsor V A]

namespace AffineSubspace

instance : Singleton A (AffineSubspace R A) where
  singleton x := ⟨{x}, fun _ _ _ _ h₁ h₂ h₃ => by rw [h₁, h₂, h₃]; simp⟩

instance : IsConcreteSingleton (AffineSubspace R A) A := ⟨fun _ => rfl⟩

end AffineSubspace

end Semiring

end Affine
