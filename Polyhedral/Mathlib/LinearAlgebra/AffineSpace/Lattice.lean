/-
Copyright (c) 2026 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
public import Polyhedral.Mathlib.Data.SetLike.IsConcrete

import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! This file proves results about the lattice structure on affine subspaces. -/

public section

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
