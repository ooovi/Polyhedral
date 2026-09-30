/-
Copyright (c) 2026 Vlad Tsyrklevich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vlad Tsyrklevich
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.Dimension
public import Polyhedral.Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs

/-! Dimension lemmas -/

@[expose] public section

namespace AffineSubspace

variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]

@[simp]
theorem dim_toAffineSubspace (s : Submodule R V) : s.toAffineSubspace.dim = Module.rank R s := by
  rw [dim_eq_rank (toAffineSubspace_ne_bot _), Submodule.toAffineSubspace_direction]

@[simp]
theorem finDim_toAffineSubspace (s : Submodule R V) :
    s.toAffineSubspace.finDim = Module.finrank R s := by
  rw [finDim_eq_finrank (toAffineSubspace_ne_bot _), Submodule.toAffineSubspace_direction]

end AffineSubspace
