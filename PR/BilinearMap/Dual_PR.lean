/-
Copyright (c) 2025 Martin Winter, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter, Yaël Dillies
-/
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Pi

import Polyhedral.PR.Dual.Dual_PR
-- import Polyhedral.PR.BilinearMap.BilinearMap_PR_2
import Polyhedral.PR.BilinearMap.BilinearMap_PR_withSurjInj

assert_not_exists TopologicalSpace Real -- Cardinal (comes with BilinearMap)

open Module Function LinearMap Pointwise Set OrderDual

namespace Submodule

variable {R M N : Type*}
  [CommSemiring R]
  [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]
  {p : M →ₗ[R] N →ₗ[R] R} {s t : Set M} {y : N}

variable [Fact p.SeparatingRight] in
@[simp] lemma dual_univ : dual p univ = ⊥ := by simp [dual_univ_ker]

end Submodule
