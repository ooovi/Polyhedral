/-
Copyright (c) 2025 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Noetherian.Basic

import Polyhedral.Mathlib.Algebra.Module.Submodule.Basic

open Module

section Submodule

open Function

variable {S R M : Type*} [Semiring S] [Semiring R] [Module S R]
    [AddCommMonoid M] [Module S M] [SMul R M] [IsScalarTower S R M]

variable (S R M) in
structure ExtSubmodule (S R M : Type*) [Semiring S] [Semiring R] [Module S R] [AddCommMonoid M]
    [Module S M] [SMul R M] [IsScalarTower S R M] extends AddSubmonoid M, SubMulAction R M

instance : HasQuotient M (ExtSubmodule S R M) := sorry

end Submodule

namespace Submodule

variable {R M N : Type*}
variable [Ring R]
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]

/-
 * I want that for `S : Submodule R M` and `T : Submodule R S` I can write `S ⧸ T` and
   get a submodule of `M ⧸ S`
-/

instance {S : Submodule R M} : CoeOut (Submodule R S) (Submodule R M) := ⟨embed⟩

-- instance {S : Submodule R M} : CoeOut (M / S)

-- def quot (S : Submodule R M) (T : Submodule R S) : Submodule R (M ⧸ (T : Submodule R M)) :=
--   map (T : Submodule R M).mkQ S

instance {S : Submodule R M} : HasQuotient M (Submodule R S) where
  quotient' T := quot S T

instance {S : Submodule R M} : HasQuotient S (Submodule R S) where
  quotient' T := quot S T

example (S : Submodule R M) (T : Submodule R S) : S ⧸ T := sorry

-- def isoTheorem (S : Submodule R M) (T : Submodule R S) :
--     (M ⧸ (T : Submodule R M)) ⧸ (S.quot T) ≃ₗ[R] M ⧸ S := sorry

end Submodule
