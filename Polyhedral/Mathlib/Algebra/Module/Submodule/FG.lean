/-
Copyright (c) 2025 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/

import Mathlib.RingTheory.Noetherian.Basic

import Polyhedral.Mathlib.Algebra.Module.Submodule.Basic

namespace Submodule

section CommSemiring

variable {R M N : Type*}
variable [Ring R]
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]
-- variable {p : M →ₗ[R] N →ₗ[R] R}

section IsNoetherianRing

variable [IsNoetherianRing R]

lemma inf_fg_right (S : Submodule R M) {T : Submodule R M} (hT : T.FG) : (S ⊓ T).FG := by
  have := isNoetherian_of_fg_of_noetherian _ hT
  exact fg_of_restrict_le inf_le_right <| IsNoetherian.noetherian <| restrict T (S ⊓ T)

lemma inf_fg_left {S : Submodule R M} (hS : S.FG) (T : Submodule R M) : (S ⊓ T).FG := by
  rw [inf_comm]; exact inf_fg_right T hS

end IsNoetherianRing

end CommSemiring

end Submodule
