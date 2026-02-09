/-
Copyright (c) 2025 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Noetherian.Basic

import Polyhedral.Mathlib.Algebra.Module.Submodule.Basic

open Module

namespace Submodule

variable {R M N : Type*}
variable [Semiring R]
variable [AddCommMonoid M] [Module R M]
variable [AddCommMonoid N] [Module R N]

alias sup_fg := Submodule.FG.sup

#check Submodule.fg_of_linearEquiv

-- This seems to be the more appropriate version of `Submodule.fg_of_linearEquiv` which
-- is probably better called `Module.fg_of_linearEquiv` or so.
lemma FG.linearEquiv {S : Submodule R M} {T : Submodule R N} (e : S ≃ₗ[R] T) (hS : S.FG) :
    T.FG := by -- T.fg_top.mp <| fg_of_linearEquiv e.symm (S.fg_top.mpr hS)
  rw [← Submodule.fg_top] at *
  exact fg_of_linearEquiv e.symm hS

-- ## RESTRICT / EMBED

lemma embed_fg_of_fg {S : Submodule R M} {T : Submodule R S} (hC : T.FG) :
    (embed T).FG := Submodule.FG.map _ hC

lemma fg_of_embed_fg {S : Submodule R M} {T : Submodule R S} (hT : (embed T).FG) : T.FG
    := fg_of_fg_map_injective _ (injective_subtype (S : Submodule R M)) hT

@[simp] lemma embed_fg_iff_fg {S : Submodule R M} {T : Submodule R S} : (embed T).FG ↔ T.FG
  := ⟨fg_of_embed_fg, embed_fg_of_fg⟩

lemma restrict_fg_of_fg_le {S T : Submodule R M} (hST : T ≤ S) (hT : T.FG) :
    (restrict S T).FG := by
  rw [← (inf_eq_left.mpr hST), inf_comm, ← embed_restrict] at hT
  exact fg_of_embed_fg hT

lemma fg_of_restrict_le {S T : Submodule R M} (hST : T ≤ S) (hC : (restrict S T).FG) :
    T.FG := by
  rw [← (inf_eq_left.mpr hST), inf_comm, ← embed_restrict]
  exact embed_fg_of_fg hC

@[simp] lemma fg_iff_restrict_le {S T : Submodule R M} (hST : T ≤ S) :
    (restrict S T).FG ↔ T.FG := ⟨fg_of_restrict_le hST, restrict_fg_of_fg_le hST⟩

lemma restrict_fg_iff_inf_fg {S T : Submodule R M} :
    (restrict S T).FG ↔ (S ⊓ T : Submodule R M).FG := by
  rw [← embed_restrict, embed_fg_iff_fg]

section IsNoetherianRing

variable {R M N : Type*}
variable [Ring R] [IsNoetherianRing R]
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]

/-- The restriction of an FG submodule to an arbitrary submodule is FG. -/
lemma restrict_fg (S : Submodule R M) {T : Submodule R M} (hT : T.FG) : (restrict S T).FG := by
  rw [restrict_fg_iff_inf_fg]; exact FG.of_le hT inf_le_right

end IsNoetherianRing

end Submodule
