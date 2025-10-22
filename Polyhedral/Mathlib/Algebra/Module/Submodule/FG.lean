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

variable {R M : Type*}
variable [Semiring R]
variable [AddCommMonoid M] [Module R M]

alias sup_fg := Submodule.FG.sup

lemma embed_fg_of_fg (S : Submodule R M) {T : Submodule R S} (hC : T.FG) :
    (embed S T).FG := Submodule.FG.map _ hC

lemma fg_of_embed_fg {S : Submodule R M} {T : Submodule R S} (hT : (embed S T).FG) : T.FG
    := fg_of_fg_map_injective _ (injective_subtype (S : Submodule R M)) hT

@[simp] lemma embed_fg_iff_fg {S : Submodule R M} {T : Submodule R S} : (embed S T).FG ↔ T.FG
  := ⟨fg_of_embed_fg, embed_fg_of_fg S⟩

lemma restrict_fg_of_fg_le {S T : Submodule R M} (hST : T ≤ S) (hT : T.FG) :
    (restrict S T).FG := by
  rw [← (inf_eq_left.mpr hST), inf_comm, ← embed_restrict] at hT
  exact fg_of_embed_fg hT

lemma fg_of_restrict_le {S T : Submodule R M} (hST : T ≤ S) (hC : (restrict S T).FG) :
    T.FG := by
  rw [← (inf_eq_left.mpr hST), inf_comm, ← embed_restrict]
  exact embed_fg_of_fg S hC

@[simp] lemma fg_iff_restrict_le {S T : Submodule R M} (hST : T ≤ S) :
    (restrict S T).FG ↔ T.FG := ⟨fg_of_restrict_le hST, restrict_fg_of_fg_le hST⟩

lemma restrict_fg_iff_inf_fg {S T : Submodule R M} :
    (restrict S T).FG ↔ (S ⊓ T : Submodule R M).FG := by
  rw [← embed_restrict, embed_fg_iff_fg]

section RestrictScalars

variable {S : Type*}
variable [Semiring S] [Module S R]
variable [Module S M] [IsScalarTower S R M]

variable (S) in
lemma restrictedScalars_fg_of_fg [Module.Finite S R] {s : Submodule R M} (hs : s.FG) :
    (s.restrictScalars S).FG := by
  rw [← Module.Finite.iff_fg] at *
  exact Module.Finite.trans R s

-- Q: Is there a simpler proof for this?
lemma fg_of_restrictedScalars_fg [Module.Finite S R] {s : Submodule R M}
    (hs : (s.restrictScalars S).FG) : s.FG := by
  obtain ⟨g, hg⟩ := hs
  use g
  rw [← SetLike.coe_set_eq, coe_restrictScalars] at hg
  have hg := congrArg (span R) hg
  rw [Submodule.span_span_of_tower] at hg
  simp [hg] -- span_eq

lemma restrictedScalars_fg_iff_fg [Module.Finite S R] {s : Submodule R M} :
    (s.restrictScalars S).FG ↔ s.FG := ⟨fg_of_restrictedScalars_fg, restrictedScalars_fg_of_fg S⟩

variable (R) in
lemma span_scalars_FG [Module.Finite S R] {s : Submodule S M} (hfg : s.FG) :
    (span R (M := M) s).FG := by
  obtain ⟨t, ht⟩ := hfg
  use t; rw [← ht, Submodule.span_span_of_tower]

end RestrictScalars

section IsNoetherianRing

variable {R M N : Type*}
variable [Ring R] [IsNoetherianRing R]
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]

/-- The intersection of a submodule with an FG submodule is FG. -/
lemma inf_fg_right (S : Submodule R M) {T : Submodule R M} (hT : T.FG) : (S ⊓ T).FG := by
  have := isNoetherian_of_fg_of_noetherian _ hT
  exact fg_of_restrict_le inf_le_right <| IsNoetherian.noetherian <| restrict T (S ⊓ T)

/-- The intersection of a submodule with an FG submodule is FG. -/
lemma inf_fg_left {S : Submodule R M} (hS : S.FG) (T : Submodule R M) : (S ⊓ T).FG := by
  rw [inf_comm]; exact inf_fg_right T hS

/-- The restriction of an FG submodule to an arbitrary submodule is FG. -/
lemma restrict_fg (S : Submodule R M) {T : Submodule R M} (hT : T.FG) : (restrict S T).FG := by
  rw [restrict_fg_iff_inf_fg]; exact inf_fg_right S hT

end IsNoetherianRing

end Submodule
