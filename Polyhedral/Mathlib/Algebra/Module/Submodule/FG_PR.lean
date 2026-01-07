/-
Copyright (c) 2025 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Noetherian.Basic

open Module

namespace Submodule

section RestrictScalars

variable {R S M N : Type*}
variable [Semiring R]
variable [Semiring S] [Module S R]
variable [AddCommMonoid M] [Module R M] [Module S M] [IsScalarTower S R M]

variable (S) in
/-- If a ring `R` is finite over a subring `S` then restricting the scalars of an FG `R`-submodule
  to `S` preserves FG. -/
lemma restrictedScalars_fg_of_fg [Module.Finite S R] {s : Submodule R M} (hs : s.FG) :
    (s.restrictScalars S).FG := by
  rw [← Module.Finite.iff_fg] at *
  exact Module.Finite.trans R s

-- Q: Is there a simpler proof for this?
/-- If a ring `R` is finite over a subring `S` and restricting the scalars of an `R`-submodule
  to `S` yields an FG submodule, then the initial submodule was also FG. -/
lemma fg_of_restrictedScalars_fg [Module.Finite S R] {s : Submodule R M}
    (hs : (s.restrictScalars S).FG) : s.FG := by
  obtain ⟨g, hg⟩ := hs
  use g
  rw [← SetLike.coe_set_eq, coe_restrictScalars] at hg
  have hg := congrArg (span R) hg
  rw [Submodule.span_span_of_tower] at hg
  simp [hg] -- span_eq

/-- If a ring `R` is finite over a subring `S` then an `R`-submodule is FG if and only if it is
  FG after restricting the scalars to `S`. -/
lemma restrictedScalars_fg_iff_fg [Module.Finite S R] {s : Submodule R M} :
    (s.restrictScalars S).FG ↔ s.FG := ⟨fg_of_restrictedScalars_fg, restrictedScalars_fg_of_fg S⟩

variable (R) in
/-- If a ring `R` is finite over a subring `S` then the `R`-span of an FG `S`-submodule is FG. -/
lemma span_scalars_fg [Module.Finite S R] {s : Submodule S M} (hfg : s.FG) :
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
lemma inf_fg_right (S : Submodule R M) {T : Submodule R M} (hT : T.FG) : (S ⊓ T).FG :=
  isNoetherian_submodule_right.mp (isNoetherian_of_fg_of_noetherian _ hT) S

/-- The intersection of a submodule with an FG submodule is FG. -/
lemma inf_fg_left {S : Submodule R M} (hS : S.FG) (T : Submodule R M) : (S ⊓ T).FG := by
  rw [inf_comm]; exact inf_fg_right T hS

/-- A submodule contained in an FG submodule is FG. -/
lemma fg_of_le_fg {S T : Submodule R M} (hT : T.FG) (hST : S ≤ T) : S.FG := by
  rw [← inf_eq_left.mpr hST]; exact S.inf_fg_right hT

end IsNoetherianRing

end Submodule
