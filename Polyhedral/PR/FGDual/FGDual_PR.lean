/-
Copyright (c) 2025 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/

import Polyhedral.PR.Dual.Dual_PR
import Polyhedral.PR.CoFG.FG_PR
import Polyhedral.PR.FGDual.DualClosed_PR

open Module Function LinearMap

namespace Submodule

section CommSemiring

variable {R M N : Type*}
variable [CommRing R]
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R} -- bilinear pairing

variable (p) in
/-- A submodule is FGDual if it is the dual of a finite set. Equivalently, a submodule is FGDual
  if it can be expressed by finitely many equalities.
  This is in analogy to `FG` (finitely generated) which is the span of a finite set. -/
def FGDual (S : Submodule R N) : Prop := ∃ s : Finset M, dual p s = S

/-- A FGDual submodule is the dual of an FG cone. If the pairin `p` is at left-separating, then
  one can choose the dual of the FGDual submodule as this FG submodule. -/
lemma FGDual.exists_fg_dual {S : Submodule R N} (hS : S.FGDual p) :
    ∃ T : Submodule R M, T.FG ∧ dual p T = S := by
  obtain ⟨s, hs⟩ := hS;
  exact ⟨_, fg_span s.finite_toSet, by simp only [dual_span, hs]⟩

/-- A FGDual cone is FGDual w.r.t. the standard pairing. -/
lemma FGDual.to_id {S : Submodule R N} (hS : S.FGDual p) : S.FGDual .id
    := by classical
  obtain ⟨s, hs⟩ := hS
  use Finset.image p s
  simp [← dual_id, hs]

variable (p) in
/-- The dual of a `Finset` is FGDual. -/
lemma FGDual.of_dual_finset (s : Finset M) : (dual p s).FGDual p := by use s

variable (p) in
/-- The dual of a finite set is FGDual. -/
lemma FGDual.of_dual_finite {s : Set M} (hs : s.Finite) : (dual p s).FGDual p := by
  use hs.toFinset; simp

variable (p) in
/-- The dual of an FG cone is FGDual. -/
lemma FGDual.of_dual_fg {S : Submodule R M} (hS : S.FG) : (dual p S).FGDual p := by
  obtain ⟨s, rfl⟩ := hS
  use s; rw [← dual_span]

alias FG.dual_fgdual := FGDual.of_dual_fg

/-- The intersection of two FGDual cones is FGDual. -/
lemma FGDual.inf {S T : Submodule R N} (hS : S.FGDual p) (hT : T.FGDual p) :
    (S ⊓ T).FGDual p := by classical
  obtain ⟨s, rfl⟩ := hS
  obtain ⟨t, rfl⟩ := hT
  use s ∪ t; rw [Finset.coe_union, dual_union]

/-- The double dual of an FGDual cone is the cone itself. -/
@[simp]
lemma FGDual.dual_dual_flip {S : Submodule R N} (hS : S.FGDual p) :
    dual p (dual p.flip S) = S := by
  obtain ⟨s, rfl⟩ := hS
  exact dual_dual_flip_dual (p := p) s

/-- The double dual of a FGDual cone is the cone itself. -/
@[simp]
lemma FGDual.dual_flip_dual {S : Submodule R M} (hS : S.FGDual p.flip) :
    dual p.flip (dual p S) = S := hS.dual_dual_flip

lemma FGDual.dualClosed {S : Submodule R M} (hS : S.FGDual p.flip) :
    S.DualClosed p := hS.dual_flip_dual

lemma FGDual.dualClosed_flip {S : Submodule R N} (hS : S.FGDual p) :
    S.DualClosed p.flip := hS.dual_dual_flip

@[simp]
lemma FGDual.ker_le {S : Submodule R N} (hS : S.FGDual p) : ker p.flip ≤ S := by
  rw [← dual_dual_flip hS]
  exact ker_le_dual _

variable (p) in
/-- The top submodule is FGDual. -/
lemma FGDual.top : (⊤ : Submodule R N).FGDual p := ⟨⊥, by simp⟩

variable (p) in
protected lemma FGDual.ker [Module.Finite R M] : (ker p.flip).FGDual p := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := M)
  use s; rw [← dual_span, hs, top_coe, dual_univ_ker]

variable (p) [Fact p.SeparatingRight] in
/-- The bottom submodule is FGDual in finite dimensional space. -/
lemma FGDual.bot [Module.Finite R M] : (⊥ : Submodule R N).FGDual p := by
  simpa only [SeparatingLeft.ker_eq_bot] using FGDual.ker p

end CommSemiring

section IsNoetherianRing

variable {R : Type*} [CommRing R] [IsNoetherianRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}

/-- An FGDual submodule is CoFG. -/
theorem FGDual.cofg {S : Submodule R N} (hS : S.FGDual p) : S.CoFG := by
  obtain ⟨s, rfl⟩ := hS
  exact CoFG.of_dual_finset p s

theorem FGDual.fg_of_isCompl {S T : Submodule R N} (hST : IsCompl S T) (hS : S.FGDual p) : T.FG :=
  CoFG.isCompl_fg hST (FGDual.cofg hS)

end IsNoetherianRing

end Submodule
