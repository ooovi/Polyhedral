/-
Copyright (c) 2025 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/

import Polyhedral.PR.BilinearMap.BilinearMap_PR
import Polyhedral.PR.Dual.Dual_PR

open Module Function LinearMap

namespace Submodule

section CommSemiring

variable {R M N : Type*}
variable [CommRing R]
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}

variable (p) in
/-- A submodule is DualFG if it is the dual of a finite set. Equivalently, it can be expressed
  by finitely many equalities. This is the counterpart to `FG` (finitely generated) which is
  expressed by finitely many generators. -/
def DualFG (S : Submodule R N) : Prop := ∃ s : Finset M, dual p s = S

/-- A DualFG submodule is the dual of an FG submodule. If the pairing `p` is left-separating, then
  one can choose here the dual of the DualFG submodule. -/
lemma DualFG.exists_fg_dual {S : Submodule R N} (hS : S.DualFG p) :
    ∃ T : Submodule R M, T.FG ∧ dual p T = S := by
  obtain ⟨s, hs⟩ := hS;
  exact ⟨_, fg_span s.finite_toSet, by simp only [dual_span, hs]⟩

/-- A DualFG submodule is DualFG w.r.t. the standard pairing. -/
lemma DualFG.to_id {S : Submodule R N} (hS : S.DualFG p) : S.DualFG .id
    := by classical
  obtain ⟨s, hs⟩ := hS
  use Finset.image p s
  simp [← dual_id, hs]

variable (p) in
/-- The dual of a `Finset` is DualFG. -/
lemma DualFG.of_dual_finset (s : Finset M) : (dual p s).DualFG p := by use s

variable (p) in
/-- The dual of an FG submodule is DualFG. -/
lemma DualFG.of_dual_fg {S : Submodule R M} (hS : S.FG) : (dual p S).DualFG p := by
  obtain ⟨s, rfl⟩ := hS
  use s; rw [← dual_span]

alias FG.dual_dualfg := DualFG.of_dual_fg

/-- The intersection of two DualFG submodule is DualFG. -/
lemma DualFG.inf {S T : Submodule R N} (hS : S.DualFG p) (hT : T.DualFG p) :
    (S ⊓ T).DualFG p := by classical
  obtain ⟨s, rfl⟩ := hS
  obtain ⟨t, rfl⟩ := hT
  use s ∪ t; rw [Finset.coe_union, dual_union]

/-- The double dual of an DualFG submodule is the submodule itself. -/
@[simp]
lemma DualFG.dual_dual_flip {S : Submodule R N} (hS : S.DualFG p) :
    dual p (dual p.flip S) = S := by
  obtain ⟨s, rfl⟩ := hS
  exact dual_dual_flip_dual (p := p) s

/-- The double dual of a DualFG submodule is the submodule itself. -/
@[simp]
lemma DualFG.dual_flip_dual {S : Submodule R M} (hS : S.DualFG p.flip) :
    dual p.flip (dual p S) = S := hS.dual_dual_flip

-- lemma DualFG.dualClosed {S : Submodule R M} (hS : S.DualFG p.flip) :
--     S.DualClosed p := hS.dual_flip_dual

-- lemma DualFG.dualClosed_flip {S : Submodule R N} (hS : S.DualFG p) :
--     S.DualClosed p.flip := hS.dual_dual_flip

@[simp]
lemma DualFG.ker_le {S : Submodule R N} (hS : S.DualFG p) : ker p.flip ≤ S := by
  rw [← dual_dual_flip hS]
  exact ker_le_dual _

variable (p) in
/-- The top submodule is DualFG. -/
lemma DualFG.top : (⊤ : Submodule R N).DualFG p := ⟨⊥, by simp⟩

variable (p) [Module.Finite R M] in
protected lemma DualFG.ker : (ker p.flip).DualFG p := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := M)
  use s; rw [← dual_span, hs, top_coe, dual_univ_ker]

variable (p) [Fact p.SeparatingRight] [Module.Finite R M] in
/-- The bottom submodule is DualFG in finite dimensional space. -/
lemma DualFG.bot : (⊥ : Submodule R N).DualFG p := by
  simpa only [SeparatingLeft.ker_eq_bot] using DualFG.ker p

end CommSemiring

section IsNoetherianRing

variable {R : Type*} [CommRing R] [IsNoetherianRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}

/-- An DualFG submodule is CoFG. -/
theorem DualFG.cofg {S : Submodule R N} (hS : S.DualFG p) : S.CoFG := by
  obtain ⟨s, rfl⟩ := hS
  exact CoFG.of_dual_finset p s

theorem DualFG.fg_of_isCompl {S T : Submodule R N} (hST : IsCompl S T) (hS : S.DualFG p) : T.FG :=
  CoFG.isCompl_fg hST (DualFG.cofg hS)

end IsNoetherianRing

end Submodule
