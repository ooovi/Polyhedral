/-
Copyright (c) 2025 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Ideal.Quotient.Index

import Polyhedral.Mathlib.Algebra.Module.Submodule.CoFG

open Module Function LinearMap

namespace Submodule

section CommSemiring

variable {R M N : Type*}
variable [CommRing R]
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R} -- bilinear pairing

/-- A cone is `CoFG` (co-finitely generated) if it is the dual of a finite set.
  This is in analogy to `FG` (finitely generated) which is the span of a finite set. -/
abbrev CoFG' (S : Submodule R M) : Prop := Module.Finite R (M ⧸ S)

/-- The top submodule is CoFG. -/
lemma cofg_top' : (⊤ : Submodule R M).CoFG' := inferInstance

/-- The bottom submodule of a finite module is CoFG. -/
lemma cofg_bot' [Module.Finite R M] : (⊥ : Submodule R M).CoFG' := inferInstance

-- NOTE: This should be in mathlib?
variable (R M) in
def quotEquivOfEqBot' : (M ⧸ (⊥ : Submodule R M)) ≃ₗ[R] M := quotEquivOfEqBot ⊥ rfl

lemma Module.Finite.of_cofg_bot' (h : (⊥ : Submodule R M).CoFG') : Module.Finite R M
    := Finite.equiv (quotEquivOfEqBot' R M)

lemma FG.compl_cofg' {S T : Submodule R M} (hST : IsCompl S T) (hS : S.FG) : T.CoFG' := by
  have : Module.Finite R S := Finite.iff_fg.mpr hS
  exact Finite.equiv (quotientEquivOfIsCompl T S hST.symm).symm

lemma CoFG'.compl_fg {S T : Submodule R M} (hST : IsCompl S T) (hS : S.CoFG') : T.FG
  := Finite.iff_fg.mp <| Finite.equiv <| quotientEquivOfIsCompl S T hST

lemma sup_cofg' {S : Submodule R M} (hS : S.CoFG') (T : Submodule R M) : (S ⊔ T).CoFG'
  := Finite.equiv (quotientQuotientEquivQuotientSup S T)

alias CoFG'.sup := sup_cofg'

/-
 * introduce corank and cofinrank
 * CoFG' iff corank is finite
 * generation from finite set
 * If finite dim, then all FG submodules are CoFG
 * relation to CoFG (better in the file CoFG when duality is available)
-/

variable [Module.Finite R M] in
lemma FG.cofg'{S : Submodule R M} (hS : S.FG) : S.CoFG' := by
  -- refine Submodule.finite_quotient_smul ⊤
  sorry

lemma CoFG.exists_finset_map_ker {S : Submodule R N} (hS : S.CoFG p) :
    ∃ (s : Finset M) (Φ : N →ₗ[R] (s → R)), S = ker Φ := by
    -- ∃ (ι : Type*) (_ : Fintype ι) (Φ : N →ₗ[R] (ι → R)), S = ker Φ := by
  obtain ⟨s, rfl⟩ := hS
  use s
  sorry

theorem CoFG.cofg' {S : Submodule R N} (hS : S.CoFG p) : S.CoFG' := by
  obtain ⟨s, Φ, h⟩ := exists_finset_map_ker hS

  sorry

variable [IsNoetherianRing R] [Fact p.IsFaithfulPair] in
theorem CoFG'.cofg {S : Submodule R N} (hS : S.CoFG') : S.CoFG p := by
  sorry


end CommSemiring

end Submodule
