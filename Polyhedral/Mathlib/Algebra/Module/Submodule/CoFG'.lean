/-
Copyright (c) 2025 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.RingTheory.Finiteness.Prod

import Polyhedral.Mathlib.Algebra.Module.Submodule.CoFG

open Module Function LinearMap

namespace Submodule

section CommSemiring

variable {R M : Type*} [Ring R]
variable {M : Type*} [AddCommGroup M] [Module R M]

-- TODO: move to extra file
@[simp] lemma ker_prod_mkQ_eq_inf (S T : Submodule R M) : ker (S.mkQ.prod T.mkQ) = S ⊓ T := by
  simp only [LinearMap.ker_prod, Submodule.ker_mkQ]

/-- A submodule `S` is co-finitely generated (CoFG) if the quotient space `M ⧸ S` is
  finitely generated (`Module.Finite`). -/
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

variable [Module.Finite R M] in
/-- In a finite module every submodule is CoFG. -/
lemma Finite.cofg' {S : Submodule R M} : S.CoFG' := Module.Finite.quotient R S

noncomputable abbrev corank (S : Submodule R M) : Cardinal := Module.rank R (M ⧸ S)
  -- ⨅ ι : { T : Submodule R M // S ⊔ T = ⊤ }, (Module.rank R ι.1)

noncomputable abbrev fincorank (S : Submodule R M) : Nat := Module.finrank R (M ⧸ S)

/-
 * corank lemmas
 * CoFG' iff corank is finite
 * generation from finite set
 * relation to CoFG (better in the file CoFG when duality is available)
-/

open Cardinal

section StrongRankCondition

variable [StrongRankCondition R]

lemma CoFG'.corank_lt_aleph0 {S : Submodule R M} (hS : S.CoFG') : corank S < ℵ₀
  := Module.rank_lt_aleph0 R _

lemma corank_lt_aleph0_iff' {S : Submodule R M} [Free R (M ⧸ S)] :
    corank S < ℵ₀ ↔ CoFG' S := Module.rank_lt_aleph0_iff

end StrongRankCondition

section HasRankNullity

variable [HasRankNullity R]

end HasRankNullity

section IsNoetherianRing

variable [IsNoetherianRing R]

theorem inf_cofg' {S T : Submodule R M} (hS : S.CoFG') (hT : T.CoFG') :
      (S ⊓ T).CoFG' := by
  let φ := (mkQ S).prod (mkQ T)
  rw [← ker_prod_mkQ_eq_inf S T]
  let ι : range φ →ₗ[R] (M ⧸ S) × (M ⧸ T) := Submodule.subtype _
  have hι : Function.Injective ι := fun _ _ h => Subtype.ext h
  exact (Module.Finite.of_injective _ hι).equiv φ.quotKerEquivRange.symm

end IsNoetherianRing

section Field

variable {R : Type*} [Field R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}

-- lemma CoFG.exists_finset_map_ker {S : Submodule R N} (hS : S.CoFG p) :
--     ∃ (s : Finset M) (Φ : N →ₗ[R] (s → R)), S = ker Φ := by
--     -- ∃ (ι : Type*) (_ : Fintype ι) (Φ : N →ₗ[R] (ι → R)), S = ker Φ := by
--   obtain ⟨s, rfl⟩ := hS
--   use s
--   sorry

theorem CoFG.cofg' {S : Submodule R N} (hS : S.CoFG p) : S.CoFG' := by
  -- obtain ⟨s, Φ, h⟩ := exists_finset_map_ker hS
  sorry

variable [IsNoetherianRing R] [Fact p.IsFaithfulPair] in
theorem CoFG'.cofg {S : Submodule R N} (hS : S.CoFG') : S.CoFG p := by
  sorry

end Field


end CommSemiring

end Submodule
