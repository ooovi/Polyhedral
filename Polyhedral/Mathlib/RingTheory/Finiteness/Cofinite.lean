/-
Copyright (c) 2025 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/
module

public import Mathlib.RingTheory.Finiteness.Cofinite
public import Polyhedral.Mathlib.Algebra.Module.Submodule.Basic
public import Polyhedral.Mathlib.RingTheory.Finiteness.Corank

import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! This file proves results about cofinitely generated submodules that are intended to
go into (or close to) `Mathlib.RingTheory.Finiteness.Cofinite`. -/

public section

open Module Function LinearMap

namespace Submodule

variable {R M : Type*}

section CommSemiring

variable [Ring R]
variable [AddCommGroup M] [Module R M]

-- this should be somewhere in mathlib
theorem quot_finite_of_finite [Module.Finite R M] (S : Submodule R M) :
    Module.Finite R (M ⧸ S) := by
  rw [finite_def, ← Finite.iff_fg, ← LinearMap.range_eq_top_of_surjective _ S.mkQ_surjective]
  exact Module.Finite.range S.mkQ

lemma CoFG.fg_quot_iff {S : Submodule R M} :
    S.CoFG ↔ FG (⊤ : Submodule R (M ⧸ S)) := by
  rw [← finite_def]

lemma CoFG.fg_quot {S : Submodule R M} (hS : S.CoFG) :
    FG (⊤ : Submodule R (M ⧸ S)) :=
  fg_quot_iff.mp hS

/-- For a CoFG submodule there exists a codisjoint FG submodule. -/
lemma CoFG.exists_fg_codisjoint {S : Submodule R M} (hS : S.CoFG) :
    ∃ T : Submodule R M, T.FG ∧ Codisjoint S T := by classical
  obtain ⟨T, hT, hST⟩ := exists_spanRank_codisjoint S
  refine ⟨T, ?_, hST⟩
  simp only [finite_def, ← Submodule.spanRank_finite_iff_fg] at ⊢ hS
  exact lt_of_eq_of_lt hT hS

lemma sSup_cofg {s : Set (Submodule R M)} (hs : ∃ S ∈ s, S.CoFG) :
    (sSup s).CoFG := by
  obtain ⟨_, hS, hcofg⟩ := hs
  exact hcofg.of_le (le_sSup hS)

section StrongRankCondition

open Cardinal

variable [StrongRankCondition R]

lemma CoFG.corank_lt_aleph0 {S : Submodule R M} (hS : S.CoFG) : corank S < ℵ₀ := by
  rw [corank_def]; exact Module.rank_lt_aleph0 R _

lemma CoFG.corank_lt_aleph0_iff {S : Submodule R M} [Free R (M ⧸ S)] :
    corank S < ℵ₀ ↔ CoFG S := by
  rw [corank_def]; exact Module.rank_lt_aleph0_iff

end StrongRankCondition

variable {N : Type*} [AddCommGroup N] [Module R N]

lemma ker_cofg_of_range_fg {f : M →ₗ[R] N} (h : (range f).FG) : (ker f).CoFG
    := range_fg_iff_ker_cofg.mp h

lemma range_fg_of_ker_cofg {f : M →ₗ[R] N} (h : (ker f).CoFG) : (range f).FG
    := range_fg_iff_ker_cofg.mpr h

section HasRankNullity

variable [HasRankNullity R]

end HasRankNullity

/-- The embedding of a CoFG submodule of a CoFG submodule is CoFG. -/
lemma CoFG.embed {S : Submodule R M} {T : Submodule R S} (hS : S.CoFG) (hT : T.CoFG) :
    CoFG (embed T) := by
  have := Finite.equiv (quotientQuotientEquivQuotient (Submodule.embed T) S embed_le).symm
  have := Finite.equiv (quot_equiv_map_embed_mkQ S T)
  exact Finite.of_submodule_quotient <| map (Submodule.embed T).mkQ S

section IsNoetherianRing

variable [IsNoetherianRing R]

/-- The restriction of a CoFG submodule is CoFG. -/
lemma CoFG.restrict (S : Submodule R M) {T : Submodule R M} (hT : T.CoFG) :
    CoFG (restrict S T) := by
  have := Module.Finite.of_injective _ (quot_restrict_linearMap_quot_injective (S ⊔ T) T)
  exact Finite.equiv (quot_restrict_iso_sup_quot_restrict S T).symm

end IsNoetherianRing

end CommSemiring

section IsNoetherianRing

variable [Ring R] [IsNoetherianRing R]
variable [AddCommGroup M] [Module R M]

lemma CoFG.disjoint_fg {S T : Submodule R M}
    (hST : Disjoint S T) (hS : S.CoFG) : T.FG := by
  rw [← Module.Finite.iff_fg]
  let := hS
  apply Module.Finite.of_injective (S.mkQ.domRestrict T)
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_domRestrict, Submodule.ker_mkQ,
    ← disjoint_iff_comap_eq_bot]
  exact hST.symm

end IsNoetherianRing

section DivisionRing

variable [DivisionRing R]
variable [AddCommGroup M] [Module R M]

lemma FG.codisjoint_cofg {S T : Submodule R M} (hST : Codisjoint S T) (hS : S.FG) : T.CoFG := by
  obtain ⟨U, hSU, hUT⟩ := hST.exists_isCompl
  exact (hS.of_le hSU).cofg_of_isCompl hUT

-- does not hold over a general ring
example {S : Submodule R M} (hS : S.CoFG) :
    ∃ T : Submodule R M, T.FG ∧ IsCompl S T := by
  obtain ⟨T, hST⟩ := S.exists_isCompl
  exact ⟨T, CoFG.disjoint_fg hST.1 hS, hST⟩

-- does not hold over a general ring
example {S : Submodule R M} (hS : S.FG) :
    ∃ T : Submodule R M, T.CoFG ∧ IsCompl S T := by
  obtain ⟨T, hST⟩ := S.exists_isCompl
  exact ⟨T, FG.codisjoint_cofg hST.2 hS, hST⟩

end DivisionRing

section Field

variable [Field R]
variable [AddCommGroup M] [Module R M]

lemma CoFG.dualAnnihilator_fg {S : Submodule R M} (hS : S.CoFG) : FG S.dualAnnihilator := by
  rw [← Submodule.fg_top]
  refine fg_of_linearEquiv S.dualQuotEquivDualAnnihilator.symm ?_
  simpa [← finite_def, Module.finite_dual_iff] using hS

end Field

end Submodule
