/-
Copyright (c) 2025 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/
import Mathlib.RingTheory.Finiteness.Cofinite
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Algebra.Exact

import Polyhedral.Mathlib.Algebra.Module.Submodule.Basic
import Polyhedral.Mathlib.Algebra.Module.Submodule.FG
import Polyhedral.Mathlib.RingTheory.Finiteness.Corank

open Module Function LinearMap

namespace Submodule

section CommSemiring

variable {R : Type*} [Ring R]
variable {M : Type*} [AddCommGroup M] [Module R M]

-- this should be somewhere in mathlib
theorem quot_finite_of_finite [Module.Finite R M] (S : Submodule R M) :
    Module.Finite R (M ⧸ S) := by
  rw [finite_def, ← Finite.iff_fg, ← LinearMap.range_eq_top_of_surjective _ S.mkQ_surjective]
  exact Module.Finite.range S.mkQ

-- lemma CoFG.finite_quot {S : Submodule R M} (hS : S.CoFG) : Module.Finite R (M ⧸ S) := hS
-- lemma CoFG.finite_quot_iff {S : Submodule R M} : S.CoFG = Module.Finite R (M ⧸ S) := rfl

-- lemma CoFG.fg_quot_iff {S : Submodule R M} : S.CoFG ↔ FG (⊤ : Submodule R (M ⧸ S)) := by
--   rw [← finite_def]
-- lemma CoFG.fg_quot {S : Submodule R M} (hS : S.CoFG) :
--     FG (⊤ : Submodule R (M ⧸ S)) := fg_quot_iff.mp hS

/-- For a CoFG submodule exists a disjoint FG submodule. -/
lemma CoFG.exists_fg_codisjoint {S : Submodule R M} (hS : S.CoFG) :
    ∃ T : Submodule R M, T.FG ∧ Codisjoint S T := by classical
  obtain ⟨T, hT, hST⟩ := exists_spanRank_le_codisjoint S
  use T; constructor
  · simp only [finite_def, ← Submodule.spanRank_finite_iff_fg] at ⊢ hS
    --simpa only [hT] using hS
    exact lt_of_le_of_lt hT hS
  · exact hST

-- lemma CoFG.exists_fg_codisjoint {S : Submodule R M} (hS : S.CoFG) :
--     ∃ T : Submodule R M, T.FG ∧ Codisjoint S T := by classical
--   obtain ⟨s, hs⟩ := hS
--   let inv := surjInv S.mkQ_surjective
--   use span R (s.image inv)
--   constructor
--   · exact fg_span (Finset.finite_toSet _)
--   rw [codisjoint_iff, ← map_mkQ_eq_top]
--   ext x
--   simp only [mem_map, mem_top, iff_true, Finset.coe_image]
--   have hx : x ∈ span R s := by simp only [hs, mem_top]
--   obtain ⟨f, hxf, hf⟩ := mem_span_finset'.mp hx
--   use ∑ y, f y • inv y
--   constructor
--   · apply sum_mem
--     intro y _
--     refine smul_mem _ _ (mem_span_of_mem ?_)
--     simpa using ⟨y, by simp⟩
--   · simp [inv, surjInv_eq S.mkQ_surjective]

-- This needs Field for th Codisjoint part.
-- (see : https://chatgpt.com/c/69300596-3280-832f-8916-3b4b07c432d8)
lemma CoFG._exists_fg_compl {S : Submodule R M} (hS : S.CoFG) :
    ∃ T : Submodule R M, T.FG ∧ IsCompl S T := by
  obtain ⟨s, hs⟩ := hS
  use span R (surjInv S.mkQ_surjective '' s)
  constructor
  · exact fg_span <| Set.Finite.image _ <| s.finite_toSet
  constructor
  · rw [disjoint_def]
    intro x hxS hx
    have x' := S.mkQ x

    sorry
  · rw [codisjoint_iff_exists_add_eq]
    intro x
    have x' := S.mkQ x
    sorry
  -- just take preimage of generators `s` to span the rest of ⊤, right?
  -- Q: do we also have the converse: given FG, we find complementary CoFG?

  -- use (Module.Finite.compl R S).some
  -- exact ⟨Finite.iff_fg.mpr (Module.Finite.compl R S).some_spec.1,
  --   (Module.Finite.compl R S).some_spec.2⟩

@[deprecated]
lemma sSup_cofg {s : Set (Submodule R M)} (hs : ∃ S ∈ s, S.CoFG) :
    (sSup s).CoFG := by
  obtain ⟨_, hS, hcofg⟩ := hs
  exact hcofg.of_cofg_le (le_sSup hS)

section StrongRankCondition

open Cardinal

variable [StrongRankCondition R]

lemma CoFG.corank_lt_aleph0 {S : Submodule R M} (hS : S.CoFG) : corank S < ℵ₀
  := Module.rank_lt_aleph0 R _

lemma CoFG.corank_lt_aleph0_iff {S : Submodule R M} [Free R (M ⧸ S)] :
    corank S < ℵ₀ ↔ CoFG S := Module.rank_lt_aleph0_iff

end StrongRankCondition

variable {N : Type*} [AddCommGroup N] [Module R N]

lemma ker_cofg_of_range_fg {f : M →ₗ[R] N} (h : (range f).FG) : (ker f).CoFG
    := range_fg_iff_ker_cofg.mp h

lemma range_fg_of_ker_cofg {f : M →ₗ[R] N} (h : (ker f).CoFG) : (range f).FG
    := range_fg_iff_ker_cofg.mpr h

lemma ker_fg_iff_range_cofg (f : M →ₗ[R] M) : (ker f).FG ↔ (range f).CoFG := by
  sorry

lemma CoFG.map_ker_fg {S : Submodule R M} {f : M →ₗ[R] M}
    (hf : (ker f).FG) (hf' : (range f).CoFG) (hS : S.CoFG) :
      (S.map f).CoFG := by
  sorry

lemma CoFG.map_surj {S : Submodule R M} {f : M →ₗ[R] M} (hf : Surjective f) (hS : S.CoFG) :
    (S.map f).CoFG := by

  sorry

-- lemma CoFG.map_equiv {S : Submodule R M} (e : M ≃ₗ[R] M) (hS : S.CoFG) : (S.map e).CoFG := by

--   sorry

section HasRankNullity

variable [HasRankNullity R]

end HasRankNullity

section IsNoetherianRing

variable [IsNoetherianRing R]

/-- The restriction of a CoFG submodule is CoFG. -/
lemma CoFG.restrict (S : Submodule R M) {T : Submodule R M} (hT : T.CoFG) :
    CoFG (restrict S T) := by
  haveI := Module.Finite.of_injective _ (quot_restrict_linearMap_quot_injective (S ⊔ T) T)
  exact Finite.equiv (quot_restrict_iso_sup_quot_restrict S T).symm

-- theorem fg_of_linearEquiv' {S : Submodule R M} {T : Submodule R N} (e : S ≃ₗ[R] T)
--     (h : T.FG) : S.FG := by
--   rw [← Finite.iff_fg, finite_def] at ⊢ h
--   exact fg_of_linearEquiv e h

-- TODO: direction of equiv in `Module.Finite.equiv` and `fg_of_linearEquiv` is opposite.

-- TODO: move out of Noetherian section once clear that Noetherian is not need
-- we keep it here because some results it depends on are not yet proven, such as
-- `quot_restrict_linearMap_quot_range`.
/-- The embedding of a CoFG submodule of a CoFG submodule is CoFG. -/
lemma CoFG.embed {S : Submodule R M} {T : Submodule R S} (hS : S.CoFG) (hT : T.CoFG) :
    CoFG (embed T) := by
  haveI := Finite.equiv (quotientQuotientEquivQuotient (Submodule.embed T) S embed_le).symm
  haveI := Finite.equiv (quot_equiv_map_embed_mkQ S T)
  exact Finite.of_submodule_quotient <| map (Submodule.embed T).mkQ S

end IsNoetherianRing

end CommSemiring

section DivisionRing

variable {R : Type*} [DivisionRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

lemma CoFG.disjoint_fg {S T : Submodule R M}
    (hST : Disjoint S T) (hS : S.CoFG) : T.FG := by
  obtain ⟨U, hSU, hUT⟩ := hST.exists_isCompl
  exact (hS.of_cofg_le hSU).fg_of_isCompl hUT

lemma FG.codisjoint_cofg {S T : Submodule R M} (hST : Codisjoint S T) (hS : S.FG) : T.CoFG := by
  obtain ⟨U, hSU, hUT⟩ := hST.exists_isCompl
  exact (hS.of_le hSU).cofg_of_isCompl hUT

end DivisionRing

end Submodule
