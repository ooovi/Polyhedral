/-
Copyright (c) 2025 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Algebra.Exact

import Polyhedral.Mathlib.Algebra.Module.Submodule.Basic
import Polyhedral.Mathlib.Algebra.Module.Submodule.FG
import Polyhedral.Mathlib.Algebra.Module.Submodule.Corank

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


/-- A submodule `S` is co-finitely generated (CoFG) if the quotient space `M ⧸ S` is
  finitely generated (`Module.Finite`). -/
abbrev CoFG (S : Submodule R M) : Prop := Module.Finite R (M ⧸ S)

-- lemma CoFG.finite_quot {S : Submodule R M} (hS : S.CoFG) : Module.Finite R (M ⧸ S) := hS
-- lemma CoFG.finite_quot_iff {S : Submodule R M} : S.CoFG = Module.Finite R (M ⧸ S) := rfl

-- lemma CoFG.fg_quot_iff {S : Submodule R M} : S.CoFG ↔ FG (⊤ : Submodule R (M ⧸ S)) := by
--   rw [← finite_def]
-- lemma CoFG.fg_quot {S : Submodule R M} (hS : S.CoFG) :
--     FG (⊤ : Submodule R (M ⧸ S)) := fg_quot_iff.mp hS

/-- The top submodule is CoFG. -/
@[simp] lemma cofg_top : (⊤ : Submodule R M).CoFG := inferInstance

/-- The bottom submodule of a finite module is CoFG. -/
@[simp] lemma cofg_bot [Module.Finite R M] : (⊥ : Submodule R M).CoFG := inferInstance

lemma _root_.Module.Finite.of_cofg_bot (h : (⊥ : Submodule R M).CoFG) : Module.Finite R M
    := Finite.equiv (quotEquivOfEqBot ⊥ rfl)

lemma CoFG.isCompl_fg {S T : Submodule R M} (hST : IsCompl S T) (hS : S.CoFG) : T.FG
  := Finite.iff_fg.mp <| Finite.equiv <| quotientEquivOfIsCompl S T hST

lemma FG.isCompl_cofg {S T : Submodule R M} (hST : IsCompl S T) (hS : S.FG) : T.CoFG := by
  haveI := Finite.iff_fg.mpr hS
  exact Finite.equiv (quotientEquivOfIsCompl T S hST.symm).symm

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

lemma CoFG.sup {S : Submodule R M} (hS : S.CoFG) (T : Submodule R M) : (S ⊔ T).CoFG
  := Finite.equiv (quotientQuotientEquivQuotientSup S T)

lemma cofg_of_le {S T : Submodule R M} (hST : S ≤ T) (hS : S.CoFG) : T.CoFG := by
  rw [← sup_eq_right.mpr hST]
  exact hS.sup T

alias sup_cofg := CoFG.sup

-- TODO: Proving this first (before CoFG.sup) might shorten total proof length.
lemma CoFG.of_cofg_le {S T : Submodule R M} (hS : S.CoFG) (hT : S ≤ T) : T.CoFG := by
  rw [← sup_eq_right.mpr hT]
  exact hS.sup T

lemma sSup_cofg {s : Set (Submodule R M)} (hs : ∃ S ∈ s, S.CoFG) :
    (sSup s).CoFG := by
  obtain ⟨S, hS, hcofg⟩ := hs
  rw [right_eq_sup.mpr <| le_sSup hS]
  exact hcofg.sup _

variable [Module.Finite R M] in
/-- In a finite module every submodule is CoFG. -/
-- Note that not every submodule is necessarily FG. So FG = CoFG needs more hypotheses.
lemma Finite.cofg {S : Submodule R M} : S.CoFG := Module.Finite.quotient R S

section StrongRankCondition

open Cardinal

variable [StrongRankCondition R]

lemma CoFG.corank_lt_aleph0 {S : Submodule R M} (hS : S.CoFG) : corank S < ℵ₀
  := Module.rank_lt_aleph0 R _

lemma CoFG.corank_lt_aleph0_iff {S : Submodule R M} [Free R (M ⧸ S)] :
    corank S < ℵ₀ ↔ CoFG S := Module.rank_lt_aleph0_iff

end StrongRankCondition

variable {N : Type*} [AddCommGroup N] [Module R N]

lemma range_fg_iff_ker_cofg {f : M →ₗ[R] N} : (range f).FG ↔ (ker f).CoFG := by
  rw [← Finite.iff_fg]
  exact Module.Finite.equiv_iff <| f.quotKerEquivRange.symm

lemma ker_cofg_of_range_fg {f : M →ₗ[R] N} (h : (range f).FG) : (ker f).CoFG
    := range_fg_iff_ker_cofg.mp h

lemma range_fg_of_ker_cofg {f : M →ₗ[R] N} (h : (ker f).CoFG) : (range f).FG
    := range_fg_iff_ker_cofg.mpr h

/-- The kernel of a liear map into a noetherian module is CoFG. -/
lemma ker_cofg [IsNoetherian R N] (f : M →ₗ[R] N) : (ker f).CoFG
    := ker_cofg_of_range_fg <| IsNoetherian.noetherian _

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

theorem inf_cofg {S T : Submodule R M} (hS : S.CoFG) (hT : T.CoFG) :
      (S ⊓ T).CoFG := by
  rw [← Submodule.ker_mkQ S, ← Submodule.ker_mkQ T, ← LinearMap.ker_prod]
  exact ker_cofg _

theorem sInf_cofg {s : Finset (Submodule R M)} (hs : ∀ S ∈ s, S.CoFG) :
    (sInf (s : Set (Submodule R M))).CoFG := by classical
  induction s using Finset.induction with
  | empty => simp
  | insert w s hws hs' =>
    simp only [Finset.mem_insert, forall_eq_or_imp, Finset.coe_insert, sInf_insert] at *
    exact inf_cofg hs.1 (hs' hs.2)

theorem sInf_cofg' {s : Set (Submodule R M)} (hs : s.Finite) (hcofg : ∀ S ∈ s, S.CoFG) :
    (sInf s).CoFG := by
  rw [← hs.coe_toFinset] at hcofg ⊢; exact sInf_cofg hcofg

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
  obtain ⟨U, hSU, hUT⟩ := exists_isCompl_of_disjoint hST
  exact (cofg_of_le hSU hS).isCompl_fg hUT

lemma FG.codisjoint_cofg {S T : Submodule R M} (hST : Codisjoint S T) (hS : S.FG) : T.CoFG := by
  obtain ⟨U, hSU, hUT⟩ := exists_isCompl_of_codisjoint hST
  exact (FG.of_le hS hSU).isCompl_cofg hUT

end DivisionRing

end Submodule
