/-
Copyright (c) 2025 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Dimension.RankNullity

import Polyhedral.Mathlib.Algebra.Module.Submodule.Basic

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

/-- The top submodule is CoFG. -/
@[simp] lemma cofg_top : (⊤ : Submodule R M).CoFG := inferInstance

/-- The bottom submodule of a finite module is CoFG. -/
@[simp] lemma cofg_bot [Module.Finite R M] : (⊥ : Submodule R M).CoFG := inferInstance

lemma _root_.Module.Finite.of_cofg_bot (h : (⊥ : Submodule R M).CoFG) : Module.Finite R M
    := Finite.equiv (quotEquivOfEqBot ⊥ rfl)

lemma cofg_of_le {S T : Submodule R M} {hST : S ≤ T} (hS : S.CoFG) : T.CoFG := by
  classical
  -- -- Register `Module.Finite R (M ⧸ S)` as an instance
  -- haveI := hS
  -- -- The canonical surjection (m + S) ↦ (m + T)
  -- let f : (M ⧸ S) →ₗ[R] (M ⧸ T) := Submodule.quotientMap _ _ hST
  -- have hf : Function.Surjective f := Submodule.quotientMap_surjective _ _ hST
  -- -- Images of finitely generated modules are finitely generated
  -- exact Module.Finite.of_surjective f hf
  sorry

lemma CoFG.isCompl_fg {S T : Submodule R M} (hST : IsCompl S T) (hS : S.CoFG) : T.FG
  := Finite.iff_fg.mp <| Finite.equiv <| quotientEquivOfIsCompl S T hST

-- Needs DivisionRing
lemma CoFG.disjoint_fg [IsNoetherianRing R] {S T : Submodule R M}
    (hST : Disjoint S T) (hS : S.CoFG) : T.FG := by
  -- obtain ⟨U, hSU, hUT⟩ := isCompl_of_disjoint hST
  wlog hST : IsCompl S T with H
  · sorry
  exact Finite.iff_fg.mp <| Finite.equiv <| quotientEquivOfIsCompl S T hST

lemma FG.isCompl_cofg {S T : Submodule R M} (hST : IsCompl S T) (hS : S.FG) : T.CoFG := by
  haveI := Finite.iff_fg.mpr hS
  exact Finite.equiv (quotientEquivOfIsCompl T S hST.symm).symm

-- needs division ring
lemma FG.codisjoint_cofg {S T : Submodule R M} (hST : Codisjoint S T) (hS : S.FG) : T.CoFG := by
  haveI := Finite.iff_fg.mpr hS
  unfold CoFG
  haveI : Module.Finite R ((⊤ : Submodule R M) ⧸ restrict ⊤ S) := sorry
  -- Idea: use second isomorphism theorem: M / T = (S + T) / T ≃ S / (S ⊓ T) is FG
  --   also use `quot_finite_of_finite` above.
  --
  -- refine Finite.equiv Submodule.topEquiv
  -- Submodule.topEquiv
  -- refine module_finite_of_liesOver ?_ ?_
  -- apply LinearMap.quotientInfEquivSupQuotient
  sorry

lemma CoFG.sup {S : Submodule R M} (hS : S.CoFG) (T : Submodule R M) : (S ⊔ T).CoFG
  := Finite.equiv (quotientQuotientEquivQuotientSup S T)

alias sup_cofg := CoFG.sup

lemma sSup_cofg {s : Set (Submodule R M)} (hs : ∃ S ∈ s, S.CoFG) :
    (sSup s).CoFG := by
  obtain ⟨S, hS, hcofg⟩ := hs
  rw [right_eq_sup.mpr <| le_sSup hS]
  exact hcofg.sup _

variable [Module.Finite R M] in
/-- In a finite module every submodule is CoFG. -/
-- Note that not every submodule is necessarily FG. So FG = CoFG needs more hypotheses.
lemma Finite.cofg {S : Submodule R M} : S.CoFG := Module.Finite.quotient R S

noncomputable abbrev corank (S : Submodule R M) : Cardinal := Module.rank R (M ⧸ S)
  -- ⨅ ι : { T : Submodule R M // S ⊔ T = ⊤ }, (Module.rank R ι.1)

noncomputable abbrev fincorank (S : Submodule R M) : Nat := Module.finrank R (M ⧸ S)

section StrongRankCondition

open Cardinal

variable [StrongRankCondition R]

lemma CoFG.corank_lt_aleph0 {S : Submodule R M} (hS : S.CoFG) : corank S < ℵ₀
  := Module.rank_lt_aleph0 R _

lemma corank_lt_aleph0_iff {S : Submodule R M} [Free R (M ⧸ S)] :
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

lemma CoFG.map_equiv {S : Submodule R M} (e : M ≃ₗ[R] M) (hS : S.CoFG) : (S.map e).CoFG := by

  sorry

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
  | empty => simpa using cofg_top
  | insert w s hws hs' =>
    simp only [Finset.mem_insert, forall_eq_or_imp, Finset.coe_insert, sInf_insert] at *
    exact inf_cofg hs.1 (hs' hs.2)

theorem sInf_cofg' {s : Set (Submodule R M)} (hs : s.Finite) (hcofg : ∀ S ∈ s, S.CoFG) :
    (sInf s).CoFG := by
  rw [← hs.coe_toFinset] at hcofg ⊢; exact sInf_cofg hcofg

end IsNoetherianRing

end CommSemiring

end Submodule
