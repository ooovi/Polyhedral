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

variable {R : Type*} [Ring R]
variable {M : Type*} [AddCommGroup M] [Module R M]

/-- A submodule `S` is co-finitely generated (CoFG) if the quotient space `M ⧸ S` is
  finitely generated (`Module.Finite`). -/
abbrev CoFG' (S : Submodule R M) : Prop := Module.Finite R (M ⧸ S)

/-- The top submodule is CoFG. -/
lemma cofg_top' : (⊤ : Submodule R M).CoFG' := inferInstance

/-- The bottom submodule of a finite module is CoFG. -/
lemma cofg_bot' [Module.Finite R M] : (⊥ : Submodule R M).CoFG' := inferInstance

lemma Module.Finite.of_cofg_bot' (h : (⊥ : Submodule R M).CoFG') : Module.Finite R M
    := Finite.equiv (quotEquivOfEqBot ⊥ rfl)

lemma FG.isCompl_cofg' {S T : Submodule R M} (hST : IsCompl S T) (hS : S.FG) : T.CoFG' := by
  have : Module.Finite R S := Finite.iff_fg.mpr hS
  exact Finite.equiv (quotientEquivOfIsCompl T S hST.symm).symm

lemma CoFG'.isCompl_fg {S T : Submodule R M} (hST : IsCompl S T) (hS : S.CoFG') : T.FG
  := Finite.iff_fg.mp <| Finite.equiv <| quotientEquivOfIsCompl S T hST

lemma CoFG'.sup {S : Submodule R M} (hS : S.CoFG') (T : Submodule R M) : (S ⊔ T).CoFG'
  := Finite.equiv (quotientQuotientEquivQuotientSup S T)

alias sup_cofg' := CoFG'.sup

lemma sSup_cofg' {s : Set (Submodule R M)} (hs : ∃ S ∈ s, S.CoFG') :
    (sSup s).CoFG' := by
  obtain ⟨S, hS, hcofg⟩ := hs
  rw [right_eq_sup.mpr <| le_sSup hS]
  exact hcofg.sup _

variable [Module.Finite R M] in
/-- In a finite module every submodule is CoFG. -/
-- Note that not every submodule is necessarily FG. So FG = CoFG needs more hypotheses.
lemma Finite.cofg' {S : Submodule R M} : S.CoFG' := Module.Finite.quotient R S

noncomputable abbrev corank (S : Submodule R M) : Cardinal := Module.rank R (M ⧸ S)
  -- ⨅ ι : { T : Submodule R M // S ⊔ T = ⊤ }, (Module.rank R ι.1)

noncomputable abbrev fincorank (S : Submodule R M) : Nat := Module.finrank R (M ⧸ S)

section StrongRankCondition

open Cardinal

variable [StrongRankCondition R]

lemma CoFG'.corank_lt_aleph0 {S : Submodule R M} (hS : S.CoFG') : corank S < ℵ₀
  := Module.rank_lt_aleph0 R _

lemma corank_lt_aleph0_iff' {S : Submodule R M} [Free R (M ⧸ S)] :
    corank S < ℵ₀ ↔ CoFG' S := Module.rank_lt_aleph0_iff

end StrongRankCondition

variable {N : Type*} [AddCommGroup N] [Module R N]

lemma range_fg_iff_ker_cofg' {f : M →ₗ[R] N} : (range f).FG ↔ (ker f).CoFG' := by
  rw [← Finite.iff_fg]
  exact Module.Finite.equiv_iff <| f.quotKerEquivRange.symm

lemma ker_cofg_of_range_fg' {f : M →ₗ[R] N} (h : (range f).FG) : (ker f).CoFG'
    := range_fg_iff_ker_cofg'.mp h

lemma range_fg_of_ker_cofg' {f : M →ₗ[R] N} (h : (ker f).CoFG') : (range f).FG
    := range_fg_iff_ker_cofg'.mpr h

/-- The kernel of a liear map into a noetherian module is CoFG. -/
lemma ker_cofg' [IsNoetherian R N] (f : M →ₗ[R] N) : (ker f).CoFG'
    := ker_cofg_of_range_fg' <| IsNoetherian.noetherian _

lemma ker_fg_iff_range_cofg' (f : M →ₗ[R] M) : (ker f).FG ↔ (range f).CoFG' := by
  sorry

lemma CoFG'.map_ker_fg {S : Submodule R M} {f : M →ₗ[R] M}
    (hf : (ker f).FG) (hf' : (range f).CoFG') (hS : S.CoFG') :
      (S.map f).CoFG' := by
  sorry

lemma CoFG'.map_surj {S : Submodule R M} {f : M →ₗ[R] M} (hf : Surjective f) (hS : S.CoFG') :
    (S.map f).CoFG' := by

  sorry

lemma CoFG'.map_equiv {S : Submodule R M} (e : M ≃ₗ[R] M) (hS : S.CoFG') : (S.map e).CoFG' := by

  sorry

section HasRankNullity

variable [HasRankNullity R]

end HasRankNullity

section IsNoetherianRing

variable [IsNoetherianRing R]

theorem inf_cofg' {S T : Submodule R M} (hS : S.CoFG') (hT : T.CoFG') :
      (S ⊓ T).CoFG' := by
  rw [← Submodule.ker_mkQ S, ← Submodule.ker_mkQ T, ← LinearMap.ker_prod]
  exact ker_cofg' _

theorem sInf_cofg' {s : Finset (Submodule R M)} (hs : ∀ S ∈ s, S.CoFG') :
    (sInf (s : Set (Submodule R M))).CoFG' := by classical
  induction s using Finset.induction with
  | empty => simpa using cofg_top'
  | insert w s hws hs' =>
    simp only [Finset.mem_insert, forall_eq_or_imp, Finset.coe_insert, sInf_insert] at *
    exact inf_cofg' hs.1 (hs' hs.2)

theorem sInf_cofg'' {s : Set (Submodule R M)} (hs : s.Finite) (hcofg : ∀ S ∈ s, S.CoFG') :
    (sInf s).CoFG' := by
  rw [← hs.coe_toFinset] at hcofg ⊢; exact sInf_cofg' hcofg


-- ## DUAL

variable {R : Type*} [CommRing R] [IsNoetherianRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}

variable (p) in
theorem dual_singleton_cofg' (x : M) : (dual p {x}).CoFG' := by
  rw [dual_singleton]; exact ker_cofg' _

variable (p) in
theorem dual_finset_cofg' (s : Finset M) : (dual p s).CoFG' := by
  rw [dual_ker_pi']; exact ker_cofg' _

variable (p) in
theorem dual_finite_cofg' {s : Set M} (hs : s.Finite) : (dual p s).CoFG' := by
  rw [← hs.coe_toFinset]; exact dual_finset_cofg' p hs.toFinset

variable (p) in
theorem dual_fg_cofg' {S : Submodule R M} (hS : S.FG) : (dual p S).CoFG' := by
  obtain ⟨s, rfl⟩ := hS
  simpa using dual_finset_cofg' p s

theorem CoFG.cofg' {S : Submodule R N} (hS : S.CoFG p) : S.CoFG' := by
  obtain ⟨s, rfl⟩ := hS.exists_finset_dual
  exact dual_finset_cofg' p s

end IsNoetherianRing

section Field

variable {R : Type*} [Field R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}

theorem CoFG'.exists_finset_dual {S : Submodule R M} (hS : S.CoFG') :
    ∃ s : Finset (Dual R M), dual .id s = S := by classical
  let Q := M ⧸ S
  obtain ⟨s, ⟨b⟩⟩ := Module.Basis.exists_basis R Q
  have h := Module.Finite.finite_basis b
  let f := b.equivFun
  let g := mkQ S
  unfold Q at *
  have hh : ker g = S := ker_mkQ S
  simp [dual_ker_pi']
  rw [← hh]

  sorry

theorem CoFG'.cofg {S : Submodule R M} (hS : S.CoFG') : S.CoFG .id := by
  sorry

end Field


end CommSemiring

end Submodule
