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

lemma CoFG'.sup {S : Submodule R M} (hS : S.CoFG') (T : Submodule R M) : (S ⊔ T).CoFG'
  := Finite.equiv (quotientQuotientEquivQuotientSup S T)

alias sup_cofg' := CoFG'.sup

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

lemma range_fg_iff_ker_cofg' (f : M →ₗ[R] N) : (range f).FG ↔ (ker f).CoFG' := by
  rw [← Finite.iff_fg]
  exact Module.Finite.equiv_iff <| f.quotKerEquivRange.symm

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
  let φ := (mkQ S).prod (mkQ T)
  let S' := Submodule.subtype (range φ)
  rw [← ker_prod_mkQ_eq_inf S T]
  have h : Function.Injective S' := subtype_injective _
  exact (Module.Finite.of_injective _ h).equiv φ.quotKerEquivRange.symm

theorem sInf_cofg' {s : Finset (Submodule R M)} (hs : ∀ S ∈ s, S.CoFG') :
    (sInf (s : Set (Submodule R M))).CoFG' := by classical
  induction s using Finset.induction with
  | empty => simpa using cofg_top'
  | insert w s hws hs' =>
    simp only [Finset.mem_insert, forall_eq_or_imp, Finset.coe_insert, sInf_insert] at *
    exact inf_cofg' hs.1 (hs' hs.2)

theorem sInf_cofg'' {s : Set (Submodule R M)} (hs : s.Finite) (hcofg : ∀ S ∈ s, S.CoFG') :
    (sInf s).CoFG' := by
  rw [← Set.Finite.coe_toFinset hs]
  exact sInf_cofg' <| fun S hS => hcofg S <| (Set.Finite.mem_toFinset hs).mp hS

variable {R : Type*} [CommRing R] [IsNoetherianRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}

variable (p) in
theorem dual_singleton_cofg' (x : M) : (dual p {x}).CoFG' := by
  rw [dual_singleton, ← range_fg_iff_ker_cofg']
  exact IsNoetherian.noetherian _

variable (p) in
theorem dual_finset_cofg' {s : Set M} (hs : s.Finite) : (dual p s).CoFG' := by
  rw [dual_eq_Inf_dual_singleton]
  rw [← sInf_image]
  refine sInf_cofg'' (Set.Finite.image _ hs) ?_
  simp only [Set.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  exact fun S _ => dual_singleton_cofg' p S

theorem dual_finset_cofg'' (s : Finset M) : (dual p s).CoFG'
    := dual_finset_cofg' p s.finite_toSet

theorem CoFG.cofg' {S : Submodule R N} (hS : S.CoFG p) : S.CoFG' := by
  obtain ⟨s, rfl⟩ := hS.exists_finset_dual
  exact dual_finset_cofg'' s

end IsNoetherianRing

section Field

variable {R : Type*} [Field R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}

#check Submodule.dualAnnihilator

variable [Fact p.IsFaithfulPair] in
theorem CoFG'.exists_finset_dual {S : Submodule R N} (hS : S.CoFG') :
    ∃ s : Finset M, dual p s = S := by

  sorry

variable [IsNoetherianRing R] [Fact p.IsFaithfulPair] in
theorem CoFG'.cofg {S : Submodule R N} (hS : S.CoFG') : S.CoFG p := by
  sorry

end Field


end CommSemiring

end Submodule
