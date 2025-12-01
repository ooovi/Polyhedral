/-
Copyright (c) 2025 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.LinearAlgebra.SesquilinearForm.Basic

import Polyhedral.Mathlib.Algebra.Module.Submodule.FGDual

open Function Module LinearMap
open Submodule hiding span dual

variable {R M N : Type*}

namespace Submodule

variable {R : Type*} [Field R]
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}
variable {S T : Submodule R M}

-- variable (p) in
-- private abbrev auxSet (S : Submodule R M) (w : N) (s₀ : M) :=
--     {p s w • s₀ - p s₀ w • s | (s ∈ S)}

-- private lemma dual_span_eq_dual_auxSet
--     (S : Submodule R M) (w : N) (s₀ : M) (hs₀ : s₀ ∈ S) (hw : p s₀ w ≠ 0) :
--     dual p S ⊔ span R {w} = dual p (auxSet p S w s₀) := by
--   ext x
--   simp [mem_sup, mem_span_singleton]
--   constructor
--   · intro ⟨y, hy, c, hc⟩ t ht
--     simp only [← hc, map_add, ← hy hs₀, map_smul, smul_eq_mul, zero_add, ← hy ht]
--     ring
--   · intro h
--     simp_rw [mul_comm] at h
--     simp only [← smul_eq_mul] at h
--     simp only [← map_smul] at h
--     simp only [← map_sub] at h
--     use -(p s₀ w)⁻¹ • (p s₀ x • w - p s₀ w • x)
--     constructor
--     · intro x hx
--       simp [map_smul, ← h x hx]
--     · use (p s₀ w)⁻¹ * p s₀ x
--       simp only [smul_sub, neg_smul, sub_neg_eq_add]
--       repeat rw [← smul_assoc, smul_eq_mul]
--       simp [inv_mul_cancel₀ hw]

-- variable [Fact (Injective p)] in
-- private lemma auxSet_eq_inf_dual (S : Submodule R M) (w : N) (s₀ : M) (h : p s₀ w ≠ 0) :
--     auxSet p S w s₀ = S ⊓ dual p.flip {w} :=
--   sorry

-- variable (p) [Fact (Injective p)] in
-- lemma dual_sup_singleton_dual_inf_dual_singleton (hS : S.IsDualClosed p) (w : N) :
--     dual p S ⊔ span R {w} = dual p (S ∩ dual p.flip {w}) := by
--   by_cases hw : w ∈ dual p S
--   · rw [← span_eq (dual p S), ← span_union, ← hS]
--     simp [← coe_inf, ← dual_union, hw]
--   simp only [mem_dual, SetLike.mem_coe, not_forall] at hw
--   obtain ⟨s₀, hsS₀, hs₀⟩ := hw
--   push_neg at hs₀
--   rw [dual_span_eq_dual_auxSet S w s₀ hsS₀ hs₀.symm,
--     auxSet_eq_inf_dual S w s₀ hs₀.symm, coe_inf]

-- variable (p) in
-- lemma IsDualClosed.sup_span_singleton (hS : S.IsDualClosed p) (w : M) :
--     (S ⊔ span R {w}).IsDualClosed p := by
--   ---- dealing withe the case w ∈ S
--   by_cases hw : w ∈ S
--   · rw [← span_eq S, ← span_union]
--     simpa [hw]
--   ---- identifying a suitable φ
--   have hΦ:= hS.def
--   set Φ := dual p S
--   rw [← hΦ] at hw
--   simp at hw
--   obtain ⟨φ, hφΦ, hφ⟩ := hw
--   push_neg at hφ
--   rw [← flip_apply] at hφ
--   rw [← hS]
--   rw [dual_span_eq_dual_auxSet (dual p S) w φ hφΦ hφ.symm]
--   refine dual_IsDualClosed _ _

private lemma dual_inf_dual_singleton_dual_sup_singleton (hS : S.IsDualClosed p) (w : N) :
    dual p (S ∩ dual p.flip {w}) = dual p S ⊔ span R {w} := by
  by_cases hw : w ∈ dual p S
  · rw [← span_eq (dual p S), ← span_union, ← hS]
    simp [← coe_inf, ← dual_union, hw]
  simp only [mem_dual, SetLike.mem_coe, not_forall] at hw
  obtain ⟨s₀, hsS₀, hs₀⟩ := hw
  push_neg at hs₀
  ----
  /- The next line is the main trick: `T` is the generating set that will
    appear on both sides on the identity as shown in h₁ and h₂:
     * dual p T = dual p S ⊔ span R {w}
     * span R T = S ⊓ dual p.flip {w}
  -/
  let T := {p s w • s₀ - p s₀ w • s | (s ∈ S)}
  have h₁ : dual p S ⊔ span R {w} = dual p T := by
    ext x
    simp [T, mem_sup, mem_span_singleton]
    constructor
    · intro ⟨y, hy, c, hc⟩ t ht
      simp only [← hc, map_add, ← hy hsS₀, map_smul, smul_eq_mul, zero_add, ← hy ht]
      ring
    · intro h
      simp_rw [mul_comm] at h
      simp only [← smul_eq_mul] at h
      simp only [← map_smul] at h
      simp only [← map_sub] at h
      use -(p s₀ w)⁻¹ • (p s₀ x • w - p s₀ w • x)
      constructor
      · intro x hx
        simp [map_smul, ← h x hx]
      · use (p s₀ w)⁻¹ * p s₀ x
        simp only [smul_sub, neg_smul, sub_neg_eq_add]
        repeat rw [← smul_assoc, smul_eq_mul]
        simp [inv_mul_cancel₀ hs₀.symm]
  have h₂ : T = S ⊓ dual p.flip {w} := by
    rw [le_antisymm_iff]
    constructor
    · intro x ⟨y, hy, h⟩
      rw [← h]
      constructor
      · exact sub_mem (S.smul_mem _ hsS₀) (S.smul_mem _ hy)
      · simp [mul_comm, sub_self]
    · unfold T
      intro x ⟨hxS, hx⟩
      simp at hxS hx
      rw [← span_eq S] at hxS
      rw [← Set.insert_eq_of_mem hsS₀] at hxS
      rw [span_insert] at hxS
      simp [mem_sup] at hxS
      simp [mem_span_singleton] at hxS
      obtain ⟨c, t, ht, rfl⟩ := hxS
      simp at hx
      simp
      by_cases hc : c = 0
      · rw [hc] at ⊢ hx
        simp at ⊢ hx
        use -((p s₀) w)⁻¹ • t
        simp
        constructor
        · exact smul_mem S _ ht
        rw [← hx]
        simp
        rw [← smul_assoc]
        simp
        rw [mul_comm]
        rw [inv_mul_cancel₀ hs₀.symm]
        simp
      use (c * (p t w)⁻¹) • t
      constructor
      · exact S.smul_mem _ ht
      rw [← smul_assoc]
      simp
      nth_rw 3 [mul_comm]
      nth_rw 4 [mul_comm]
      nth_rw 2 [mul_assoc]
      have hx := neg_eq_of_add_eq_zero_left hx.symm
      rw [← hx]
      simp
      have h : p t w ≠ 0 := by
        by_contra h
        rw [h] at hx
        simp at hx
        cases hx
        case inl h => contradiction
        case inr h => exact hs₀ h.symm
      rw [mul_assoc]
      rw [inv_mul_cancel₀ h]
      simp
  rw [h₁, h₂, coe_inf]

-- private lemma dual_inf_dual_singleton_dual_sup_singleton' (hS : S.IsDualClosed p) (w : N) :
--     dual p (S ∩ dual p.flip {w}) = dual p S ⊔ span R {w} := by
--   -- by_cases hw : w ∈ dual p S
--   -- · rw [← span_eq (dual p S), ← span_union, ← hS]
--   --   simp [← coe_inf, ← dual_union, hw]
--   -- simp only [mem_dual, SetLike.mem_coe, not_forall] at hw
--   -- obtain ⟨s₀, hsS₀, hs₀⟩ := hw
--   -- push_neg at hs₀
--   ----
--   let T := { p s w • t - p t w • s | (s ∈ S) (t ∈ S) }
--   have h₁ : dual p S ⊔ span R {w} = dual p T := by
--     ext x
--     simp [T, mem_sup, mem_span_singleton]
--     constructor
--     · intro ⟨y, hy, c, hc⟩ z s hs t ht rfl
--       simpa [← hc, ← hy ht, ← hy hs] using by ring
--     · intro h
--       replace h : ∀ y ∈ S, ∀ z ∈ S, 0 = (p y) w * (p z) x - (p z) w * (p y) x := by
--         intro y hy z hz
--         simpa using @h ((p y) w • z - (p z) w • y) y hy z hz
--       ---
--       simp_rw [mul_comm] at h
--       simp only [← smul_eq_mul] at h
--       simp only [← map_smul] at h
--       simp only [← map_sub] at h
--       use -(p s₀ w)⁻¹ • (p s₀ x • w - p s₀ w • x)
--       constructor
--       · intro x hx
--         simp [map_smul, ← h x hx]
--       · use (p s₀ w)⁻¹ * p s₀ x
--         simp only [smul_sub, neg_smul, sub_neg_eq_add]
--         repeat rw [← smul_assoc, smul_eq_mul]
--         simp [inv_mul_cancel₀ hs₀.symm]
--   have h₂ : T = S ⊓ dual p.flip {w} := by
--     rw [le_antisymm_iff]
--     constructor
--     · intro x ⟨s, hs, t, ht, h⟩
--       rw [← h]
--       constructor
--       · exact sub_mem (S.smul_mem _ ht) (S.smul_mem _ hs)
--       · simp [mul_comm, sub_self]
--     · unfold T
--       intro x ⟨hxS, hx⟩
--       simp at hxS hx
--       rw [← span_eq S] at hxS
--       rw [← Set.insert_eq_of_mem hsS₀] at hxS
--       rw [span_insert] at hxS
--       simp [mem_sup] at hxS
--       simp [mem_span_singleton] at hxS
--       obtain ⟨c, t, ht, rfl⟩ := hxS
--       simp at hx
--       simp
--       by_cases hc : c = 0
--       · rw [hc] at ⊢ hx
--         simp at ⊢ hx
--         use -((p s₀) w)⁻¹ • t
--         simp
--         constructor
--         · exact smul_mem S _ ht
--         rw [← hx]
--         simp
--         rw [← smul_assoc]
--         simp
--         rw [mul_comm]
--         rw [inv_mul_cancel₀ hs₀.symm]
--         simp
--       use (c * (p t w)⁻¹) • t
--       constructor
--       · exact S.smul_mem _ ht
--       rw [← smul_assoc]
--       simp
--       nth_rw 3 [mul_comm]
--       nth_rw 4 [mul_comm]
--       nth_rw 2 [mul_assoc]
--       have hx := neg_eq_of_add_eq_zero_left hx.symm
--       rw [← hx]
--       simp
--       have h : p t w ≠ 0 := by
--         by_contra h
--         rw [h] at hx
--         simp at hx
--         cases hx
--         case inl h => contradiction
--         case inr h => exact hs₀ h.symm
--       rw [mul_assoc]
--       rw [inv_mul_cancel₀ h]
--       simp
--   rw [h₁, h₂, coe_inf]

lemma dual_inf_dual_finite_dual_sup_finite (hS : S.IsDualClosed p) (s : Finset N) :
    dual p (S ∩ dual p.flip s) = dual p S ⊔ span R s := by classical
  induction s using Finset.induction with
  | empty => simp
  | insert w s hws hs =>
    rw [Finset.coe_insert, span_insert, dual_insert, ← coe_inf]
    nth_rw 2 [sup_comm, inf_comm]
    rw [← sup_assoc, ← hs, ← inf_assoc]
    simpa using dual_inf_dual_singleton_dual_sup_singleton
      (inf_isDualClosed hS <| dual_IsDualClosed p.flip s) w

lemma dual_inf_dual_fg_dual_sup_fg (hS : S.IsDualClosed p) {T : Submodule R N} (hT : T.FG) :
    dual p (S ∩ dual p.flip T) = dual p S ⊔ T := by
  obtain ⟨s, rfl⟩ := hT
  simpa using dual_inf_dual_finite_dual_sup_finite hS s

-- variable (p) in
-- lemma IsDualClosed.sup_span_singleton (hS : S.IsDualClosed p) (w : M) :
--     (S ⊔ span R {w}).IsDualClosed p := by
--   rw [← hS, ← dual_inf_dual_singleton_dual_sup_singleton (dual_IsDualClosed p _) w]
--   exact dual_IsDualClosed _ _

variable (p) in
lemma IsDualClosed.sup_span_finite (hS : S.IsDualClosed p) (s : Finset M) :
    (S ⊔ span R s).IsDualClosed p := by
  rw [← hS, ← dual_inf_dual_finite_dual_sup_finite (dual_IsDualClosed p _) s]
  exact dual_IsDualClosed _ _

variable (p) in
lemma IsDualClosed.sup_fg (hS : S.IsDualClosed p) (hT : T.FG) :
    (S ⊔ T).IsDualClosed p := by
  obtain ⟨t, rfl⟩ := hT
  exact sup_span_finite p hS t

-- variable (p) [Fact p.flip.IsFaithfulPair] in -- [Fact (Injective p)] in
-- lemma IsDualClosed.singleton (w : M) : (span R {w}).IsDualClosed p := by
--   simpa using sup_span_finite p isDualClosed_bot {w}

variable [Fact p.SeparatingLeft] in -- [Fact (Injective p)] in
lemma IsDualClosed.finite (s : Finset M) : (span R s).IsDualClosed p := by
  simpa using sup_span_finite p isDualClosed_bot s

variable [Fact p.SeparatingLeft] in
@[simp] lemma dual_flip_dual_finite (s : Finset M) : dual p.flip (dual p s) = span R s := by
  nth_rw 2 [← dual_span]
  exact IsDualClosed.finite s

variable [Fact p.SeparatingRight] in
@[simp] lemma dual_dual_flip_finite (s : Finset N) : dual p (dual p.flip s) = span R s :=
    dual_flip_dual_finite _

variable (p) [Fact p.SeparatingLeft] in -- [Fact (Injective p)] in
lemma FG.isDualClosed (hS : S.FG) : S.IsDualClosed p := by
  simpa using IsDualClosed.sup_fg p isDualClosed_bot hS

-- variable (p) [Fact p.IsFaithfulPair] in -- [Fact (Injective p)] in
-- lemma FG.isDualClosed_flip {S : Submodule R N} (hS : S.FG) : S.IsDualClosed p.flip :=
--   FG.isDualClosed p.flip hS

variable (p) [Fact p.SeparatingLeft] in
@[simp] lemma FG.dual_flip_dual (hS : S.FG) : dual p.flip (dual p S) = S := by
  exact FG.isDualClosed p hS

variable (p) [Fact p.SeparatingRight] in
@[simp] lemma FG.dual_dual_flip {S : Submodule R N} (hS : S.FG) : dual p (dual p.flip S) = S :=
    dual_flip_dual _ hS

variable [Fact p.SeparatingLeft] in
lemma FGDual.dual_fg {S : Submodule R N} (hS : S.FGDual p) : FG (dual p.flip S) := by
  obtain ⟨T, hfg, rfl⟩ := hS.exists_fg_dual
  simp [hfg]

-- variable [Fact p.IsFaithfulPair] in
-- lemma FGDual.dual_fg (hS : S.FGDual p.flip) : FG (dual p S) := dual_flip_fg hS

variable [Fact p.SeparatingRight] in
lemma dual_inf_dual_sup_fgdual (hS : S.IsDualClosed p) (hT : T.FGDual p.flip) :
    dual p (S ∩ T) = dual p S ⊔ dual p T := by
  obtain ⟨s, rfl⟩ := hT
  simpa only [dual_dual_flip_finite] using dual_inf_dual_finite_dual_sup_finite hS s

variable [Fact p.SeparatingRight] in
lemma FGDual.dual_inf_dual_sup_dual (hS : S.FGDual p.flip) (hT : T.FGDual p.flip) :
    dual p (S ∩ T) = dual p S ⊔ dual p T := by
  exact dual_inf_dual_sup_fgdual hS.isDualClosed hT

-- less assumptions possible?
variable [Fact p.Nondegenerate] in
lemma dual_fg_inf_fgdual_dual_sup_dual (hS : S.FG) (hT : T.FGDual p.flip) :
    dual p (S ∩ T) = dual p S ⊔ dual p T := by
  exact dual_inf_dual_sup_fgdual (FG.isDualClosed p hS) hT




---

variable [Fact p.Nondegenerate] in
lemma sup_fgdual_fg {S T : Submodule R N} (hS : S.FGDual p) (hT : T.FG) : (S ⊔ T).FGDual p := by
  rw [← hS.isDualClosed_flip]
  rw [← FG.isDualClosed p.flip hT] -- this line should not need IsFaithfulPair
  simp only [flip_flip]
  rw [← dual_fg_inf_fgdual_dual_sup_dual]
  · rw [← coe_inf]
    exact fgdual_of_fg p (inf_fg_left hS.dual_fg _)
  · exact hS.dual_fg
  · exact fgdual_of_fg p.flip hT


lemma FGDual.of_fgdual_le {S T : Submodule R N} (hS : S.FGDual p) (hST : S ≤ T) :
    T.FGDual p := by
  have h : ∃ S' : Submodule R N, S ⊓ S' = ⊥ ∧ S ⊔ S' = T := sorry
  obtain ⟨S', hbot, hT⟩ := h

  sorry

  /- Proof idea:
    * use that S ⊓ T is CoFG, and S ⊓ T ≤ S ⊔ T. Hence restrict of S ⊓ T is CoFG in S ⊔ T.
    * Choose a complement R of S ⊓ T in S ⊔ T. Hence S ⊔ T = (S ⊓ T) ⊔ R.
    * R is FG because complements of CoFG submodules are FG.
    * S ⊓ T is FGDual, and R is FG, hence by `sup_fgdual_fg` their union S ⊔ T is FGDual.
  -/
variable [Fact p.Nondegenerate] in -- is Nondegenerate necessary?
lemma sup_fgdual {S T : Submodule R N} (hS : S.FGDual p) (hT : T.FGDual p) :
    (S ⊔ T).FGDual p := by
  have h := CoFG.restrict (S ⊔ T) (inf_cofg hS.cofg hT.cofg)
  obtain ⟨U, hUST⟩ := exists_isCompl (restrict (S ⊔ T) (S ⊓ T))
  have hU := CoFG.isCompl_fg hUST h
  have H := congrArg embed <| hUST.codisjoint.eq_top
  simp only [embed_sup, embed_restrict, inf_right_le_sup_right, inf_of_le_right, embed_top] at H
  simpa [← H] using sup_fgdual_fg (inf_fgdual hS hT) (embed_fg_of_fg hU)

variable [Fact p.Nondegenerate] in
lemma FG.dual_inf_dual_sup_dual (hS : S.FG) (hT : T.FG) :
    dual p (S ∩ T) = dual p S ⊔ dual p T := by
  rw [← coe_inf]
  nth_rw 1 [← FG.isDualClosed p hS, ← FG.isDualClosed p hT]
  rw [← dual_union, ← dual_sup, FGDual.dual_dual_flip]
  exact sup_fgdual (FG.dual_fgdual p hS) (FG.dual_fgdual p hT)

end Submodule
