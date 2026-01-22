/-
Copyright (c) 2025 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/

import Polyhedral.PR.FGDual.FGDual_PR

open Function Module LinearMap
open Submodule hiding span dual

namespace Submodule

variable {R : Type*} [Field R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}
variable {S T : Submodule R M}

/- Better: this version allows an explicit computation for generating sets of duals
  in case this will be necessary at some point. -/

variable (p) in
private def auxGenSet (s : Set M) (w : N) : Set M :=
  {x ∈ s | p x w = 0} ∪ {p r w • t - p t w • r | (t ∈ s) (r ∈ s)}

lemma auxGenSet_of_mem_dual (s : Set M) (w : N) (hw : w ∈ dual p s) :
    auxGenSet p s w = span R s := by
  sorry

lemma auxGenSet_of_not_mem_dual (s : Set M) (w : N) (hw : w ∉ dual p s) :
    auxGenSet p s w = {p r w • t - p t w • r | (t ∈ s) (r ∈ s)} := by
  sorry

variable (p) in
private lemma dual_auxGenSet_eq_dual_sup_span_singleton (s : Set M) (w : N) :
    dual p (auxGenSet p s w) = dual p s ⊔ span R {w} := by
  sorry

private lemma span_auxGenSet_eq_span_inf_dual_singleton (s : Set M) (w : N) :
    span R (auxGenSet p s w) = span R s ⊓ dual p.flip {w} := by
  sorry

variable (p) in
private lemma dual_inf_dual_singleton_dual_sup_singleton' (s : Set M) (w : N) :
    dual p (span R s ⊓ dual p.flip {w} : Submodule R M) = dual p s ⊔ span R {w} := by
  simp [← dual_auxGenSet_eq_dual_sup_span_singleton, ← span_auxGenSet_eq_span_inf_dual_singleton]

variable (p) in
private lemma dual_inf_dual_singleton_dual_sup_singleton'' (w : N) :
    dual p (S ∩ dual p.flip {w}) = dual p S ⊔ span R {w} := by
  simpa using dual_inf_dual_singleton_dual_sup_singleton' p S w

-- --------------

private lemma dual_inf_dual_singleton_dual_sup_singleton (hS : S.DualClosed p) (w : N) :
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

----

lemma dual_inf_dual_finite_dual_sup_finite (hS : S.DualClosed p) (s : Finset N) :
    dual p (S ∩ dual p.flip s) = dual p S ⊔ span R s := by classical
  induction s using Finset.induction with
  | empty => simp
  | insert w s hws hs =>
    rw [Finset.coe_insert, span_insert, dual_insert, ← coe_inf]
    nth_rw 2 [sup_comm, inf_comm]
    rw [← sup_assoc, ← hs, ← inf_assoc]
    simpa using dual_inf_dual_singleton_dual_sup_singleton
      (hS.inf <| DualClosed.of_dual p.flip s) w

lemma dual_inf_dual_finite_dual_sup_finite' (hS : S.DualClosed p) {s : Set N} (hs : s.Finite) :
    dual p (S ∩ dual p.flip s) = dual p S ⊔ span R s := by
  simpa using dual_inf_dual_finite_dual_sup_finite hS hs.toFinset

lemma dual_inf_dual_fg_dual_sup_fg (hS : S.DualClosed p) {T : Submodule R N} (hT : T.FG) :
    dual p (S ∩ dual p.flip T) = dual p S ⊔ T := by
  obtain ⟨s, rfl⟩ := hT
  simpa using dual_inf_dual_finite_dual_sup_finite hS s


-- ## DUAL CLOSED

-- variable (p) in
-- lemma DualClosed.sup_span_singleton (hS : S.DualClosed p) (w : M) :
--     (S ⊔ span R {w}).DualClosed p := by
--   rw [← hS, ← dual_inf_dual_singleton_dual_sup_singleton (dual_dualClosed p _) w]
--   exact dual_dualClosed _ _

variable (p) in
lemma DualClosed.sup_span_finite (hS : S.DualClosed p) (s : Finset M) :
    (S ⊔ span R s).DualClosed p := by
  rw [← hS, ← dual_inf_dual_finite_dual_sup_finite (DualClosed.of_dual p _) s]
  exact DualClosed.of_dual _ _

variable (p) in
lemma DualClosed.sup_fg (hS : S.DualClosed p) (hT : T.FG) :
    (S ⊔ T).DualClosed p := by
  obtain ⟨t, rfl⟩ := hT
  exact sup_span_finite p hS t

-- variable (p) [Fact p.flip.IsFaithfulPair] in -- [Fact (Injective p)] in
-- lemma DualClosed.singleton (w : M) : (span R {w}).DualClosed p := by
--   simpa using sup_span_finite p dualClosed_bot {w}

variable [Fact p.SeparatingLeft] in -- [Fact (Injective p)] in
lemma DualClosed.finite (s : Finset M) : (span R s).DualClosed p := by
  simpa using sup_span_finite p bot s

variable [Fact p.SeparatingLeft] in
@[simp] lemma dual_flip_dual_finite (s : Finset M) : dual p.flip (dual p s) = span R s := by
  nth_rw 2 [← dual_span]
  exact DualClosed.finite s

variable [Fact p.SeparatingRight] in
@[simp] lemma dual_dual_flip_finite (s : Finset N) : dual p (dual p.flip s) = span R s :=
    dual_flip_dual_finite _

variable (p) [Fact p.SeparatingLeft] in
/-- FG cones are dual closed. -/
lemma FG.dualClosed (hS : S.FG) : S.DualClosed p := by
  simpa using DualClosed.sup_fg p DualClosed.bot hS

variable (p) in
lemma FG.dualClosed_of_ker_le (hS : S.FG) (h : ker p ≤ S) : S.DualClosed p := by
  simpa [h] using DualClosed.sup_fg p DualClosed.ker hS

-- variable (p) [Fact p.IsFaithfulPair] in -- [Fact (Injective p)] in
-- lemma FG.dualClosed_flip {S : Submodule R N} (hS : S.FG) : S.DualClosed p.flip :=
--   FG.dualClosed p.flip hS

variable (p) [Fact p.SeparatingLeft] in
@[simp] lemma FG.dual_flip_dual (hS : S.FG) : dual p.flip (dual p S) = S := by
  exact FG.dualClosed p hS

variable (p) [Fact p.SeparatingRight] in
@[simp] lemma FG.dual_dual_flip {S : Submodule R N} (hS : S.FG) : dual p (dual p.flip S) = S :=
    dual_flip_dual _ hS

variable (p) in
lemma FG.dual_flip_dual_sup_ker (hS : S.FG) : dual p.flip (dual p S) = S ⊔ ker p := by
  nth_rw 2 [← dual_union_ker, ← dual_span]
  simpa [sup_comm] using DualClosed.ker.sup_fg p hS

variable (p) in
lemma FG.dual_dual_flip_sup_ker {S : Submodule R N} (hS : S.FG) :
    dual p (dual p.flip S) = S ⊔ ker p.flip := dual_flip_dual_sup_ker p.flip hS

variable (p) in
lemma FG.sup_ker_dualClosed (hS : S.FG) : (S ⊔ ker p).DualClosed p := by
  simpa [DualClosed, dual_sup, dual_union_ker] using dual_flip_dual_sup_ker p hS

variable [Fact p.SeparatingLeft] in
lemma FGDual.dual_fg {S : Submodule R N} (hS : S.FGDual p) : FG (dual p.flip S) := by
  obtain ⟨T, hfg, rfl⟩ := hS.exists_fg_dual
  simp [hfg]

lemma FGDual.dual_fg_sup_ker {S : Submodule R N} (hS : S.FGDual p) :
    ∃ T : Submodule R M, T.FG ∧ T ⊔ ker p = dual p.flip S := by
  obtain ⟨T, hfg, rfl⟩ := hS.exists_fg_dual
  use T
  simpa [hfg, Eq.comm] using hfg.dual_flip_dual_sup_ker p

----- vvvvvv experimental
-- TODO: move to correct file

lemma mkQ_eq_zero_of_mem {S : Submodule R M} {x : M} (hx : x ∈ S) : S.mkQ x = 0 := by
  simpa only [← S.ker_mkQ, mem_ker] using hx

def dualAnnihilator_linearEquiv_dual_quot (S : Submodule R M) :
    S.dualAnnihilator ≃ₗ[R] Dual R (M ⧸ S)  where
  toFun f := S.liftQ f.1 (le_ker_of_mem_dualAnnihilator f.2)
  invFun f := ⟨f ∘ₗ S.mkQ, by
    simp only [mem_dualAnnihilator, coe_comp, Function.comp_apply]
    exact fun _ h => by simp [mkQ_eq_zero_of_mem h]⟩
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp
  left_inv _ := by ext; simp
  right_inv _ := by ext; simp

-- TODO: this is an equivalence when p is surjective, I think; see
--  `dualAnnihilator_linearEquiv_dual_quot` above.
def dual_linearMap_dual_quot (S : Submodule R M) :
    dual p S →ₗ[R] Dual R (M ⧸ S)  where
  toFun f := S.liftQ (p.flip f.1) <| le_ker_of_mem_dualAnnihilator (by
    simpa using fun _ hx => (f.2 hx).symm )
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

-- #check Subspace.quotDualEquivAnnihilator -- this is similar to the below, but restricted to finite dim
-- def dual_eval_linearEquiv_dual_quot (S : Submodule R M) :
--     dual (Dual.eval R M) S ≃ₗ[R] Dual R (M ⧸ S)  where
--   toFun f := S.liftQ f.1 (subset_ker_of_mem_dual f.2)
--   invFun f := ⟨f ∘ₗ S.mkQ, by
--     simp only [mem_dual, SetLike.mem_coe, Dual.eval_apply, coe_comp, Function.comp_apply]
--     exact fun _ h => by simp [mkQ_eq_zero_of_mem h]⟩
--   map_add' _ _ := by ext; simp
--   map_smul' _ _ := by ext; simp
--   left_inv _ := by ext; simp
--   right_inv _ := by ext; simp

-- lemma CoFG.dual_fg' {S : Submodule R M} (hS : S.CoFG) : (dual (Dual.eval R M) S).FG := by
--   rw [← fg_top]
--   refine fg_of_linearEquiv S.dual_eval_linearEquiv_dual_quot ?_
--   simpa [← finite_def, Module.finite_dual_iff] using hS

lemma CoFG.dualAnnihilator_fg {S : Submodule R M} (hS : S.CoFG) : FG S.dualAnnihilator := by
  rw [← fg_top]
  refine fg_of_linearEquiv S.dualAnnihilator_linearEquiv_dual_quot ?_
  simpa [← finite_def, Module.finite_dual_iff] using hS

variable (p) [Fact p.SeparatingRight] in
lemma CoFG.dual_fg {S : Submodule R M} (hS : S.CoFG) : (dual p S).FG := by
  apply fg_of_fg_map_injective p.flip SeparatingRight.injective
  rw [S.dual_comap_dualAnnihilator, map_comap_eq]
  exact inf_fg_right _ hS.dualAnnihilator_fg

/- Not true!! Consider M = N the space finitely supported sequences. Let S be the subspace of
    sequences with sum x_i = 0. Then S^* = bot and S^** = top. -/
example {S : Submodule R M} (hS : S.CoFG) : (S ⊔ ker p).DualClosed p := sorry

-- ChatGPT says this is true and gives a proof.
-- https://chatgpt.com/c/6934b9d9-d210-832c-b723-a0d0adeb0749
variable (p) in
lemma CoFG._exists_fg_sup_ker_eq_dual {S : Submodule R M} (hS : S.CoFG) :
    ∃ T : Submodule R N, T.FG ∧ T ⊔ ker p.flip = dual p S := by
  --have h := hS.fgdual .id
  sorry

theorem CoFG._fgDual_of_dualClosed {S : Submodule R N} (hS : S.CoFG) (hS' : S.DualClosed p.flip) :
    S.FGDual p := by
  obtain ⟨T, hfg, hT⟩ := hS._exists_fg_sup_ker_eq_dual p.flip -- unproven!
  rw [← hS', ← hT, dual_sup, dual_union_ker]
  exact hfg.dual_fgdual _

variable [Fact p.SeparatingLeft] in -- TODO: remove assumption, see above
theorem CoFG.fgDual_of_dualClosed {S : Submodule R N} (hS : S.CoFG) (hS' : S.DualClosed p.flip) :
    S.FGDual p := by
  rw [← hS', flip_flip]
  exact FG.dual_fgdual _ (hS.dual_fg _)

----------- ^^^^^^ experimental

-- variable [Fact p.IsFaithfulPair] in
-- lemma FGDual.dual_fg (hS : S.FGDual p.flip) : FG (dual p S) := dual_flip_fg hS

-- variable [Fact p.SeparatingRight] in
-- private lemma dual_inf_dual_sup_fgdual' (hS : S.DualClosed p) (hT : T.FGDual p.flip) :
--     dual p (S ∩ T) = dual p S ⊔ dual p T := by
--   obtain ⟨s, rfl⟩ := hT
--   simpa only [dual_dual_flip_finite] using dual_inf_dual_finite_dual_sup_finite hS s

-- The proof is slightly longer but we can avoid assumptions about p, see
-- `dual_inf_dual_sup_fgdual'` above.
lemma dual_inf_dual_sup_fgdual (hS : S.DualClosed p) (hT : T.FGDual p.flip) :
    dual p (S ∩ T) = dual p S ⊔ dual p T := by
  obtain ⟨S', hfg, rfl⟩ := hT.exists_fg_dual
  rw [hfg.dual_dual_flip_sup_ker p]
  nth_rw 2 [sup_comm]
  rw [← sup_assoc]
  rw [sup_eq_left.mpr (DualClosed.of_dual p S).ker_le]
  exact dual_inf_dual_fg_dual_sup_fg hS hfg

lemma FGDual.dual_inf_dual_sup_dual (hS : S.FGDual p.flip) (hT : T.FGDual p.flip) :
    dual p (S ∩ T) = dual p S ⊔ dual p T := by
  exact dual_inf_dual_sup_fgdual hS.dualClosed hT

-- less assumptions possible?
-- variable [Fact p.SeparatingLeft] in
-- lemma dual_fg_inf_fgdual_dual_sup_dual' (hS : S.FG) (hT : T.FGDual p.flip) :
--     dual p (S ∩ T) = dual p S ⊔ dual p T := by
--   exact dual_inf_dual_sup_fgdual (hS.dualClosed p) hT

lemma dual_fg_inf_fgdual_dual_sup_dual (hS : S.FG) (hT : T.FGDual p.flip) :
    dual p (S ∩ T) = dual p S ⊔ dual p T := by
  rw [← dual_union_ker, ← coe_inf, ← dual_sup, inf_comm]
  rw [inf_sup_assoc_of_le]
  · rw [inf_comm, coe_inf]
    rw [dual_inf_dual_sup_fgdual (hS.sup_ker_dualClosed p) hT]
    rw [dual_sup, dual_union_ker]
  exact hT.ker_le



variable (p) [Fact p.SeparatingRight] in
/-- For an FG submodule `S`, there exists an FGDual submodule `T` so that `S ⊓ T = ⊥`. -/
lemma FG.exists_fgdual_disjoint {S : Submodule R N} (hS : S.FG) :
    ∃ T : Submodule R N, T.FGDual p ∧ Disjoint S T := by
  obtain ⟨V, hfg, hV⟩ := (hS.dual_cofg p.flip).exists_fg_codisjoint
  use dual p V
  constructor
  · exact hfg.dual_fgdual _
  · rw [← hS.dual_dual_flip p]
    exact disjoint_dual_of_codisjoint p hV


---

private lemma sup_fgdual_fg {S T : Submodule R N} (hS : S.FGDual p) (hT : T.FG) :
    (S ⊔ T).FGDual p := by
  rw [← sup_eq_left.mpr (hS.ker_le)]
  rw [sup_assoc, sup_comm]
  nth_rw 2 [sup_comm]
  rw [← hS.dualClosed_flip]
  rw [← hT.sup_ker_dualClosed p.flip]
  simp only [flip_flip]
  rw [sup_comm]
  rw [← dual_inf_dual_sup_fgdual]
  · rw [← coe_inf]
    obtain ⟨S', hfg, hS'⟩ := hS.dual_fg_sup_ker
    rw [← hS', inf_comm, ← inf_sup_assoc_of_le]
    · rw [dual_sup, dual_union_ker]
      exact FGDual.of_dual_fg p (inf_fg_right _ hfg)
    exact ker_le_dual_flip _
  · exact DualClosed.of_dual _ _
  · simpa [dual_sup, dual_union_ker] using FGDual.of_dual_fg _ hT

-- variable [Fact p.Nondegenerate] in
-- private lemma sup_fgdual_fg' {S T : Submodule R N} (hS : S.FGDual p) (hT : T.FG) :
--     (S ⊔ T).FGDual p := by
--   rw [← hS.dualClosed_flip]
--   rw [← hT.dualClosed p.flip] -- this line should not need IsFaithfulPair
--   simp only [flip_flip]
--   rw [← dual_fg_inf_fgdual_dual_sup_dual]
--   · rw [← coe_inf]
--     exact fgdual_of_fg p (inf_fg_left hS.dual_fg _)
--   · exact hS.dual_fg
--   · exact fgdual_of_fg p.flip hT

  /- Proof idea:
    * use that S ⊓ T is CoFG, and S ⊓ T ≤ S ⊔ T. Hence restrict of S ⊓ T is CoFG in S ⊔ T.
    * Choose a complement R of S ⊓ T in S ⊔ T. Hence S ⊔ T = (S ⊓ T) ⊔ R.
    * R is FG because complements of CoFG submodules are FG.
    * S ⊓ T is FGDual, and R is FG, hence by `sup_fgdual_fg` their union S ⊔ T is FGDual.
  -/
/-- The sum of an FGDual submodule with an arbitrary submodule is FGDual. -/
lemma FGDual.sup {S : Submodule R N} (hS : S.FGDual p) (T : Submodule R N) :
    (S ⊔ T).FGDual p := by
  have h := CoFG.restrict (S ⊔ T) hS.cofg
  obtain ⟨U, hUST⟩ := exists_isCompl (restrict (S ⊔ T) S)
  have hU := CoFG.isCompl_fg hUST h
  have H := congrArg embed <| hUST.codisjoint.eq_top
  simp only [embed_sup, embed_restrict, embed_top] at H
  rw [← H]
  simpa using sup_fgdual_fg hS (embed_fg_of_fg hU)

alias sup_fgdual := FGDual.sup

-- TODO: Proving this first (before sup_fgdual) might shorten total proof length.
/-- A submodule that contains an FGDual submodule is itself FGDual. -/
lemma FGDual.of_fgdual_le {S T : Submodule R N} (hS : S.FGDual p) (hST : S ≤ T) :
    T.FGDual p := by
  rw [← sup_eq_right.mpr hST]
  exact hS.sup T

-- def foob'' (S : Submodule R M) : Submodule R (M →ₗ[R] N) where
--   carrier := { f : M →ₗ[R] N | S ≤ ker f }
--   add_mem' := sorry
--   zero_mem' := sorry
--   smul_mem' := sorry
-- instance (S : Submodule R M) : AddCommMonoid { f : M →ₗ[R] N // S ≤ ker f } := sorry
-- instance (S : Submodule R M) : Module R { f : M →ₗ[R] N // S ≤ ker f } := sorry

-- #check liftQ
-- def liftQ_map (S : Submodule R M) : { f : M →ₗ[R] N // S ≤ ker f } →ₗ[R] (M ⧸ S →ₗ[R] N) := sorry

/- NOTE: The assumption `SeparatingLeft` cannot be dropped. Consider submodules with
  S ⊓ T = ⊥, but where S ⊔ ker p = T ⊔ ker p = ⊤. -/
variable [Fact p.SeparatingLeft] in
lemma FG.dual_inf_dual_sup_dual (hS : S.FG) (hT : T.FG) :
    dual p (S ∩ T) = dual p S ⊔ dual p T := by
  rw [← coe_inf]
  nth_rw 1 [← FG.dualClosed p hS, ← FG.dualClosed p hT]
  rw [← dual_union, ← dual_sup, FGDual.dual_dual_flip]
  exact (hS.dual_fgdual p).sup _

variable [Fact p.SeparatingLeft] in -- assumption is unnecessary, adapt the below
lemma FG.dual_inf_dual_sup_dual' (hS : S.FG) (hT : T.DualClosed p) :
    dual p (S ∩ T) = dual p S ⊔ dual p T := by
  rw [← coe_inf]
  nth_rw 1 [← FG.dualClosed p hS, ← hT]
  rw [← dual_union, ← dual_sup, FGDual.dual_dual_flip]
  exact (hS.dual_fgdual p).sup _

-- lemma dual_inf_dual_sup_dual_of_dualClosed'' {S T : Submodule R M}
--     (hS : S.DualClosed p) (hT : T.WeakDualClosed p)
--     (hST : (dual p S ⊔ dual p T).WeakDualClosed p.flip) :
--       dual p (S ∩ T) = dual p S ⊔ dual p T := by
--   rw [← dual_union_ker, ← coe_inf, ← dual_sup, inf_sup_assoc_of_le]
--   · nth_rw 1 [← hS, ← hT, ← flip_flip p]
--     simp only [← dual_union, ← dual_sup, hST, sup_assoc, ker_le_dual, sup_of_le_left]
--   exact hS.ker_le

-- ## TODO: add lemma: in finite dim every submodule is FGDual

end Submodule
