/-
Copyright (c) 2025 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/

import Polyhedral.PR.FGDual.FGDual_PR
import Polyhedral.PR.FGDual.DualClosed_PR

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
private def auxGenSet' (s : Set M) (w : N) : Set M :=
  {x ∈ s | p x w = 0} ∪ {p r w • t - p t w • r | (t ∈ s) (r ∈ s)}

variable (p) in
private lemma dual_auxGenSet_eq_dual_sup_span_singleton' (s : Set M) (w : N) :
    dual p (auxGenSet' p s w) = dual p s ⊔ span R {w} := by
  ext x; simp only [auxGenSet', mem_dual, Set.mem_union, Set.mem_setOf_eq, mem_sup]; constructor
  · intro h; by_cases H : ∀ x ∈ s, p x w = 0
    · exact ⟨x, fun y ys => h <| .inl ⟨ys, H y ys⟩, 0, zero_mem _, by simp⟩
    push_neg at H; obtain ⟨x₀, hx₀s, hx₀⟩ := H
    use -(p x₀ w)⁻¹ • (p x₀ x • w - p x₀ w • x)
    constructor
    · intro y ys
      simp only [neg_smul, map_neg, map_smul, map_sub, smul_eq_mul, zero_eq_neg, mul_eq_zero,
        inv_eq_zero, hx₀, false_or]
      simp [h <| Or.inr <| ⟨x₀, hx₀s, y, ⟨ys, rfl⟩⟩, mul_comm]
    · use ((p x₀ w)⁻¹ * p x₀ x) • w
      exact ⟨mem_span.mpr (fun _ h => smul_mem _ _ (h rfl)), by simp [smul_sub, ← smul_assoc, hx₀]⟩
  · simp_rw [mem_span_singleton]
    rintro ⟨_, hy, _, ⟨_, rfl⟩, rfl⟩ _ (⟨vs, hw⟩ | ⟨_, ht, _, hr, rfl⟩)
    · simp [← hy vs, hw]
    · simp [map_add, map_smul, smul_eq_mul, ← hy ht, ← hy hr, mul_comm]

private lemma span_auxGenSet_eq_inter_dual_singleton' (w : N) :
    auxGenSet' p S w = (S : Set M) ∩ dual p.flip {w} := by
  ext x
  simp only [auxGenSet', SetLike.mem_coe, Set.mem_union, Set.mem_setOf_eq, Set.mem_inter_iff,
    mem_dual, Set.mem_singleton_iff, flip_apply, forall_eq]
  constructor
  · rintro (⟨xS, px⟩ | ⟨r, hr, t, ht, rfl⟩)
    · exact ⟨xS, px.symm⟩
    · exact ⟨S.sub_mem (S.smul_mem _ hr) (S.smul_mem _ ht), by simp [mul_comm]⟩
  · rintro ⟨xS, px⟩
    exact Or.inl ⟨xS, px.symm⟩

variable (p) in
private lemma dual_inf_dual_singleton_dual_sup_singleton'' (s : Set M) (w : N) :
    dual p (span R s ⊓ dual p.flip {w} : Submodule R M) = dual p s ⊔ span R {w} := by
  simp [← dual_auxGenSet_eq_dual_sup_span_singleton', ← span_auxGenSet_eq_inter_dual_singleton',
    auxGenSet', dual_union]
  sorry

variable (p) in
private lemma dual_inf_dual_singleton_dual_sup_singleton''' (w : N) :
    dual p (S ∩ dual p.flip {w}) = dual p S ⊔ span R {w} := by
  simpa using dual_inf_dual_singleton_dual_sup_singleton'' p S w

-- --------------

def auxGenSet (p : M →ₗ[R] N →ₗ[R] R) (S : Submodule R M) (w : N) (s₀ : M) : Set M :=
  {p s w • s₀ - p s₀ w • s | s ∈ S}

private lemma dual_sup_singleton_eq_dual_auxGenSet {w : N} {s₀ : M} (h : s₀ ∈ S)
    (hs₀ : (p s₀) w ≠ 0) :
    dual p S ⊔ span R {w} = dual p (auxGenSet p S w s₀) := by
  ext x; simp [auxGenSet, mem_sup, mem_span_singleton]
  constructor
  · rintro ⟨y, hy, c, rfl⟩ t s
    simp only [map_add, ← hy h, map_smul, smul_eq_mul, zero_add, ← hy s]
    ring
  · intro h
    simp_rw [mul_comm, ← smul_eq_mul, ← map_smul, ← map_sub] at h
    refine ⟨-(p s₀ w)⁻¹ • (p s₀ x • w - p s₀ w • x), fun x hx => by simp [map_smul, ← h x hx],
            (p s₀ w)⁻¹ * p s₀ x, by simp [smul_sub, ← smul_assoc, hs₀]⟩

private lemma auxGenSet_eq_inf_dual {w : N} {s₀ : M} (h : s₀ ∈ S) (hs₀ : (p s₀) w ≠ 0) :
    auxGenSet p S w s₀ = (S : Set M) ∩ dual p.flip {w}:= by
  ext x
  simp only [auxGenSet, Set.mem_setOf_eq, Set.mem_inter_iff, SetLike.mem_coe, mem_dual,
    Set.mem_singleton_iff, flip_apply, forall_eq]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨sub_mem (S.smul_mem _ h) (S.smul_mem _ hy), by simp [mul_comm]⟩
  · intro ⟨hxS, hx⟩
    rw [← span_eq S, ← Set.insert_eq_of_mem h, span_insert, mem_sup] at hxS
    simp only [mem_span_singleton, span_coe_eq_restrictScalars, restrictScalars_self,
      exists_exists_eq_and] at hxS
    obtain ⟨c, t, ht, rfl⟩ := hxS
    by_cases hc : c = 0
    · use -((p s₀) w)⁻¹ • t, smul_mem S _ ht
      simp only [hc, zero_smul, zero_add] at hx
      simp [hc, ← hx, ← smul_assoc, mul_inv_cancel₀ hs₀]
    · use (c * (p t w)⁻¹) • t, S.smul_mem _ ht
      simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul] at hx
      have hx := neg_eq_of_add_eq_zero_left hx.symm
      have h : p t w ≠ 0 := fun hb => (mul_ne_zero hc hs₀) (by simpa [hb] using hx)
      simp only [map_smul, smul_apply, smul_eq_mul, ← smul_assoc, mul_left_comm, ← mul_assoc, ← hx,
        neg_mul, mul_inv_cancel₀ h, neg_smul, one_smul, sub_neg_eq_add, add_left_inj]
      simp [mul_assoc, inv_mul_cancel₀ h]

private lemma dual_inf_dual_singleton_dual_sup_singleton (w : N) :
    dual p (S ∩ dual p.flip {w}) = dual p S ⊔ span R {w} := by
  by_cases hw : w ∈ dual p S
  · have : S ≤ dual p.flip {w} := fun _ hx => by simpa using hw hx
    simp [← coe_inf, this, hw]
  simp only [mem_dual, SetLike.mem_coe, not_forall] at hw
  obtain ⟨s₀, hsS₀, hs₀⟩ := hw
  push_neg at hs₀
  rw [dual_sup_singleton_eq_dual_auxGenSet hsS₀ hs₀.symm, auxGenSet_eq_inf_dual hsS₀ hs₀.symm]


----

lemma dual_inf_dual_eq_dual_sup_of_finset' (s : Set M) (t : Finset N) :
    dual p (span R s ∩ dual p.flip t) = dual p s ⊔ span R t := by classical
  induction t using Finset.induction with
  | empty => simp
  | insert w s hws hs =>
    rw [Finset.coe_insert, span_insert, dual_insert, ← coe_inf]
    nth_rw 2 [sup_comm, inf_comm]
    rw [← sup_assoc, ← hs, ← inf_assoc]
    exact dual_inf_dual_singleton_dual_sup_singleton w

lemma FG.dual_inf_dual_eq_dual_sup' (S : Submodule R M) {T : Submodule R N} (hT : T.FG) :
    dual p (S ∩ dual p.flip T) = dual p S ⊔ T := by classical
  obtain ⟨t, rfl⟩ := hT
  induction t using Finset.induction with
  | empty => simp
  | insert w s hws hs =>
    rw [Finset.coe_insert, dual_span, span_insert, dual_insert, ← coe_inf]
    nth_rw 2 [sup_comm, inf_comm]
    rw [← sup_assoc, ← hs, ← inf_assoc, dual_span]
    exact dual_inf_dual_singleton_dual_sup_singleton w

----------

lemma dual_inf_dual_eq_dual_sup_of_finset {S : Submodule R M} (s : Finset N) :
    dual p (S ∩ dual p.flip s) = dual p S ⊔ span R s := by classical
  induction s using Finset.induction with
  | empty => simp
  | insert w s hws hs =>
    rw [Finset.coe_insert, span_insert, dual_insert, ← coe_inf]
    nth_rw 2 [sup_comm, inf_comm]
    rw [← sup_assoc, ← hs, ← inf_assoc]
    exact dual_inf_dual_singleton_dual_sup_singleton w

-- lemma dual_inf_dual_eq_dual_sup_of_finite {s : Set N} (hs : s.Finite) :
--     dual p (S ∩ dual p.flip s) = dual p S ⊔ span R s := by
--   simpa using dual_inf_dual_eq_dual_sup_of_finset hs.toFinset

lemma FG.dual_inf_dual_eq_dual_sup {T : Submodule R N} (hT : T.FG) :
    dual p (S ∩ dual p.flip T) = dual p S ⊔ T := by
  obtain ⟨s, rfl⟩ := hT
  simpa using dual_inf_dual_eq_dual_sup_of_finset s

-----

-- ## DUAL CLOSED

-- variable (p) in
-- lemma DualClosed.sup_span_singleton (hS : S.DualClosed p) (w : M) :
--     (S ⊔ span R {w}).DualClosed p := by
--   rw [← hS, ← dual_inf_dual_singleton_dual_sup_singleton (dual_dualClosed p _) w]
--   exact dual_dualClosed _ _

variable (p) in
lemma DualClosed.sup_span_finite (hS : S.DualClosed p) (s : Finset M) :
    (S ⊔ span R s).DualClosed p := by
  rw [← hS, ← dual_inf_dual_eq_dual_sup_of_finset s]
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
lemma dual_flip_dual_span_sup_ker (s : Finset M) : dual p.flip (dual p s) = span R s ⊔ ker p := by
  nth_rw 2 [← dual_union_ker, ← dual_span]
  simpa [span_union, sup_comm] using DualClosed.ker.sup_span_finite p s

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
  use T; simpa [hfg, Eq.comm] using hfg.dual_flip_dual_sup_ker p

/-- The sup of an FGDual submodule with an FG submodule is FGDual. -/
private lemma FGDual.sup_fg {S T : Submodule R N} (hS : S.FGDual p) (hT : T.FG) :
    (S ⊔ T).FGDual p := by
  rw [← hS.dual_dual_flip, ← hT.dual_inf_dual_eq_dual_sup]
  obtain ⟨Q, hQfg, hQ⟩ := hS.dual_fg_sup_ker
  rw [← coe_inf, ← hQ, sup_comm, sup_inf_assoc_of_le]
  · rw [sup_comm, dual_sup, dual_union_ker]
    exact FGDual.of_dual_fg _ <| fg_le hQfg inf_le_left
  exact ker_le_dual_flip _

/-- The sup of an FG submodule with an FGDual submodule is FGDual. -/
private lemma FG.sup_fgdual {S T : Submodule R N} (hS : S.FG) (hT : T.FGDual p) :
    (S ⊔ T).FGDual p := by simpa only [sup_comm] using hT.sup_fg hS

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
  simpa using hS.sup_fg (embed_fg_of_fg hU)

-- TODO: This is the more important lemma thanb FGDual.sup. People will complain that sup is
-- unnecessary.
/-- A submodule that contains an FGDual submodule is itself FGDual. -/
lemma FGDual.of_fgdual_le {S T : Submodule R N} (hS : S.FGDual p) (hST : S ≤ T) :
    T.FGDual p := by
  rw [← sup_eq_right.mpr hST]
  exact hS.sup T

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
lemma dual_inf_dual_sup_fgdual (hT : T.FGDual p.flip) :
    dual p (S ∩ T) = dual p S ⊔ dual p T := by
  obtain ⟨S', hfg, rfl⟩ := hT.exists_fg_dual
  rw [hfg.dual_dual_flip_sup_ker p]
  nth_rw 2 [sup_comm]
  rw [← sup_assoc]
  rw [sup_eq_left.mpr (DualClosed.of_dual p S).ker_le]
  exact hfg.dual_inf_dual_eq_dual_sup

lemma FGDual.dual_inf_dual_sup_dual (hT : T.FGDual p.flip) :
    dual p (S ∩ T) = dual p S ⊔ dual p T := by
  exact dual_inf_dual_sup_fgdual hT

-- less assumptions possible?
-- variable [Fact p.SeparatingLeft] in
-- lemma dual_fg_inf_fgdual_dual_sup_dual' (hS : S.FG) (hT : T.FGDual p.flip) :
--     dual p (S ∩ T) = dual p S ⊔ dual p T := by
--   exact dual_inf_dual_sup_fgdual (hS.dualClosed p) hT

lemma dual_fg_inf_fgdual_dual_sup_dual (hT : T.FGDual p.flip) :
    dual p (S ∩ T) = dual p S ⊔ dual p T := by
  rw [← dual_union_ker, ← coe_inf, ← dual_sup, inf_comm]
  rw [inf_sup_assoc_of_le]
  · rw [inf_comm, coe_inf]
    rw [dual_inf_dual_sup_fgdual hT]
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

private lemma sup_fgdual_fg' {S T : Submodule R N} (hS : S.FGDual p) (hT : T.FG) :
    (S ⊔ T).FGDual p := by
  rw [← sup_eq_left.mpr (hS.ker_le)]
  rw [sup_assoc, sup_comm]
  nth_rw 2 [sup_comm]
  rw [← hS.dual_dual_flip]
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
