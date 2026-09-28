/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Geometry.Convex.AffineMap.Module
public import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Order

import Mathlib.Algebra.Module.BigOperators
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Positivity.Basic

/-!
# Ordered modules are ordered convex spaces

This file shows that a linearly ordered module is an ordered convex space
(`Convexity.IsOrderedConvexSpace.ofModule`), by Abel summation.
-/

public section

namespace Convexity
variable {S R K M X : Type*}

section Semiring
variable [Semiring R] [AddCommMonoid M] [Module R M] [PartialOrder R]
  [IsStrictOrderedRing R] [ConvexSpace R M] [IsModuleConvexSpace R M]

@[simp]
lemma _root_.Submodule.isConvexSet (S : Submodule R M) : IsConvexSet R (S : Set M) := by
  refine .of_sConvexComb_mem fun w hw ↦ ?_
  rw [sConvexComb_eq_sum w]
  refine S.finsuppSum_mem _ _ (fun i r ↦ r • i) fun c hc ↦ ?_
  exact Submodule.smul_mem S (w.weights c) <| hw <| Finsupp.mem_support_iff.mpr hc

end Semiring

section Field
variable [Field K] [LinearOrder K] [IsStrictOrderedRing K] [ConvexSpace K X] [AddCommGroup X]
  [Module K X] [IsModuleConvexSpace K X] {w : StdSimplex K X} {s t : Set X} {x y : X}

-- NOTE: Replace `p + q ≠ 0` by `s.Nonempty`. It still holds uisng `add_eq_zero_iff_of_nonneg`.
-- NOTE: I tend to believe that this should be formulated on `ConvexSet`.
open Pointwise Set in
protected theorem IsConvexSet.add_smul {s : Set X}
    (h_conv : IsConvexSet K s) {p q : K} (hp : 0 ≤ p) (hq : 0 ≤ q) (h : p + q ≠ 0) :
    (p + q) • s = p • s + q • s := by
  ext x
  simp only [mem_smul_set, mem_add, exists_exists_and_eq_and]
  constructor
  · rintro ⟨y, ys, rfl⟩
    use y, ys, y, ys
    exact (add_smul p q y).symm
  · rintro ⟨y, ys, y', ys', rfl⟩
    refine ⟨_, h_conv.convexCombPair_mem ys ys' (a := p • (p + q)⁻¹) (b := q • (p + q)⁻¹)
      (by dsimp; positivity) (by dsimp; positivity) (by simp [← add_mul, mul_inv_cancel₀ h]), ?_⟩
    simp [convexCombPair_eq_sum, smul_smul]
    grind

end Field

variable {R M N : Type*} [Semiring R] [AddCommGroup M] [Module R M]

open Finset in
/-- **Abel summation**: a weighted sum `∑ k < n, c k • y k` is determined by the tail sums of `c`
and the increments of `y`. -/
private lemma sum_smul_eq_sum_tail_smul_sub (n : ℕ) (c : ℕ → R) (y : ℕ → M) :
    ∑ k ∈ range n, c k • y k =
      (∑ k ∈ range n, c k) • y 0 +
        ∑ i ∈ range n, (∑ k ∈ Ico (i + 1) n, c k) • (y (i + 1) - y i) := by
  have step (k : ℕ) : c k • y k = c k • y 0 + ∑ i ∈ range k, c k • (y (i + 1) - y i) := by
    rw [← Finset.smul_sum, sum_range_sub, smul_sub]
    abel
  rw [sum_congr rfl fun k _ ↦ step k, sum_add_distrib, ← Finset.sum_smul]
  congr 1
  rw [sum_comm' (t' := range n) (s' := fun i ↦ Ico (i + 1) n) (by intro k i; simp; omega)]
  exact sum_congr rfl fun i _ ↦ Finset.sum_smul.symm

variable [PartialOrder R] [LinearOrder M] [IsOrderedAddMonoid M] [SMulPosMono R M]

open Finset in
/-- If the tail sums of `a` are dominated by those of `b` and the two have the same total, then
`∑ a k • y k ≤ ∑ b k • y k` for any monotone `y`. This is Abel summation plus the fact that the
increments of `y` are nonnegative. -/
private lemma sum_smul_le_sum_smul {n : ℕ} {a b : ℕ → R} {y : ℕ → M} (hy : Monotone y)
    (hab : ∑ k ∈ range n, a k = ∑ k ∈ range n, b k)
    (h : ∀ i, ∑ k ∈ Ico i n, a k ≤ ∑ k ∈ Ico i n, b k) :
    ∑ k ∈ range n, a k • y k ≤ ∑ k ∈ range n, b k • y k := by
  rw [sum_smul_eq_sum_tail_smul_sub n a y, sum_smul_eq_sum_tail_smul_sub n b y, hab]
  gcongr with i hi
  · exact sub_nonneg.2 (hy i.le_succ)
  · exact h (i + 1)

variable [IsStrictOrderedRing R] [ConvexSpace R M] [IsModuleConvexSpace R M]

open Finset in
/-- A linearly ordered module is an ordered convex space: replacing the points of a convex
combination by larger ones, or moving weight from smaller points to larger ones, can only increase
the combination.

The proof is by Abel summation over the union of the two supports, enumerated in increasing
order. -/
instance (priority := low) IsOrderedConvexSpace.ofModule : IsOrderedConvexSpace R M where
  monotone_sConvexComb w₁ w₂ hw := by
    -- Enumerate the union `S` of the two supports in increasing order as `y 0 < … < y (n - 1)`.
    set S := w₁.weights.support ∪ w₂.weights.support with hSdef
    have hS₁ : w₁.weights.support ⊆ S := subset_union_left
    have hS₂ : w₂.weights.support ⊆ S := subset_union_right
    obtain ⟨n, hn⟩ : ∃ n, S.card = n := ⟨_, rfl⟩
    have hpos : 0 < n := hn ▸ card_pos.2 (w₁.support_weights_nonempty.mono hS₁)
    set e := S.orderEmbOfFin hn with he
    obtain ⟨y, hyk, hy⟩ : ∃ y : ℕ → M, (∀ k, ∀ hk : k < n, y k = e ⟨k, hk⟩) ∧ Monotone y :=
      ⟨fun k ↦ e ⟨min k (n - 1), by omega⟩,
        fun k hk ↦ by
          have hmin : min k (n - 1) = k := by omega
          simp only [hmin],
        fun k l hkl ↦ e.monotone (by simp only [Fin.mk_le_mk]; omega)⟩
    have hinj : ∀ k ∈ range n, ∀ l ∈ range n, y k = y l → k = l := by
      simp only [mem_range]
      intro k hk l hl hkl
      rw [hyk k hk, hyk l hl] at hkl
      simpa using e.injective hkl
    have hle : ∀ i < n, ∀ k < n, (y i ≤ y k ↔ i ≤ k) := fun i hi k hk ↦ by
      rw [hyk i hi, hyk k hk, e.le_iff_le, Fin.mk_le_mk]
    have himg : (range n).image y = S := by
      rw [← Finset.image_orderEmbOfFin_univ S hn, ← he]
      ext x
      simp only [mem_image, mem_range, Finset.mem_univ, true_and]
      exact ⟨fun ⟨k, hk, hkx⟩ ↦ ⟨⟨k, hk⟩, by rwa [← hyk k hk]⟩,
        fun ⟨i, hix⟩ ↦ ⟨i, i.2, by rwa [hyk i i.2]⟩⟩
    -- Sums over `S` are sums over `range n`.
    have hsumM (f : M → M) : ∑ x ∈ S, f x = ∑ k ∈ range n, f (y k) := by
      rw [← himg, Finset.sum_image hinj]
    have hsumR (f : M → R) : ∑ x ∈ S, f x = ∑ k ∈ range n, f (y k) := by
      rw [← himg, Finset.sum_image hinj]
    have hcomb (w : StdSimplex R M) (hwS : w.weights.support ⊆ S) :
        w.sConvexComb = ∑ k ∈ range n, w.weights (y k) • y k := by
      rw [sConvexComb_eq_sum w, Finsupp.sum, Finset.sum_subset hwS, hsumM]
      intro x _ hx
      rw [Finsupp.notMem_support_iff.1 hx, zero_smul]
    have htotal (w : StdSimplex R M) (hwS : w.weights.support ⊆ S) :
        ∑ k ∈ range n, w.weights (y k) = 1 := by
      have hw := w.total
      rw [Finsupp.sum] at hw
      rw [← hsumR, ← Finset.sum_subset hwS fun x _ hx ↦ Finsupp.notMem_support_iff.1 hx, hw]
    have hupper (w : StdSimplex R M) (hwS : w.weights.support ⊆ S) (i : ℕ) (hi : i < n) :
        w.upperMass (y i) = ∑ k ∈ Ico i n, w.weights (y k) := by
      have hfilter : (range n).filter (fun k ↦ y i ≤ y k) = Ico i n := by
        ext k
        simp only [mem_filter, mem_range, mem_Ico]
        exact ⟨fun h ↦ ⟨(hle i hi k h.1).1 h.2, h.1⟩, fun h ↦ ⟨h.2, (hle i hi k h.2).2 h.1⟩⟩
      rw [StdSimplex.upperMass_eq_sum,
        Finset.sum_subset (Finset.filter_subset_filter _ hwS) (fun x hx hx' ↦ by
          by_contra h
          exact hx' (Finset.mem_filter.2
            ⟨Finsupp.mem_support_iff.2 h, (Finset.mem_filter.1 hx).2⟩)),
        ← himg, Finset.filter_image, hfilter,
        Finset.sum_image fun k hk l hl ↦ hinj k (mem_range.2 (mem_Ico.1 hk).2) l
          (mem_range.2 (mem_Ico.1 hl).2)]
    rw [hcomb w₁ hS₁, hcomb w₂ hS₂]
    refine sum_smul_le_sum_smul hy ((htotal w₁ hS₁).trans (htotal w₂ hS₂).symm) fun i ↦ ?_
    rcases lt_or_ge i n with hi | hi
    · rw [← hupper w₁ hS₁ i hi, ← hupper w₂ hS₂ i hi]
      exact StdSimplex.le_def.1 hw _
    · rw [Finset.Ico_eq_empty (by omega)]
      simp

end Convexity
