/-
Copyright (c) 2026 Martin Winter, Olivia Röhrig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter, Olivia Röhrig
-/

import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.Geometry.Convex.ConvexSpace.Module
import Mathlib.Geometry.Convex.ConvexSpace.AffineSpace

/-! This file proves basic properties of convex sets. -/

noncomputable section

variable {ι R K X Y V A W B : Type*}

namespace Convexity

namespace Semiring

variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R] [ConvexSpace R X]

protected lemma IsConvexSet.biInter {S : Set (Set X)} (hS : ∀ s ∈ S, IsConvexSet R s) :
    IsConvexSet R (⋂ s ∈ S, s) := by
  simp +contextual [IsConvexSet, (hS _ _).sConvexComb_mem]

end Semiring

section Semiring

-- TODO: move the below to Module.lean

variable {M S R : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [PartialOrder R]
  [IsStrictOrderedRing R] [ConvexSpace R M] [IsModuleConvexSpace R M]

@[simp]
lemma _root_.Submodule.isConvexSet (S : Submodule R M) : IsConvexSet R (S : Set M) := by
  apply IsConvexSet.of_sConvexComb_mem
  intro w hw
  rw [sConvexComb_eq_sum w]
  refine S.finsuppSum_mem _ _ (fun i r ↦ r • i) (fun c hc ↦ ?_)
  exact Submodule.smul_mem S (w.weights c) <| hw <| Finsupp.mem_support_iff.mpr hc

end Semiring

section Field

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K] [ConvexSpace K X] {w : StdSimplex K X}
  {s t : Set X} {x y : X}
variable [AddCommGroup X] [Module K X] [IsModuleConvexSpace K X]

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
    have := h_conv.convexCombPair_mem ys ys' (a := p • (p + q)⁻¹) (b := q • (p + q)⁻¹) ?_ ?_ ?_
    · refine ⟨_, this, ?_⟩
      simp [convexCombPair_eq_sum, smul_smul]
      grind
    · exact mul_nonneg hp (inv_nonneg.mpr (add_nonneg hp hq))
    · exact mul_nonneg hq (inv_nonneg.mpr (add_nonneg hp hq))
    · simp [← add_mul, mul_inv_cancel₀ h]

end Field

end Convexity
