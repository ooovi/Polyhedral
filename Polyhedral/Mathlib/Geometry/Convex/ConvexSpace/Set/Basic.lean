/-
Copyright (c) 2026 Martin Winter, Olivia Röhrig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter, Olivia Röhrig
-/

import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.Geometry.Convex.ConvexSpace.Module
import Mathlib.Geometry.Convex.ConvexSpace.AffineSpace

-- import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Nonneg

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

section Pointwise

open Pointwise

section Semiring

variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [AddCommGroup V] [Module R V] [ConvexSpace R V] [IsModuleConvexSpace R V]

variable {K K₁ K₂ : Set V}

protected lemma IsConvexSet.neg (hK : IsConvexSet R K) : IsConvexSet R (-K) := by
  sorry

end Semiring

section Ring

variable [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [AddCommGroup V] [Module R V] [ConvexSpace R V] [IsModuleConvexSpace R V]
variable [AddTorsor V A]

local instance : ConvexSpace R A := AddTorsor.toConvexSpace
-- TODO: add class expressing compatibility between the convex structures on A and V

/- Minkowski addition preserves convexity. -/
protected lemma IsConvexSet.vadd {K₁ : Set V} {K₂ : Set A}
    (hK₁ : IsConvexSet R K₁) (hK₂ : IsConvexSet R K₂) : IsConvexSet R (K₁ +ᵥ K₂) := by
  -- TODO: use `AddTorsor.sConvexComb_eq_affineCombination`
  sorry

/- Minkowski addition preserves convexity. -/
lemma IsConvexSet.translate (t : V) {K : Set A} (hK : IsConvexSet R K) :
    IsConvexSet R (t +ᵥ K) := by
  -- TODO: use `IsConvexSet.vadd hK₁ hK₂` by setting `K₁ := {t}` and
  --  some missing vadd lemmas
  -- this likely requires a compatbility class between affine and linear convexity
  sorry

/- Minkowski addition preserves convexity. -/
protected lemma IsConvexSet.add {K₁ : Set V} {K₂ : Set V}
    (hK₁ : IsConvexSet R K₁) (hK₂ : IsConvexSet R K₂) : IsConvexSet R (K₁ + K₂) :=
  -- TODO: use `IsConvexSet.vadd hK₁ hK₂`
  -- this likely requires a compatbility class between affine and linear convexity
  sorry

/- Minkowski addition preserves convexity. -/
protected lemma IsConvexSet.sub {K₁ : Set V} {K₂ : Set V}
    (hK₁ : IsConvexSet R K₁) (hK₂ : IsConvexSet R K₂) : IsConvexSet R (K₁ - K₂) :=
  -- TODO: use `IsConvexSet.vadd` and `IsConvexSet.neg`
  sorry

protected lemma IsConvexSet.smul (r : R) {K : Set V} (hK : IsConvexSet R K) :
    IsConvexSet R (r • K) := by
  sorry

end Ring

end Pointwise

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

-- example (C : PointedCone R M) : IsConvexSet R (C : Set M) := by
--   exact Submodule.isConvexSet C

end Semiring

section Field

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K] [ConvexSpace K X] {w : StdSimplex K X}
  {s t : Set X} {x y : X}
variable [AddCommGroup X] [Module K X] [IsModuleConvexSpace K X]

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
