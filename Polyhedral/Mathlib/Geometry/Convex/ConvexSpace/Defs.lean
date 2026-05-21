/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Andrew Yang, Yaël Dillies
-/
module
public import Mathlib.Geometry.Convex.ConvexSpace.Defs

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Finsupp.Order
public import Mathlib.LinearAlgebra.Finsupp.LSum

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity.Basic

/-!
# Convex spaces

This file defines convex spaces as an algebraic structure supporting finite convex combinations.

-/

@[expose] public noncomputable section

universe u v w u₁ u₂

open Finsupp

namespace Convexity
variable {R X M N P I J K : Type*}

namespace StdSimplex

section Semifield
variable [Semifield K] [LinearOrder K] [IsStrictOrderedRing K]

private lemma restrict_nonneg_aux {w : StdSimplex K X} {p : X → Prop} [DecidablePred p] :
    0 ≤ (filter p w.weights).sum fun _x k ↦ k :=
  sum_nonneg <| by simp [filter_apply, apply_ite]

private lemma restrict_ne_zero_aux {w : StdSimplex K X} {p : X → Prop} [DecidablePred p]
    (hp : ∃ a, p a ∧ w.weights a ≠ 0) :
    (filter p w.weights).sum (fun _x k ↦ k) ≠ 0 :=
  (sum_pos (by simp +contextual [lt_iff_le_and_ne, eq_comm]) <| by simpa [ne_iff, filter_apply]).ne'

/-- Project an element of the standard simplex to a lower-dimensional standard simplex,
assuming at least one non-zero weight subsists. -/
def restrict (w : StdSimplex K X) (s : Set X) (hs : ∃ x ∈ s, w.weights x ≠ 0) : StdSimplex K X where
  weights := open scoped Classical in
    ((w.weights.filter (· ∈ s)).sum fun x k ↦ k)⁻¹ • w.weights.filter (· ∈ s)
  nonneg := by
    classical
    exact smul_nonneg (inv_nonneg.2 restrict_nonneg_aux) fun _ ↦ by simp [filter_apply, apply_ite]
  total := by classical simp [sum_smul_index, ← mul_sum, restrict_ne_zero_aux hs]

lemma weights_restrict (w : StdSimplex K X) (s : Set X) (hs) [DecidablePred (· ∈ s)] :
    (w.restrict s hs).weights =
      ((w.weights.filter (· ∈ s)).sum fun _x k ↦ k)⁻¹ • w.weights.filter (· ∈ s) := by
  simp [restrict]; congr

variable [IsDomain K]

@[simp]
lemma support_weights_restrict (w : StdSimplex K X) (s : Set X) (hs) [DecidablePred (· ∈ s)] :
    (w.restrict s hs).weights.support = w.weights.support.filter (· ∈ s) := by
  have : (w.weights.filter (· ∈ s)).sum (fun x k ↦ k) ≠ 0 :=
    (sum_pos (by simp +contextual [lt_iff_le_and_ne, eq_comm]) <| by
      simpa [ne_iff, filter_apply]).ne'
  rw [weights_restrict, support_smul_eq (by convert inv_ne_zero this)]
  simp

@[simp] lemma restrict_singleton (w : StdSimplex K X) (x : X) (hx) :
    w.restrict {x} hx = single x := by
  classical
  simp only [← support_weights_eq_singleton, support_weights_restrict, Set.mem_singleton_iff]
  ext
  simp only [Finset.mem_filter, mem_support_iff, ne_eq, Finset.mem_singleton, and_iff_right_iff_imp]
  rintro rfl
  simpa using hx

end Semifield
end StdSimplex

namespace StdSimplex

variable [Semifield K] [LinearOrder K] [IsStrictOrderedRing K]

lemma convexCombPair_restrict_restrict_compl (w : StdSimplex K I) (s : Set I) (hs hs')
    [DecidablePred (· ∈ s)] :
    convexCombPair
      ((w.weights.filter (· ∈ s)).sum fun _x k ↦ k)
      ((w.weights.filter (· ∉ s)).sum fun _x k ↦ k)
      (by exact restrict_nonneg_aux) (by exact restrict_nonneg_aux) (by simp)
      (w.restrict s hs) (w.restrict sᶜ hs') = w := by
  ext : 1
  simp only [Set.mem_compl_iff] at hs'
  simp [weights_restrict, smul_inv_smul₀, restrict_ne_zero_aux, hs, hs']

end StdSimplex

end Convexity


namespace Convexity

variable {R X Y : Type*}
variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [ConvexSpace R X] [ConvexSpace R Y]

noncomputable instance instConvexSpaceProd : ConvexSpace R (X × Y) where
  sConvexComb w := (w.iConvexComb Prod.fst, w.iConvexComb Prod.snd)
  sConvexComb_single x := by
    ext <;> simp
  assoc w := by
    ext <;>
      simpa [sConvexComb_map, Function.comp_def] using
        iConvexComb_assoc w (id : StdSimplex R (X × Y) → StdSimplex R (X × Y)) _
end Convexity
