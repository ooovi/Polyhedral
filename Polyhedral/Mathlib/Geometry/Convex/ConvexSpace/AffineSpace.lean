/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Geometry.Convex.ConvexSpace.AffineSpace
public import Mathlib.LinearAlgebra.AffineSpace.Combination
public import Mathlib.LinearAlgebra.AffineSpace.AffineMap

/-!
# Affine spaces are convex spaces

This file shows that every affine space is a convex space.

-/

public noncomputable section

open scoped Affine

variable {R V V2 P P2 I : Type*}
variable [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [AddCommGroup V] [Module R V] [AddTorsor V P]
variable [AddCommGroup V2] [Module R V2] [AffineSpace V2 P2]

open Convexity

namespace AffineMap

attribute [local instance] AddTorsor.toConvexSpace

-- PR #39437
open Finset AddTorsor in
lemma isAffineMap {V2 P2 : Type*} [AddCommGroup V2] [Module R V2] [AffineSpace V2 P2]
    (f : P →ᵃ[R] P2) : IsAffineMap R f where
  map_sConvexComb s:= by
    classical
    simp_rw [sConvexComb_eq_affineCombination, StdSimplex.weights_map, Finsupp.mapDomain,
      map_affineCombination _ _ _ s.total, Finsupp.sum, Finsupp.coe_finsetSum]
    simp only [affineCombination_apply, weightedVSubOfPoint_apply, map_sum]
    congr
    ext i
    rw [sum_eq_single (f i) fun _ _ hx ↦ by simp [hx.symm]]
    · simp
    · intro h
      simp only [Finsupp.mem_support_iff, Finsupp.coe_finsetSum, sum_apply,
        Decidable.not_not, Finsupp.single_apply] at h
      have hwi : s.weights i = 0 := by
        by_contra hi
        have := sum_eq_zero_iff_of_nonneg (fun _ _ ↦ ?_) |>.mp h i (Finsupp.mem_support_iff.mpr hi)
        · simp at this
          contradiction
        · split_ifs <;> simp
      simp [hwi]

end AffineMap
