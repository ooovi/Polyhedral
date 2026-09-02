/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/
module


public import Mathlib.Geometry.Convex.ConvexSpace.AffineSpace
public import Mathlib.Geometry.Convex.ConvexSpace.Module

/-!
# Convex combinations in affine convex spaces

This file proves that indexed convex combinations in an affine convex space commute with
pointwise translation (`iConvexComb_vadd`) and pointwise difference (`iConvexComb_vsub`).

-/

@[expose] public section

namespace Convexity

open AddTorsor

variable {R V P I : Type*}
variable [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [AddCommGroup V] [Module R V] [AddTorsor V P]
variable [ConvexSpace R P] [IsAffineConvexSpace R V P]
variable [ConvexSpace R V] [IsModuleConvexSpace R V]

/-- A convex combination of pointwise translates splits as the convex combination of the
translations acting on the convex combination of the base points. -/
theorem iConvexComb_vadd (w : StdSimplex R I) (g : I → V) (q : I → P) :
    w.iConvexComb (fun i => g i +ᵥ q i) = w.iConvexComb g +ᵥ w.iConvexComb q := by
  obtain ⟨b⟩ : Nonempty P := inferInstance
  rw [iConvexComb_eq_affineCombination (f := fun i => g i +ᵥ q i),
    iConvexComb_eq_affineCombination (f := q), iConvexComb_eq_sum,
    Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one (h := w.total) (b := b),
    Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one (h := w.total) (b := b),
    Finset.weightedVSubOfPoint_apply, Finset.weightedVSubOfPoint_apply, Finsupp.sum]
  simp_rw [vadd_vsub_assoc, smul_add, Finset.sum_add_distrib, add_vadd]

/-- A convex combination of pointwise differences is the difference of the convex
combinations. -/
theorem iConvexComb_vsub (w : StdSimplex R I) (p q : I → P) :
    (w.iConvexComb fun i => p i -ᵥ q i) = w.iConvexComb p -ᵥ w.iConvexComb q := by
  rw [iConvexComb_eq_sum, iConvexComb_eq_affineCombination (f := p),
    iConvexComb_eq_affineCombination (f := q), Finsupp.sum,
    ← Finset.sum_smul_vsub_eq_affineCombination_vsub]

end Convexity
