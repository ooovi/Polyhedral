/-
Copyright (c) 2026 Olivia Röhrig, Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter, Olivia Röhrig
-/
module

public import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Basic
public import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Module

import Mathlib.Geometry.Convex.ConvexSpace.AffineSpace
import Mathlib.Geometry.Convex.Set
import Polyhedral.Mathlib.LinearAlgebra.AffineSpace.AffineMap

/-! This file proves results about affine maps and convexity. -/

public section

open Affine Convexity

variable {R V V₁ V₂ P P₁ P₂ I : Type*}

variable [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [AddCommGroup V] [Module R V] [AddTorsor V P]
variable [AddCommGroup V₁] [Module R V₁] [AddTorsor V₁ P₁]
variable [AddCommGroup V₂] [Module R V₂] [AddTorsor V₂ P₂]

variable [ConvexSpace R P] [IsAffineConvexSpace R V P]
variable [ConvexSpace R P₁] [IsAffineConvexSpace R V₁ P₁]
variable [ConvexSpace R P₂] [IsAffineConvexSpace R V₂ P₂]

open Convexity Finset AddTorsor

namespace AffineMap

variable (f : P₁ →ᵃ[R] P₂)

-- PR #39437
lemma isAffineMap : IsAffineMap R f where
  map_sConvexComb s := by
    rw [sConvexComb_eq_affineCombination, sConvexComb_map, iConvexComb_eq_affineCombination]
    simpa only [Function.comp_id] using
      map_affineCombination (s := s.weights.support) _root_.id s.weights s.total f

@[simp] lemma map_sConvexComb (w : StdSimplex R P₁) :
    f (sConvexComb w) = sConvexComb (w.map f) := f.isAffineMap.map_sConvexComb w

lemma image_isConvexSet {s : Set P₁} (hs : IsConvexSet R s) : IsConvexSet R (f '' s) :=
  hs.image f.isAffineMap

lemma range_isConvexSet : IsConvexSet R (Set.range f) := by
  rw [← Set.image_univ]
  exact f.image_isConvexSet .univ

end AffineMap
