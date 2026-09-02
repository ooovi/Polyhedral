/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/
module

public import Mathlib.Geometry.Convex.ConvexSpace.Prod

/-!
# Pairing of affine maps

This file proves that the pairing of two affine maps into a product convex space is affine
(`IsAffineMap.prodMk`).
-/

@[expose] public section

namespace Convexity

variable {R X Y Z : Type*} [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [ConvexSpace R X] [ConvexSpace R Y] [ConvexSpace R Z]

/-- The pairing of two affine maps is affine. -/
@[fun_prop]
lemma IsAffineMap.prodMk {f : X → Y} {g : X → Z} (hf : IsAffineMap R f) (hg : IsAffineMap R g) :
    IsAffineMap R fun x => (f x, g x) where
  map_sConvexComb w := by
    ext
    · simp [hf.map_sConvexComb, sConvexComb_map]
    · simp [hg.map_sConvexComb, sConvexComb_map]

end Convexity
