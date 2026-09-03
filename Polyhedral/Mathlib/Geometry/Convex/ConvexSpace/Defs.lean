/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Geometry.Convex.ConvexSpace.Defs

/-!
# Missing lemmas about convex spaces

This file contains material destined for `Mathlib/Geometry/Convex/ConvexSpace/Defs.lean`.
-/

public section

namespace Convexity
variable {R M I : Type*}

attribute [simp] StdSimplex.nonneg

section iConvexComb
variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R] [ConvexSpace R M]

/-- Evaluating convex combinations is affine in the weights. -/
@[fun_prop]
protected lemma IsAffineMap.sConvexComb :
    IsAffineMap R (sConvexComb : StdSimplex R M → M) :=
  ⟨sConvexComb_sConvexComb⟩

/-- Taking convex combinations of a fixed family of points is affine in the weights. -/
@[fun_prop]
protected lemma IsAffineMap.iConvexComb {f : I → M} :
    IsAffineMap R (fun w : StdSimplex R I ↦ iConvexComb w f) :=
  .comp .sConvexComb (StdSimplex.isAffineMap_map R f)

lemma iConvexComb_duple (i j : I) (a b : R) (ha hb hab) (x : I → M) :
    iConvexComb (.duple i j ha hb hab) x = convexCombPair a b ha hb hab (x i) (x j) := by
  simp [iConvexComb, convexCombPair]

end iConvexComb
end Convexity
