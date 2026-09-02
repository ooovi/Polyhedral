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

lemma iConvexComb_duple (i j : I) (a b : R) (ha hb hab) (x : I → M) :
    iConvexComb (.duple i j ha hb hab) x = convexCombPair a b ha hb hab (x i) (x j) := by
  simp [iConvexComb, convexCombPair]

end iConvexComb
end Convexity
