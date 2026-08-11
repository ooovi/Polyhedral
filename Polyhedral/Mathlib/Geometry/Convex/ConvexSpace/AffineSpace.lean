/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/

import Mathlib.Geometry.Convex.Set
import Mathlib.Geometry.Convex.ConvexSpace.AffineSpace
import Mathlib.LinearAlgebra.AffineSpace.Combination
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.Geometry.Convex.ConvexSpace.Module

/-!
# Affine spaces are convex spaces

This file shows that every affine space is a convex space.

-/

namespace Convexity

variable {R V P I : Type*}
variable [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [AddCommGroup V] [Module R V] [AddTorsor V P]

-- for consistent naming
@[implicit_reducible]
alias ConvexSpace.ofAddTorsor := AddTorsor.toConvexSpace

variable (R V P) [ConvexSpace R P] in
/-- Typeclass for a convex space structure on an affine space to be given by affine
combinations. -/
class IsAffineConvexSpace : Prop where
  sConvexComb_eq_convexComb (w : StdSimplex R P) :
    w.sConvexComb = AddTorsor.convexCombination w

export IsAffineConvexSpace (sConvexComb_eq_convexComb)
attribute [simp] sConvexComb_eq_convexComb

attribute [local instance] ConvexSpace.ofAddTorsor in
instance IsAffineConvexSpace.ofAddTorsor : IsAffineConvexSpace R V P where
  sConvexComb_eq_convexComb _ := rfl

instance [ConvexSpace R V] [IsModuleConvexSpace R V] : IsAffineConvexSpace R V V where
  sConvexComb_eq_convexComb w := by
    rw [IsModuleConvexSpace.sConvexComb_eq_sum, AddTorsor.convexCombination,
      Finset.affineCombination_eq_linear_combination _ _ _ w.total]
    rfl

end Convexity
