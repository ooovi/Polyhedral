/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/

import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Geometry.Convex.Set

public section

namespace Convexity
variable {ι R K X Y : Type*}

section Field
variable [Field K] [LinearOrder K] [IsStrictOrderedRing K] [ConvexSpace K X] {w : StdSimplex K X}
  {s t : Set X} {x y : X}

open Pointwise

variable [AddCommGroup X] [Module K X]

open Pointwise Set in
protected theorem IsConvexSet.add_smul {s : Set X}
    (h_conv : IsConvexSet K s) {p q : K} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    (p + q) • s = p • s + q • s := by
  sorry

end Field

end Convexity
