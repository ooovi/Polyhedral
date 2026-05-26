/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/

import Mathlib.Geometry.Convex.Set
import Mathlib.Geometry.Convex.ConvexSpace.Defs
import Mathlib.Geometry.Convex.ConvexSpace.Module
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Geometry.Convex.Set

public section

variable {ι R K X Y : Type*}

section Semiring

open Convexity

variable {M S R : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [PartialOrder R]
  [IsStrictOrderedRing R] [ConvexSpace R M] [IsModuleConvexSpace R M]

lemma Submodule.isConvexSet (P : Submodule R M) :
    Convexity.IsConvexSet R (P : Set M) := by
  intro w hw
  rw [sConvexComb_eq_sum w]
  refine P.finsuppSum_mem _ _ (fun i r ↦ r • i) (fun c hc ↦ ?_)
  exact Submodule.smul_mem P (w.weights c) <| hw <| Finsupp.mem_support_iff.mpr hc

end Semiring

section Field

namespace Convexity

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K] [ConvexSpace K X] {w : StdSimplex K X}
  {s t : Set X} {x y : X}
variable [AddCommGroup X] [Module K X]

open Pointwise Set in
protected theorem IsConvexSet.add_smul {s : Set X}
    (h_conv : IsConvexSet K s) {p q : K} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    (p + q) • s = p • s + q • s := by
  sorry

end Convexity

end Field

end
