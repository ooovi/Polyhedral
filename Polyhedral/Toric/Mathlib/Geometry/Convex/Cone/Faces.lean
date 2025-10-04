/-
Copyright (c) 2025 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.LinearAlgebra.SesquilinearForm

import Polyhedral.Toric.Mathlib.Geometry.Convex.Cone.Primspace

/-!
# Polyhedral cones
...
-/

open Function Module

variable {𝕜 M N : Type*}

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup M] [Module 𝕜 M] [Module.Finite 𝕜 M]
  [AddCommGroup N] [Module 𝕜 N] [Module.Finite 𝕜 N]

namespace PointedCone

def IsFace (P : PointedCone 𝕜 M) (F : PointedCone 𝕜 M)
  := ∃ Q : PolyhedralCone.Primspace 𝕜 M, P ≤ Q ∧ F = P ⊓ Q.boundary

end PointedCone
