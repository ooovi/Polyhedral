/-
Copyright (c) 2025 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Order.Partition.Basic
import Mathlib.Order.Grade

import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.MinkowskiWeyl
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Face.Lattice
import Polyhedral.Hyperplane
import Polyhedral.Halfspace

open Module



-- ## PREDICATE

namespace PointedCone

variable {R : Type*} [Field R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}
variable {C F F₁ F₂ : PointedCone R M}

variable (R M) in
/-- Salient rank of a cone. -/
noncomputable def salRank (C : PointedCone R M) :=
    Module.rank R (Submodule.span R (C.salientQuot : Set (M ⧸ C.lineal)))

variable (R M) in
/-- Salient rank of a cone. -/
noncomputable def salFinrank (C : PointedCone R M) :=
    Module.finrank R (Submodule.span R (C.salientQuot : Set (M ⧸ C.lineal)))

end PointedCone








-- ## BUNDLES STRUCTURE

namespace PointedCone

variable {R : Type*} [Field R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}
variable {C F F₁ F₂ : PointedCone R M}

variable (hC : C.FG)

-- My impression is someone should first implement the grading for the lattice of submodules.
-- (if not already done). This here is then a simple derivate thereof.

noncomputable instance {C : PointedCone R M} : GradeOrder ℕ (Face C) where
  grade F := salFinrank R M F
  grade_strictMono := sorry
  covBy_grade := sorry


end PointedCone
