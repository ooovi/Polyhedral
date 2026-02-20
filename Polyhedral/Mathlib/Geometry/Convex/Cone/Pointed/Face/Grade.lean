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
import Polyhedral.Polyhedral.Basic
-- import Polyhedral.Hyperplane
-- import Polyhedral.Halfspace

open Module



-- ## PREDICATE

namespace PointedCone

variable {R : Type*} [Field R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}
variable {C F F₁ F₂ : PointedCone R M}

-- ...

end PointedCone








-- ## BUNDLED STRUCTURE

namespace PointedCone

variable {R : Type*} [Field R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}
variable {C F F₁ F₂ : PointedCone R M}

-- My impression is someone should first implement the grading for the lattice of submodules.
-- (if not already done). This here is then a simple derivate thereof.

lemma salFinrank_strictMono (C : PointedCone R M) : -- (hC : C.IsPolyhedral) :
    StrictMono fun F : Face C => salFinrank (F : PointedCone R M) := by
  sorry

lemma salFinrank_covBy {C : PointedCone R M} (hC : C.IsPolyhedral) (F G : Face C) (hFG : F ⋖ G) :
    salFinrank (F : PointedCone R M) ⋖ salFinrank (G : PointedCone R M) := by
  sorry

noncomputable instance {C : PointedCone R M} (hC : C.IsPolyhedral) : GradeOrder ℕ (Face C) where
  grade F := salFinrank (F : PointedCone R M)
  grade_strictMono := salFinrank_strictMono C
  covBy_grade := salFinrank_covBy hC


end PointedCone
