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

import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.MinkowskiWeyl
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Relint
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Face.Lattice
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Face.Exposed
import Polyhedral.Hyperplane
import Polyhedral.Halfspace

open Module

namespace PointedCone

/- TODO: basically we need to copy almost everything from `IsFaceOf ` and reprove it for
  `IsExposedFaceOf`. -/

variable {R : Type*} [Field R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}
variable {C F F₁ F₂ : PointedCone R M}

-- We introduce semi-exposed faces because for dual closed cones the semi-exposed face
-- lattice flipps when transitioning to the dual cone.
-- * In finite dimensions all exposed faces are semi-exposed.
-- * For polyhedral cones all faces are semi-exposed.
-- Note that finite intersections of exposed faces are exposed, and so a true semi-exposed
-- face (one that is not an exposed face) is an intersection of infinitely many exposed
-- faces

/-- A semi-exposed face is the (potentially infinite) intersection of exposed faces. -/
def IsSemiExposedFaceOf (F C : PointedCone R M) :=
  ∃ Fs : Set (PointedCone R M), (∀ F ∈ Fs, F.IsExposedFaceOf C) ∧ sInf Fs = F

lemma IsExposedFaceOf.semiExposed (hF : F.IsExposedFaceOf C) :
    F.IsSemiExposedFaceOf C := ⟨{F}, by simpa using hF⟩

variable [Module.Finite R M]
lemma IsSemiExposedFaceOf.exposed (hF : F.IsSemiExposedFaceOf C) :
    F.IsExposedFaceOf C := sorry

end PointedCone
