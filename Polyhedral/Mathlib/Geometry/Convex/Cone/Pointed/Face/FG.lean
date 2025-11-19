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
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Face.Lattice
import Polyhedral.Hyperplane
import Polyhedral.Halfspace

namespace PointedCone

variable {R : Type*} [Field R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}
variable {C F F₁ F₂ : PointedCone R M}

variable (hC : C.FG)

noncomputable def Face.rank (F : Face C) := Module.rank R F.span

-- def Face.IsRay (F : Face C) := F.rank = 1

-- lemma isAtom_of_isRay {F : Face C} (h : F.IsRay) : IsAtom F := sorry

-- def atoms : Set (Face C) := {F : Face C | IsAtom F}
-- def rays : Set (Face C) := {F : Face C | F.IsRay}

-- def coatoms : Set (Face C) := {F : Face C | IsCoatom F}
-- alias facets := coatoms


-- ## KREIN MILMAN

lemma atomic_of_fg (hC : C.FG) : IsAtomic (Face C) := sorry

lemma atomistic_of_fg (hC : C.FG) : IsAtomistic (Face C) := sorry

lemma coatomic_of_fg (hC : C.FG) : IsCoatomic (Face C) := sorry

lemma coatomistic_of_fg (hC : C.FG) : IsCoatomistic (Face C) := sorry

lemma face_complemented (hC : C.FG) : ComplementedLattice (Face C) := sorry

end PointedCone
