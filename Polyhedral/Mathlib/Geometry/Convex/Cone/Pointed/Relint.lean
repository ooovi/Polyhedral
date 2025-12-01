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
import Polyhedral.Halfspace

open Function Module OrderDual LinearMap
open Submodule hiding span dual IsDualClosed
open PointedCone

-- ## RELINT

namespace PointedCone

variable {R : Type*} [Field R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {C : PointedCone R M}
variable {p : M →ₗ[R] N →ₗ[R] R}
variable {C F F₁ F₂ : PointedCone R M}
variable (hC : C.IsDualClosed p)

/- A non-topological variant of the relative interior.
  Below two definitions are given. If they are not equivalent, then the more general one should
  be chose and equivalence should be proven when it holds.
-/

-- def IsFaceOf.peal (hF : F.IsFaceOf C) : ConvexCone R M where
--   carrier := C \ F
--   smul_mem' c hc x h := sorry
--   add_mem' x hx y hy := sorry

-- lemma face_iff_dif_cone (C F : PointedCone R M) :
--     F.IsFaceOf C ↔ ∃ D : ConvexCone R M, (C \ F : Set M) = D := sorry

/-- The relative interior of a pointed cone `C` consists of all the points of `C` that do not lie
  in any proper face of `C`. This is an algebraic variant of relative interior that agrees
  with the topological one in many cases. -/
def relint (C : PointedCone R M) : ConvexCone R M where
  carrier := {x ∈ C | ∀ F : Face C, x ∈ F → F = C}
  smul_mem' c hc x hx := by
    constructor
    · exact C.smul_mem (le_of_lt hc) hx.1
    · intro F hcF
      have H : x ∈ F := sorry -- (F.smul_mem_iff (ne_of_lt hc).symm).mp hcF
      exact hx.2 F H
  add_mem' x hx y hy := by
    simp
    constructor
    · sorry
    · sorry

lemma relint_le (C : PointedCone R M) : C.relint ≤ C := sorry

lemma relint_submodule (S : Submodule R M) : (S : PointedCone R M).relint = S := sorry

-- theorem relint_def_sInf (C : PointedCone R M) :
--     C.relint = sInf {s | dual p.flip (dual p s) = C} := sorry

-- def min_face {x : M} (h : x ∈ C) : Face C := sorry -- sInf {F : Face C | x ∈ F}

-- theorem relint_def_min (C : PointedCone R M) :
--     C.relint = { x ∈ C | C.min_face (x := x) sorry = C } := sorry

/-- The relative interior is non-empty. -/
lemma relint_nonempty (C : PointedCone R M) : Nonempty C.relint := sorry

/-- The relative interior is non-empty. -/
lemma relint_nonempty' (C : PointedCone R M) : C.relint ≠ ⊥ := sorry

lemma relint_disj (F₁ F₂ : Face C) :
    F₁ ≠ F₂ ↔ Disjoint (relint F₁) (relint F₂) (α := ConvexCone R M) := sorry

lemma relint_cover (C : PointedCone R M) :
    ⋃ F : Face C, (relint F : ConvexCone R M) = (C : Set M) := sorry

def relint_partition (C : PointedCone R M) : Partition (C : Set M) where
  parts := { relint (F : PointedCone R M) | (F : Face C) }
  sSupIndep' := sorry
  bot_notMem' := by
    simp only [Set.bot_eq_empty, Set.mem_setOf_eq, ConvexCone.coe_eq_empty, not_exists]
    exact fun F => relint_nonempty' (F : PointedCone R M)
  sSup_eq' := by
    ext x
    -- simp; exact relint_partition C
    sorry

-- Should we introduce a topology/metric before proving lemmas such as the below?

lemma relint_foo (x y : M) (hx : x ∈ relint C) (hy : y ∈ C) :
    ∃ ε > 0, ∀ δ > 0, δ < ε → δ • x + y ∈ relint C := sorry

lemma relint_foo'' (x y : M) (hx : x ∈ relint C) (hy : y ∈ Submodule.span R C) :
    ∃ ε > 0, ∀ δ ≥ 0, δ < ε → x + δ • y ∈ relint C := sorry

lemma relint_foo' (x y : M) (hx : x ∈ relint C) (hy : y ∈ C) : ∃ z ∈ relint C, z + y = x := sorry

end PointedCone
