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
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Rank
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Face.Lattice
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Face.Dual
-- import Polyhedral.Halfspace

open Function Module OrderDual LinearMap
open Submodule hiding span dual DualClosed
open PointedCone

-- ## RELINT

namespace PointedCone

variable {R : Type*} [Field R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}
variable {C F F₁ F₂ : PointedCone R M}
variable {x : M}

/- A non-topological variant of the relative interior.
  There are many ways to define it, and hopefully all of them are equivalent.
-/

def relint (C : PointedCone R M) : ConvexCone R M where
  carrier := {x ∈ C | span R (insert (-x) C) = ⊤}
  smul_mem' c hc x hx := sorry
  add_mem' x hx y hy := sorry

lemma mem_relint_iff_mem_span_neg_eq_top :
    x ∈ C.relint ↔ x ∈ C ∧ span R (insert (-x) C) = ⊤ := by simp [relint]

lemma relint_le : C.relint ≤ C := fun _ hx => (mem_relint_iff_mem_span_neg_eq_top.mp hx).1

lemma mem_relint_iff_mem_forall_isFaceOf_eq_top_of_mem :
    x ∈ C.relint ↔ x ∈ C ∧ ∀ F : PointedCone R M, F.IsFaceOf C → (x ∈ F → F = ⊤) := by
  sorry

lemma mem_relint_iff_mem_forall_face_eq_top_of_mem :
    x ∈ C.relint ↔ x ∈ C ∧ ∀ F : Face C, x ∈ F → F = ⊤ := by
  sorry

lemma mem_relint_iff_forall_dual_zero_le_mem_lineal_of_eq_zero :
    x ∈ C.relint ↔ x ∈ C ∧ ∀ y ∈ dual p C, 0 ≤ p x y ∧ (p x y = 0 → y ∈ (dual p C).lineal) := by
  sorry

lemma finset_sum_mem_relint_span {s : Finset M} (hs : (s : Set M) ⊆ C)
    (hC : C ≤ Submodule.span (M := M) R s) : ∑ x ∈ s, x ∈ relint (span R (s : Set M)) := by
  sorry

lemma relint_nonempty (h : C.FinSalRank) : Nonempty C.relint := sorry

-- easier to prove for now
lemma relint_nonempty' (h : C.FinRank) : Nonempty C.relint := by
  /-
    * choose a basis in C
    * since C.FinRank, this basis is finite
    * use `finset_sum_mem_relint_span`
  -/
  sorry

end PointedCone
