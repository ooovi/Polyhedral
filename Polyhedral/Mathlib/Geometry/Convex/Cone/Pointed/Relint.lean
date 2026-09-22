/-
Copyright (c) 2025 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/
module

public import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Face.Lattice
public import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.DualClosed

/-! This file defines the algebraic relative interior of a convex cone. -/

@[expose] public section

open Submodule

/-
The relative interior (relint for short) is a topological notion, and hence might depend on the
exact topology chosen on the ambient space. In finite dimensions, the topology is essentially
unique, but in infinite dimensions it is possible that a cone has a non-empty or empty relint
depending on the topology.

Without a topology one can consider algebraic notions of relative interior.

The `core` is one possible notion with the following equivalent definitions: a point x ∈ C lies in
the core iff one of the following equivalent conditions holds:
  * x lies in no proper face of C
  * hull R (C ∪ (-x)) = span R C
  * ∀ t : span R C, ∃ c > 0, x + c • t ∈ C
  * ∀ φ : Dual R M, φ x = 0 → φ ∈ lineal (dual (Dual.eval R M) C)

The `weak relint` is another notion that is not always equivalent to the core. It is the relative
interior w.r.t. the topology obtain from the double-dual closure operation (or, weak topology).

In finite dimensions all these notions are the same, while in infinite dimensions this is not
true anymore. We always have `weak relint ≤ core`.

The core has moreover the property that the cone is the disjoint union of the cores of the faces.
This is not true for the weak relint. One still has disjointness of the weak relints, but not that
they cover all of the cone.

Here we chose the core for defining the algebraic relint. Among its many equivalent definitions,
we chose the most elementary one: `∀ t : span R C, ∃ c > 0, x + c • t ∈ C`, because it does not
depend on duality or the notions of faces or hulls.

See also: https://en.wikipedia.org/wiki/Algebraic_interior

-/

/- TODO:
  * proving that all these definitions are equivalent.
  * the relints of the faces of a cone partition the cone.
  * the relint is preserved under taking the double dual closure.
  * defining the weak relint and proving its relation to the core.
-/

namespace PointedCone

variable {R : Type*} [Field R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}
variable {C D : PointedCone R M} {x : M}

/-- Algebraic relative interior, also known as core. -/
def relint (C : PointedCone R M) : ConvexCone R M where
  carrier := {x ∈ C | ∀ t ∈ span R C, ∃ c > (0 : R), x + c • t ∈ C}
  smul_mem' c hc x hx := by
    refine ⟨C.smul_mem hc.le hx.1, fun t ht ↦ ?_⟩
    obtain ⟨d, hd, hxd⟩ := hx.2 (c⁻¹ • t) (Submodule.smul_mem _ _ ht)
    refine ⟨d, hd, ?_⟩
    have := C.smul_mem hc.le hxd
    rwa [smul_add, smul_comm c d, smul_inv_smul₀ hc.ne'] at this
  add_mem' x hx y hy := by
    refine ⟨C.add_mem hx.1 hy.1, fun t ht ↦ ?_⟩
    obtain ⟨c, hc, hxc⟩ := hx.2 t ht
    refine ⟨c, hc, ?_⟩
    have := C.add_mem hxc hy.1
    rwa [add_assoc, add_comm (c • t) y, ← add_assoc] at this

lemma relint_le : C.relint ≤ C := fun _ hx => hx.1

lemma mem_relint_iff_forall_exists_gt_zero_forall_le_add_smul_mem :
    x ∈ C.relint ↔ x ∈ C ∧ ∀ t ∈ span R C, ∃ c > (0 : R), x + c • t ∈ C := by
  simp [relint]

lemma mem_relint_iff_mem_hull_neg_eq_top :
    x ∈ C.relint ↔ x ∈ C ∧ hull R (insert (-x) C) = Submodule.span R (C : Set M) := by
    sorry

lemma mem_relint_iff_mem_forall_isFaceOf_eq_top_of_mem :
    x ∈ C.relint ↔ x ∈ C ∧ ∀ F : PointedCone R M, F.IsFaceOf C → x ∈ F → F = C := by
  sorry

lemma mem_relint_iff_mem_forall_face_eq_top_of_mem :
    x ∈ C.relint ↔ x ∈ C ∧ ∀ F : Face C, x ∈ F → F = ⊤ := by
  sorry

variable [Fact p.SeparatingLeft] in
lemma mem_relint_iff_forall_dual_zero_le_mem_lineal_of_eq_zero :
    x ∈ C.relint ↔ x ∈ C ∧ ∀ y ∈ dual p C, p x y = 0 → y ∈ (dual p C).lineal := by
  sorry

variable [Fact p.SeparatingLeft] in
lemma mem_relint_dual {y : N} :
    y ∈ (dual p C).relint ↔ y ∈ dual p C ∧ ∀ x ∈ C, p x y = 0 → x ∈ C.lineal := by
  sorry

lemma finset_sum_mem_relint_of_subset_of_le_span {s : Finset M} (hs : (s : Set M) ⊆ C)
    (hC : C ≤ Submodule.span R (s : Set M)) : ∑ x ∈ s, x ∈ relint C := by
  sorry

lemma finset_sum_mem_relint_hull {s : Finset M} : ∑ x ∈ s, x ∈ relint (hull R (s : Set M)) := by
  sorry

lemma relint_nonempty_of_finSalRank (h : C.FinSalRank) : Nonempty C.relint := sorry

-- Easier to prove than `relint_nonempty`, perhaps prove this first.
lemma relint_nonempty_of_finRank (h : C.FinRank) : Nonempty C.relint := by
  /-
    * choose a basis of span R C in C
    * since C.FinRank, this basis is finite
    * use `finset_sum_mem_relint_of_subset_of_le_span`
  -/
  let := (Submodule.fg_iff_finiteDimensional _).mp h
  obtain ⟨s, hsC, _, hs, _⟩ := exists_finset_span_eq_linearIndepOn R (C : Set M)
  refine ⟨∑ x ∈ s, x, finset_sum_mem_relint_of_subset_of_le_span hsC ?_⟩
  intro x hx
  rw [hs]
  exact Submodule.subset_span hx

 -- potential short proof of `IsExposedFace.exists_dual_pos`
variable (p) [Fact p.SeparatingLeft] in
example {C : PointedCone R M} (hC : C.FinSalRank) :
    ∃ φ : N, ∀ x ∈ C, 0 ≤ p x φ ∧ (p x φ = 0 → x ∈ C.lineal) := by
  obtain ⟨φ, hφ⟩ := relint_nonempty_of_finSalRank (hC.dual_finSalRank p)
  rw [mem_relint_dual] at hφ
  exact ⟨φ, fun _ h => ⟨by simpa using hφ.1 h, hφ.2 _ h⟩⟩

lemma ofSubmodule_relint (S : Submodule R M) : (S : PointedCone R M).relint = S := by
  refine le_antisymm relint_le fun _ hx ↦ ⟨hx, fun _ ht ↦ ⟨1, zero_lt_one, ?_⟩⟩
  rw [one_smul]
  exact S.add_mem hx (by simpa using ht)

end PointedCone
