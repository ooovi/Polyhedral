/-
Copyright (c) 2025 Martin Winter, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter, Yaël Dillies
-/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Order.OmegaCompletePartialOrder

-- only needed temporarily
import Mathlib.Geometry.Convex.Cone.Pointed

/-!
# The algebraic dual of a cone

Given a bilinear pairing `p` between two `R`-modules `M` and `N` and a set `s` in `M`, we define
`PointedCone.dual p s` to be the pointed cone in `N` consisting of all points `y` such that
`0 ≤ p x y` for all `x ∈ s`.

When the pairing is perfect, this gives us the algebraic dual of a cone. This is developed here.
When the pairing is continuous and perfect (as a continuous pairing), this gives us the topological
dual instead. See `Mathlib/Analysis/Convex/Cone/Dual.lean` for that case.

## Implementation notes

We do not provide a `ConvexCone`-valued version of `PointedCone.dual` since the dual cone of any set
always contains `0`, i.e. is a pointed cone.
Furthermore, the strict version `{y | ∀ x ∈ s, 0 < p x y}` is a candidate to the name
`ConvexCone.dual`.

## TODO

Deduce from `dual_flip_dual_dual_flip` that polyhedral cones are invariant under taking double duals
-/

assert_not_exists TopologicalSpace Real Cardinal

open Function LinearMap Pointwise Set OrderDual

namespace Submodule.Dual

variable {S R M N : Type*}
  [CommSemiring S]
  [CommSemiring R] [Algebra S R]
  [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N] [Module S N] [IsScalarTower S R N]
  {C : Submodule S R}
  {p : M →ₗ[R] N →ₗ[R] R}

variable (C p) in
/-- The dual cone of a set `s` with respect to a bilinear pairing `p` is the cone consisting of all
points `y` such that for all points `x ∈ s` we have `p x y ∈ C`. -/
def dual (s : Set M) : Submodule S N where
  carrier := {y | ∀ ⦃x⦄, x ∈ s → p x y ∈ C}
  zero_mem' := by simp
  add_mem' {u v} hu hv x hx := by rw [map_add]; exact C.add_mem (hu hx) (hv hx)
  smul_mem' c y hy x hx := by
    rw [← algebraMap_smul R, map_smul, algebraMap_smul]
    exact C.smul_mem c (hy hx)

variable {s t : Set M} {y : N}

@[simp] lemma mem_dual : y ∈ dual C p s ↔ ∀ ⦃x⦄, x ∈ s → p x y ∈ C := .rfl

@[simp] lemma dual_empty : dual C p ∅ = ⊤ := by ext; simp
@[simp] lemma dual_zero : dual C p 0 = ⊤ := by ext; simp

-- TODO: only true conditionally (e.g. not true for C = ⊤)
-- @[simp] lemma dual_univ' (hp : Injective p.flip) (hC : C.salient) : dual C p univ = ⊥ := by
--   ext x; simp
--   refine le_antisymm (fun y hy ↦ (_root_.map_eq_zero_iff p.flip hp).1 ?_) (by simp)
--   ext x
--   have h := hy (mem_univ x)
--   simp
--   sorry

@[gcongr] lemma dual_le_dual (h : t ⊆ s) : dual C p s ≤ dual C p t := fun _y hy _x hx ↦ hy (h hx)

/-- The inner dual cone of a singleton is given by the preimage of the positive cone under the
linear map `p x`. -/
-- lemma dual_singleton (x : M) : dual C p {x} = (positive R R).comap (p x) := by ext; simp

lemma dual_union (s t : Set M) : dual C p (s ∪ t) = dual C p s ⊓ dual C p t := by aesop

lemma dual_insert (x : M) (s : Set M) : dual C p (insert x s) = dual C p {x} ⊓ dual C p s := by
  rw [insert_eq, dual_union]

lemma dual_iUnion {ι : Sort*} (f : ι → Set M) : dual C p (⋃ i, f i) = ⨅ i, dual C p (f i) := by
  ext; simp [forall_swap (α := M)]

lemma dual_sUnion (S : Set (Set M)) : dual C p (⋃₀ S) = sInf (dual C p '' S) := by
  ext; simp [forall_swap (α := M)]

/-- The dual cone of `s` equals the intersection of dual cones of the points in `s`. -/
lemma dual_eq_iInter_dual_singleton (s : Set M) :
    dual C p s = ⋂ i : s, (dual C p {i.val} : Set N) := by ext; simp

variable [Module S M] [IsScalarTower S R M]

/-- Any set is a subset of its double dual cone. -/
lemma subset_dual_dual : s ⊆ dual C p.flip (dual C p s) := fun _x hx _y hy ↦ hy hx

variable (s) in
@[simp] lemma dual_dual_flip_dual : dual C p (dual C p.flip (dual C p s)) = dual C p s :=
  le_antisymm (dual_le_dual subset_dual_dual) subset_dual_dual

@[simp] lemma dual_flip_dual_dual_flip (s : Set N) :
    dual C p.flip (dual C p (dual C p.flip s)) = dual C p.flip s := dual_dual_flip_dual _

@[simp]
lemma dual_span (s : Set M) : dual C p (Submodule.span S s) = dual C p s := by
  refine le_antisymm (dual_le_dual Submodule.subset_span) (fun x hx y hy => ?_)
  induction hy using Submodule.span_induction with
  | mem _y h => exact hx h
  | zero => simp
  | add y z _hy _hz hy hz => rw [map_add, add_apply]; exact C.add_mem hy hz
  | smul t y _hy hy =>
      rw [← algebraMap_smul R, map_smul, algebraMap_smul, smul_apply]
      exact C.smul_mem t hy

variable (p) in
/-- Duality of submodules. -/
abbrev dual' := dual (⊥ : Submodule R R) p

example (s : Set M) : s ≤ dual' p.flip (dual' p s) := subset_dual_dual

section OrderedRing

variable [PartialOrder R] [IsOrderedRing R]

instance : Algebra {c : R // 0 ≤ c} R where
  algebraMap := Nonneg.coeRingHom
  commutes' r x := mul_comm ..
  smul_def' r x := by aesop

variable (p) in
/-- Duality of pointed cones. -/
abbrev dual'' := dual (PointedCone.positive R R) p

example (s : Set M) : s ≤ dual'' p.flip (dual'' p s) := subset_dual_dual

end OrderedRing

def IsDualClosed (T : Submodule S M) := dual C p.flip (dual C p T) = T

end Submodule.Dual
