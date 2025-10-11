/-
Copyright (c) 2025 Martin Winter, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter, Yaël Dillies
-/
import Mathlib.Algebra.Module.Submodule.Pointwise
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.RingTheory.Ideal.Defs
import Mathlib.Algebra.Order.Nonneg.Module
import Mathlib.Geometry.Convex.Cone.Basic
import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.LinearAlgebra.Dual.Defs

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

open Function LinearMap Pointwise Set

namespace Submodule
variable {S R M N : Type*}
  [CommSemiring S]
  [CommSemiring R] [Module S R]
  [AddCommMonoid M] [Module R M] -- [Module S M] -- [IsScalarTower S R M]
  [AddCommMonoid N] [Module R N] [Module S N] -- [IsScalarTower S R N]
  [MulActionHomClass (N →ₗ[R] R) S N R] -- [MulActionHomClass (M →ₗ[R] R) S M R]
  {p : M →ₗ[R] N →ₗ[R] R}
  {C : Submodule S R}
  {s t : Set M} {y : N}

variable (C p s) in
/-- The dual cone of a set `s` with respect to a bilinear pairing `p` is the cone consisting of all
points `y` such that for all points `x ∈ s` we have `0 ≤ p x y`. -/
def dual : Submodule S N where
  carrier := {y | ∀ ⦃x⦄, x ∈ s → p x y ∈ C}
  zero_mem' := by simp
  add_mem' {u v} hu hv x hx := by rw [map_add]; exact C.add_mem (hu hx) (hv hx)
  smul_mem' c y hy x hx := by rw [map_smul]; exact C.smul_mem c (hy hx)

@[simp] lemma mem_dual : y ∈ dual p C s ↔ ∀ ⦃x⦄, x ∈ s → p x y ∈ C := .rfl

@[simp] lemma dual_empty : dual p C ∅ = ⊤ := by ext; simp
@[simp] lemma dual_zero : dual p C 0 = ⊤ := by ext; simp

lemma dual_univ (hp : Injective p.flip) : dual p C univ = 0 := by
  refine le_antisymm (fun y hy ↦ (_root_.map_eq_zero_iff p.flip hp).1 ?_) (by simp)
  ext x
  have h := hy (mem_univ x)
  simp
  sorry

@[gcongr] lemma dual_le_dual (h : t ⊆ s) : dual p C s ≤ dual p C t := fun _y hy _x hx ↦ hy (h hx)

/-- The inner dual cone of a singleton is given by the preimage of the positive cone under the
linear map `p x`. -/
-- lemma dual_singleton (x : M) : dual p C {x} = (positive R R).comap (p x) := by ext; simp

lemma dual_union (s t : Set M) : dual p C (s ∪ t) = dual p C s ⊓ dual p C t := by aesop

lemma dual_insert (x : M) (s : Set M) : dual p C (insert x s) = dual p C {x} ⊓ dual p C s := by
  rw [insert_eq, dual_union]

lemma dual_iUnion {ι : Sort*} (f : ι → Set M) : dual p C (⋃ i, f i) = ⨅ i, dual p C (f i) := by
  ext; simp [forall_swap (α := M)]

lemma dual_sUnion (S : Set (Set M)) : dual p C (⋃₀ S) = sInf (dual p C '' S) := by
  ext; simp [forall_swap (α := M)]

/-- The dual cone of `s` equals the intersection of dual cones of the points in `s`. -/
lemma dual_eq_iInter_dual_singleton (s : Set M) :
    dual p C s = ⋂ i : s, (dual p C {i.val} : Set N) := by ext; simp

variable [Module S M] [MulActionHomClass (M →ₗ[R] R) S M R]

/-- Any set is a subset of its double dual cone. -/
lemma subset_dual_dual : s ⊆ dual p.flip C (dual p C s) := fun _x hx _y hy ↦ hy hx

variable (s) in
@[simp] lemma dual_dual_flip_dual : dual p C (dual p.flip C (dual p C s)) = dual p C s :=
  le_antisymm (dual_le_dual subset_dual_dual) subset_dual_dual

@[simp] lemma dual_flip_dual_dual_flip (s : Set N) :
    dual p.flip C (dual p C (dual p.flip C s)) = dual p.flip C s := dual_dual_flip_dual _

-- omit [Module S M] omit [MulActionHomClass (M →ₗ[R] R) S M R]

variable [SMulCommClass R S R] [MulActionHomClass (M →ₗ[R] N →ₗ[R] R) S M (N →ₗ[R] R)]
omit [MulActionHomClass (M →ₗ[R] R) S M R]

-- variable (C : Ideal R)

@[simp]
lemma dual_span (s : Set M) : dual p C (Submodule.span S s) = dual p C s := by
  refine le_antisymm (dual_le_dual Submodule.subset_span) (fun x hx y hy => ?_)
  induction hy using Submodule.span_induction with
  | mem _y h => exact hx h
  | zero => simp
  | add y z _hy _hz hy hz => rw [map_add, add_apply]; exact C.add_mem hy hz
  | smul t y _hy hy => rw [map_smul, smul_apply]; exact C.smul_mem t hy

variable (p s) in
def dual' := dual p ⊥ s

variable [PartialOrder R] [IsOrderedRing R]

-- variable (p s) in
-- def polar := dual p (PointedCone.positive R R) s

-- section CoFG

-- omit [Module S M]
--   [SMulCommClass R S R]
--   [MulActionHomClass (M →ₗ[R] N →ₗ[R] R) S M (N →ₗ[R] R)]
--   [PartialOrder R]
--   [IsOrderedRing R]

-- open Module

-- -- definde in analogy to FG := ∃ S : Finset M, Submodule.span R ↑S = N
-- variable (R C) in
-- def CoFG (T : Submodule S M) : Prop :=
--   ∃ s : Finset (Dual R M), dual .id C s = T

-- lemma dual_bilin_dual_id (s : Set M) : dual p C s = dual .id C (p '' s):= by ext x; simp

-- variable [MulActionHomClass (R →ₗ[R] R) S R R]

-- -- NOTE: converse is not true
-- lemma cofg_intro (T : Submodule S M) (hT : ∃ s : Finset N, dual p.flip C s = T) : T.CoFG R C := by
--   classical
--   obtain ⟨S, hS⟩ := hN
--   use Finset.image p S
--   rw [Finset.coe_image, ← hS, ← dual_bilin_dual_id]

-- -- lemma cofg_def_fg (N : Submodule R E) (hN : N.CoFG) :
-- --     ∃ M : Submodule R (Dual R E), M.FG ∧ dual .id M = N := by
-- --   obtain ⟨S, hS⟩ := hN
-- --   exact ⟨span R S, ⟨S, rfl⟩, by rw [dual_span, hS]⟩

-- lemma cofg_of_dual_fg (N : Submodule R F) (hN : ∃ M : Submodule R E, M.FG ∧ dual p M = N) :
--     N.CoFG := by sorry
--   -- obtain ⟨M, ⟨S, hS⟩, hM⟩ := hN
--   -- refine cofg_intro (E := E) (p := p) N ?_
--   -- exact ⟨S, by rw [← dual_span, hS, hM]⟩

-- lemma cofg_of_dual_fg' (N : Submodule R F) (M : Submodule R E) (hM : M.FG) (hN : dual p M = N) :
--     N.CoFG := cofg_of_dual_fg N ⟨M, hM, hN⟩

-- lemma dual_cofg_iff_fg (N : Submodule R E) : N.FG → (dual p N).CoFG
--   := (cofg_of_dual_fg' _ N · rfl)

-- -- @[simp]
-- lemma dual_fg_iff_cofg (N : Submodule R E) : N.CoFG → (dual p N).FG := sorry

-- end CoFG

end Submodule
