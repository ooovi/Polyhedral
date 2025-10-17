/-
Copyright (c) 2025 Martin Winter, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter, Yaël Dillies
-/
import Mathlib.Algebra.Module.Submodule.Pointwise
import Mathlib.LinearAlgebra.BilinearMap
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

open Module Function LinearMap Pointwise Set

namespace Submodule

variable {R M N : Type*}
  [CommSemiring R]
  [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]
  {p : M →ₗ[R] N →ₗ[R] R} {s t : Set M} {y : N}

-- TODO: I think `dual` should be renamed to `dualSpan` or so, and `dual` should become a map
--  from subspaces to subspaces. This allows us to implement it as a `PreDualityOperator`.

variable (p s) in
/-- The dual cone of a set `s` with respect to a bilinear pairing `p` is the cone consisting of all
points `y` such that for all points `x ∈ s` we have `0 ≤ p x y`. -/
def dual : Submodule R N where
  carrier := {y | ∀ ⦃x⦄, x ∈ s → 0 = p x y}
  zero_mem' := by simp
  add_mem' {u v} hu hv x hx := by rw [map_add, ← hu hx, ← hv hx, add_zero]
  smul_mem' c y hy x hx := by rw [map_smul, ← hy hx, smul_eq_mul, mul_zero]

@[simp] lemma mem_dual : y ∈ dual p s ↔ ∀ ⦃x⦄, x ∈ s → 0 = p x y := .rfl

@[simp] lemma dual_empty : dual p ∅ = ⊤ := by ext; simp
@[simp] lemma dual_zero : dual p 0 = ⊤ := by ext; simp

lemma dual_univ (hp : Injective p.flip) : dual p univ = 0 := by
  refine le_antisymm (fun y hy ↦ (_root_.map_eq_zero_iff p.flip hp).1 ?_) (by simp)
  ext x
  simp [hy (mem_univ x)]

@[gcongr] lemma dual_le_dual (h : t ⊆ s) : dual p s ≤ dual p t := fun _y hy _x hx ↦ hy (h hx)

alias dual_antimono := dual_le_dual

/-- The inner dual cone of a singleton is given by the preimage of the positive cone under the
linear map `p x`. -/
-- lemma dual_singleton (x : M) : dual p {x} = (positive R R).comap (p x) := by ext; simp

lemma dual_union (s t : Set M) : dual p (s ∪ t) = dual p s ⊓ dual p t := by aesop

lemma dual_insert (x : M) (s : Set M) : dual p (insert x s) = dual p {x} ⊓ dual p s := by
  rw [insert_eq, dual_union]

lemma dual_iUnion {ι : Sort*} (f : ι → Set M) : dual p (⋃ i, f i) = ⨅ i, dual p (f i) := by
  ext; simp [forall_swap (α := M)]

lemma dual_sUnion (S : Set (Set M)) : dual p (⋃₀ S) = sInf (dual p '' S) := by
  ext; simp [forall_swap (α := M)]

/-- The dual cone of `s` equals the intersection of dual cones of the points in `s`. -/
lemma dual_eq_iInter_dual_singleton (s : Set M) :
    dual p s = ⋂ i : s, (dual p {i.val} : Set N) := by ext; simp

/-- Any set is a subset of its double dual cone. -/
lemma subset_dual_dual : s ⊆ dual p.flip (dual p s) := fun _x hx _y hy ↦ hy hx

variable (s) in
@[simp] lemma dual_dual_flip_dual : dual p (dual p.flip (dual p s)) = dual p s :=
  le_antisymm (dual_le_dual subset_dual_dual) subset_dual_dual

@[simp] lemma dual_flip_dual_dual_flip (s : Set N) :
    dual p.flip (dual p (dual p.flip s)) = dual p.flip s := dual_dual_flip_dual _

@[simp]
lemma dual_span (s : Set M) : dual p (Submodule.span R s) = dual p s := by
  refine le_antisymm (dual_le_dual Submodule.subset_span) (fun x hx y hy => ?_)
  induction hy using Submodule.span_induction with
  | mem _y h => exact hx h
  | zero => simp
  | add y z _hy _hz hy hz => rw [map_add, add_apply, ← hy, ← hz, add_zero]
  | smul t y _hy hy => simp only [map_smul, smul_apply, smul_eq_mul, ← hy, mul_zero]

-- ----------------

/-- The dual submodule w.r.t. the standard dual map is the dual annihilator. -/
lemma dual_dualAnnihilator (S : Submodule R M) : dual (Dual.eval R M) S = S.dualAnnihilator := by
  ext x; simp; exact ⟨fun h _ hw => (h hw).symm, fun h w hw => (h w hw).symm⟩


------------------

-- variable (p) in
-- abbrev dual' (S : Submodule R M) : Submodule R N := dual p S

-- lemma dual_mono' {S T : Submodule R M} (hST : S ≤ T) : dual p T ≤ dual p S := by
--   exact dual_mono hST

------------------

variable {M' N' : Type*}
  [AddCommMonoid M'] [Module R M']
  [AddCommMonoid N'] [Module R N']


lemma dual_bilin_dual_id (s : Set M) : dual p s = dual .id (p '' s) := by ext x; simp

lemma dual_bilin_dual_id_submodule (S : Submodule R M) : dual p S = dual .id (map p S) := by
  rw [map_coe, dual_bilin_dual_id]

-- variable {p : M →ₗ[R] N →ₗ[R] R} {p' : M' →ₗ[R] N' →ₗ[R] R}

-- lemma dual_map_foo {p : (Dual R M) →ₗ[R] N →ₗ[R] R}
--     (f : (Dual R M) →ₗ[R] (Dual R M)) (s : Set (Dual R M)) :
--     dual p (f '' s) --= dual .id ((p ∘ₗ f) '' s)
--                     = comap (p ∘ₗ f).dualMap (dual (Dual.eval R (Dual R M)) s)
--                     := by
--   ext x; simp

-- lemma dual_map_foo' (f : M →ₗ[R] M) (s : Set M) :
--     dual p (f '' s) = dual .id ((p ∘ f) '' s)
--                     --= comap (p ∘ₗ f).dualMap (dual .id s)
--                     := by
--   ext x; simp

-- TODO: generalize to arbitrary pairings (but what takes the place of `f.dualMap`?)
lemma dual_map (f : M →ₗ[R] M') (s : Set M) :
    comap f.dualMap (dual (Dual.eval R M) s) = dual (Dual.eval R M') (f '' s) := by
  ext x; simp

lemma dual_map' (f : M →ₗ[R] M') (s : Set (Dual R M')) :
    comap f (dual .id s) = dual .id (f.dualMap '' s) := by
  ext x; simp

lemma dual_sup (S T : Submodule R M) :
    dual p (S ⊔ T : Submodule R M) = dual p (S ∪ T) := by
  nth_rw 2 [←dual_span]; sorry

lemma dual_sup_dual_inf_dual (S T : Submodule R M) :
    dual p (S ⊔ T : Submodule R M) = dual p S ⊓ dual p T := by rw [dual_sup, dual_union]

lemma dual_inf_dual_sup_dual (S T : Submodule R M) :
    dual p (S ⊓ T : Submodule R M) = dual p S ⊔ dual p T := by
  ext x
  simp [mem_sup]
  constructor
  · intro h
    -- x can be written as the sum of y and z, where y is in S* and z is in T*
    sorry
  · intro h y hyS hyT
    obtain ⟨x', hx', y', hy', hxy⟩ := h
    specialize hx' hyS
    specialize hy' hyT
    rw [← hxy, ← zero_add 0]
    nth_rw 1 [hx', hy']
    simp

end Submodule
