/-
Copyright (c) 2025 Martin Winter, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter, Yaël Dillies
-/
import Mathlib.Algebra.Module.Submodule.Pointwise
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Projection

import Polyhedral.Mathlib.Algebra.Module.Submodule.Basic
import Polyhedral.Mathlib.LinearAlgebra.BilinearMap -- imports Cardinal ... somehow

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

assert_not_exists TopologicalSpace Real -- Cardinal (comes with BilinearMap)

open Module Function LinearMap Pointwise Set OrderDual

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
@[simp] lemma dual_bot : dual p {0} = ⊤ := dual_zero

variable (p) [Fact p.IsFaithfulPair] in
@[simp] lemma dual_univ : dual p univ = ⊥ := by
  rw [le_antisymm_iff, and_comm]
  constructor
  · exact bot_le
  rw [SetLike.le_def]
  simp only [mem_dual, mem_univ, forall_const, mem_bot]
  intro x h
  obtain ⟨g, hg⟩ : p.IsFaithfulPair := Fact.elim inferInstance
  exact hg x (@h (g x)).symm

alias dual_top := dual_univ

-- SHOULD HAVE: variable (p) in
@[gcongr] lemma dual_le_dual (h : t ⊆ s) : dual p s ≤ dual p t := fun _y hy _x hx ↦ hy (h hx)

alias dual_antitone := dual_le_dual

/-- The inner dual cone of a singleton is given by the preimage of the positive cone under the
linear map `p x`. -/
lemma dual_singleton (x : M) : dual p {x} = (⊥ : Submodule R R).comap (p x) := by
  simp; sorry

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

/-- Any cone is a subcone of its double dual cone. -/
lemma le_dual_dual {S : Submodule R M} : S ≤ dual p.flip (dual p S) := subset_dual_dual

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

lemma dual_id (s : Set M) : dual p s = dual .id (p '' s) := by ext x; simp

lemma dual_id_map (S : Submodule R M) : dual p S = dual .id (map p S) := by ext x; simp

/-- The dual submodule w.r.t. the standard dual map is the dual annihilator. -/
lemma dual_dualAnnihilator (S : Submodule R M) : dual (Dual.eval R M) S = S.dualAnnihilator := by
  ext x; simp; exact ⟨fun h _ hw => (h hw).symm, fun h w hw => (h w hw).symm⟩

/-- The dual submodule w.r.t. the standard dual map is the dual annihilator. -/
lemma dual_dualCoannihilator (S : Submodule R (Dual R M)) : dual .id S = S.dualCoannihilator := by
  ext x; simp; exact ⟨fun h _ hw => (h hw).symm, fun h w hw => (h w hw).symm⟩

lemma dual_dualCoannihilator' (S : Submodule R M) : dual p S = (map p S).dualCoannihilator := by
  ext x; simp; exact ⟨fun h _ hw => (h hw).symm, fun h w hw => (h w hw).symm⟩

--------------------

-- **NEEDED** for `PointedCone.IsDualClosed.dual_lineal_span_dual`
lemma dual_sSup_sInf_dual (S : Set (Submodule R M)) :
    dual p (sSup S : Submodule R M) = sInf ((dual p ∘ SetLike.coe) '' S) := by
  sorry

-------------------

variable (p) in
abbrev dual' (S : Submodule R M) : Submodule R N := dual p S

-- variable (p) in
-- lemma dual_antimono' {S T : Submodule R M} (hST : S ≤ T) : dual p T ≤ dual p S := by
--   exact dual_antimono hST

lemma dual_gc' : GaloisConnection (toDual ∘ dual' p) (dual' p.flip ∘ ofDual) := by
  intro S T
  simp
  nth_rw 1 [← toDual_ofDual T]
  rw [toDual_le_toDual]
  constructor
  · intro h
    unfold dual' at *
    have h := dual_antitone (p := p.flip) h
    have h := dual_antitone (p := p) h
    rw [dual_dual_flip_dual] at h
    have h := dual_antitone (p := p.flip) h
    rw [dual_flip_dual_dual_flip] at h
    exact le_trans subset_dual_dual h
  · sorry

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

--------------

lemma dual_sup (S T : Submodule R M) :
    dual p (S ⊔ T : Submodule R M) = dual p (S ∪ T) := by
  nth_rw 2 [←dual_span]; rw [span_union']

lemma dual_sup_dual_eq_inf_dual (S T : Submodule R M) :
    dual p (S ⊔ T : Submodule R M) = dual p S ⊓ dual p T := by rw [dual_sup, dual_union]

lemma dual_sup_dual_le_dual_inf (S T : Submodule R M) :
    dual p S ⊔ dual p T ≤ dual p (S ⊓ T : Submodule R M) := by
  intro x h y ⟨hyS, hyT⟩
  simp only [mem_sup, mem_dual, SetLike.mem_coe] at h
  obtain ⟨x', hx', y', hy', hxy⟩ := h
  rw [← hxy, ← zero_add 0]
  nth_rw 1 [hx' hyS, hy' hyT, map_add]

-------------------

section CommSemiring

open LinearMap

variable {M S R : Type*} [CommSemiring R] [AddCommGroup M] [Module R M]

lemma IsCompl.dual {S T : Submodule R M} (hST : IsCompl S T) :
    IsCompl T.dualAnnihilator S.dualAnnihilator := by
  sorry

variable {M S R : Type*} [Field R] [AddCommGroup M] [Module R M]

lemma IsProj.dualMap_dual_Annihilator {S : Submodule R M} (p : M →ₗ[R] M) (hp : IsProj S p) :
    IsProj (ker p).dualAnnihilator p.dualMap where
  map_mem x := sorry
  map_id x hx := sorry

lemma IsCompl.projection_dual {S T : Submodule R M} (hST : IsCompl S T) :
    (projection hST).dualMap = projection (dual hST) := by
  sorry

-- lemma IsProj.dual {S : Submodule R M} {p : M →ₗ[R] M} (hp : LinearMap.IsProj S p) :
--     LinearMap.IsProj (p.ker.dualAnnihilator) p.dualMap := by sorry

end CommSemiring

----------------------

variable (p) in
abbrev IsDualClosed (S : Submodule R M) := dual p.flip (dual p S) = S

variable (p) in
@[simp] lemma IsDualClosed.def {S : Submodule R M} (hS : IsDualClosed p S) :
     dual p.flip (dual p S) = S := hS

variable (p) in
lemma IsDualClosed.def_iff {S : Submodule R M} :
    IsDualClosed p S ↔ dual p.flip (dual p S) = S := by rfl

variable (p) in
lemma dual_IsDualClosed (S : Submodule R M) : (dual p S).IsDualClosed p.flip := by
  simp [IsDualClosed, flip_flip, dual_dual_flip_dual]

variable (p) in
lemma dual_flip_IsDualClosed (S : Submodule R N) : (dual p.flip S).IsDualClosed p
    := by simp [IsDualClosed]

lemma IsDualClosed.dual_inj {S T : Submodule R M} (hS : S.IsDualClosed p) (hT : T.IsDualClosed p)
    (hST : dual p S = dual p T) : S = T := by
  rw [← hS, ← hT, hST]

@[simp] lemma IsDualClosed.dual_inj_iff {S T : Submodule R M} (hS : S.IsDualClosed p)
    (hT : T.IsDualClosed p) : dual p S = dual p T ↔ S = T := ⟨dual_inj hS hT, by intro h; congr ⟩

lemma IsDualClosed.exists_of_dual_flip {S : Submodule R M} (hS : S.IsDualClosed p) :
    ∃ T : Submodule R N, T.IsDualClosed p.flip ∧ dual p.flip T = S
  := ⟨dual p S, by simp [IsDualClosed, hS.def]⟩

lemma IsDualClosed.exists_of_dual {S : Submodule R N} (hS : S.IsDualClosed p.flip) :
    ∃ T : Submodule R M, T.IsDualClosed p ∧ dual p T = S := by
  rw [← flip_flip p]; exact hS.exists_of_dual_flip

variable (p) in
lemma isDualClosed_top : IsDualClosed p ⊤ := by
  rw [IsDualClosed, le_antisymm_iff, and_comm]
  exact ⟨le_dual_dual, by simp⟩

variable (p) in
@[simp] lemma dual_dual_top : dual p.flip (dual p ⊤) = ⊤
    := isDualClosed_top p

variable (p) [Fact p.flip.IsFaithfulPair] in
lemma isDualClosed_bot : IsDualClosed p ⊥ := by simp [IsDualClosed]

variable (p) [Fact p.flip.IsFaithfulPair] in
-- @[simp]
lemma dual_dual_bot : dual p.flip (dual p 0) = ⊥ := by simp





-- NOTE: we want this for only one of the spaces being dual closed. But this version is
--  useful in the cone case.
lemma IsDualClosed.inf' {S T : Submodule R M} (hS : S.IsDualClosed p) (hT : T.IsDualClosed p) :
    (S ⊓ T).IsDualClosed p := by
  rw [← hS, ← hT, IsDualClosed, ← dual_sup_dual_eq_inf_dual, dual_flip_dual_dual_flip]

lemma IsDualClosed.inf {S T : Submodule R M} (hS : S.IsDualClosed p) :
    (S ⊓ T).IsDualClosed p := by
  rw [← hS]
  sorry

lemma IsDualClosed.sup {S T : Submodule R M} (hS : S.IsDualClosed p) (hT : T.IsDualClosed p) :
    (S ⊔ T).IsDualClosed p := by
  obtain ⟨S', hSdc, rfl⟩ := hS.exists_of_dual_flip
  obtain ⟨T', hTdc, rfl⟩ := hT.exists_of_dual_flip
  sorry

lemma dual_inf_dual_sup_dual' {S T : Submodule R M} (hS : S.IsDualClosed p)
    (hT : T.IsDualClosed p) : dual p (S ⊓ T : Submodule R M) = dual p S ⊔ dual p T := by
  -- refine IsDualClosed.dual_inj (p := p) hS hT ?_
  -- rw [← IsDualClosed.dual_inj_iff hS hT]
  -- rw [← hS.def]
  sorry

lemma dual_inf_dual_sup_dual {S T : Submodule R M} (hS : S.IsDualClosed p) :
    dual p (S ⊓ T : Submodule R M) = dual p S ⊔ dual p T := by
  sorry

variable (p) [Fact p.flip.IsFaithfulPair] in
lemma IsDualClosed.singleton (x : M) : (span R {x}).IsDualClosed p := by
  unfold IsDualClosed
  rw [le_antisymm_iff, and_comm]
  constructor
  · exact le_dual_dual
  rw [SetLike.le_def]
  simp only [dual_span, mem_dual, SetLike.mem_coe, mem_singleton_iff, forall_eq, flip_apply]
  obtain ⟨g, hg⟩ : p.flip.IsFaithfulPair := Fact.elim inferInstance
  intro y h
  simp at hg
  --
  specialize hg y
  specialize @h (g y)
  rw [Eq.comm] at hg
  have H := hg ∘ h
  sorry

variable (p) in
lemma IsDualClosed.to_eval {S : Submodule R M} (hS : S.IsDualClosed p)
    : S.IsDualClosed (Dual.eval R M) := by
  sorry

-- **NEEDED** in `Submodule.isDualClosed` below
variable (p) [Fact p.flip.IsFaithfulPair] in
lemma IsDualClosed.to_bilin {S : Submodule R M} (hS : S.IsDualClosed (Dual.eval R M))
    : S.IsDualClosed p := by
  rw [IsDualClosed, Eq.comm, le_antisymm_iff]
  constructor
  · exact le_dual_dual
  nth_rw 2 [← hS]
  nth_rw 1 [Dual.eval, flip_flip]
  rw [dual_id]
  apply dual_antitone
  rw [← map_coe, SetLike.coe_subset_coe]
  -- What to do now?
  --
  rw [SetLike.le_def]
  simp only [mem_dual, SetLike.mem_coe, Dual.eval_apply, mem_map]
  intro x hx
  obtain ⟨g, hg⟩ : p.flip.IsFaithfulPair := Fact.elim inferInstance


  -- What to do now?
  ---
  -- rw [dual_id]
  -- nth_rw 2 [dual_id]

  sorry


section Field

variable {R M N : Type*}
  [Field R]
  [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]
  {p : M →ₗ[R] N →ₗ[R] R}

variable (p) [Fact p.flip.IsFaithfulPair] in
/-- Every submodule of a vector space is dual closed. -/
lemma isDualClosed (S : Submodule R M) : S.IsDualClosed p := by
  apply IsDualClosed.to_bilin
  nth_rw 1 [IsDualClosed, Dual.eval, flip_flip]
  rw [dual_dualCoannihilator, dual_dualAnnihilator]
  exact Subspace.dualAnnihilator_dualCoannihilator_eq

variable (p) [Fact p.flip.IsFaithfulPair] in
/-- Every submodule of a vector space is its own double dual. -/
lemma dual_dual (S : Submodule R M) : dual p.flip (dual p S) = S := isDualClosed p S

end Field

end Submodule
