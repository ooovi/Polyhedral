/-
Copyright (c) 2025 Martin Winter, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter, Yaël Dillies
-/
import Mathlib.Algebra.Module.Submodule.Pointwise
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Projection

import Polyhedral.Mathlib.LinearAlgebra.BilinearMap -- imports Cardinal ... somehow
import Polyhedral.Mathlib.Algebra.Module.Submodule.Basic
import Polyhedral.Mathlib.Algebra.Module.Submodule.CoFG

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

lemma dual_univ_ker : dual p univ = ker p.flip := by
  ext x; simpa [Eq.comm] using (funext_iff (f := (0 : M →ₗ[R] R)) (g := p.flip x)).symm

variable [inst : Fact p.SeparatingRight] in
@[simp] lemma dual_univ : dual p univ = ⊥ := by
  simpa [dual_univ_ker, separatingRight_iff_flip_ker_eq_bot] using inst.elim

-- variable (p) [Fact p.IsFaithfulPair] in
-- @[simp] lemma dual_univ' : dual p univ = ⊥ := by
--   rw [le_antisymm_iff, and_comm]
--   constructor
--   · exact bot_le
--   obtain ⟨g, hg⟩ : p.IsFaithfulPair := Fact.elim inferInstance
--   simp only [SetLike.le_def, mem_dual, mem_univ, forall_const]
--   exact fun x h => hg x (@h (g x)).symm

alias dual_top := dual_univ

@[gcongr] lemma dual_le_dual (h : t ⊆ s) : dual p s ≤ dual p t := fun _y hy _x hx ↦ hy (h hx)

alias dual_antitone := dual_le_dual

/-- The inner dual cone of a singleton is given by the preimage of the positive cone under the
linear map `p x`. -/
lemma dual_singleton (x : M) : dual p {x} = ker (p x) := by
  ext x; simp [Eq.comm]

-- lemma dual_singleton' (x : M) : dual p {x} = (⊥ : Submodule R R).comap (p x) := by
--   simp; sorry

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

/-- The dual cone of `s` equals the intersection of dual cones of the points in `s`. -/
lemma dual_eq_Inf_dual_singleton (s : Set M) :
    dual p s = ⨅ x ∈ s, dual p {x} := by ext; simp

/-- The dual cone of `s` equals the intersection of dual cones of the points in `s`. -/
lemma dual_eq_Inf_dual_singleton' (s : Finset M) :
    dual p s = ⨅ x ∈ s, dual p {x} := by ext; simp

lemma dual_singleton_ker (x : M) : dual p {x} = ker (p x) := by ext; simp [Eq.comm]

/-- The dual is the kernel of a linear map into a free module. -/
lemma dual_ker_pi (s : Set M) : dual p s = ker (LinearMap.pi fun x : s => p x) := by
  simp only [dual_eq_Inf_dual_singleton s, ker_pi, dual_singleton, ← sInf_image, sInf_image']

/-- The dual is the kernel of a linear map into a free module. -/
lemma dual_ker_pi' (s : Finset M) : dual p s = ker (LinearMap.pi fun x : s => p x) := by
  simp [dual_ker_pi]

/-- The dual is the kernel of a linear map into a free module. -/
lemma dual_exists_fun_ker (s : Set M) : ∃ f : N →ₗ[R] (s → R), dual p s = ker f
    := ⟨_, dual_ker_pi s⟩

/-- The dual is the kernel of a linear map into a free module. -/
lemma dual_exists_fun_ker' (s : Finset M) : ∃ f : N →ₗ[R] (s → R), dual p s = ker f
    := ⟨_, dual_ker_pi' s⟩

/-- Any set is a subset of its double dual cone. -/
lemma subset_dual_dual : s ⊆ dual p.flip (dual p s) := fun _x hx _y hy ↦ hy hx

alias le_dual_dual := subset_dual_dual

-- variable (p) in
-- /-- Any cone is a subcone of its double dual cone. -/
-- lemma le_dual_dual (S : Submodule R M) : S ≤ dual p.flip (dual p S) := subset_dual_dual

lemma le_dual_of_le_dual {S : Submodule R M} {T : Submodule R N}
    (hST : T ≤ dual p S) : S ≤ dual p.flip T :=
  le_trans subset_dual_dual (dual_antitone hST)

lemma dual_le_iff_dual_le {S : Submodule R M} {T : Submodule R N} :
    S ≤ dual p.flip T ↔ T ≤ dual p S := ⟨le_dual_of_le_dual, le_dual_of_le_dual⟩

variable (p) in
/-- Any cone is a subcone of its double dual cone. -/
lemma dual_dual_mono {s t : Set M} (hST : s ⊆ t) :
    dual p.flip (dual p s) ≤ dual p.flip (dual p t) := by
  exact dual_antitone <| dual_antitone hST

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

/-- Conversion to the standard algebraic duality operator. -/
lemma dual_id (s : Set M) : dual p s = dual .id (p '' s) := by ext x; simp

lemma dual_id_map (S : Submodule R M) : dual p S = dual .id (map p S) := by ext x; simp

lemma dual_id_surj (s : Set (Dual R N)) (h : Surjective p) :
    dual p (surjInv h '' s) = dual .id s := by simp [dual_id, image_image,surjInv_eq]

variable [h : Fact (Surjective p)] in
lemma dual_exists_set_id (s : Set (Dual R N)) : ∃ t : Set M, dual p t = dual .id s := by
  use surjInv h.out '' s
  ext x; simp [surjInv_eq]

lemma dual_sup (S T : Submodule R M) : dual p (S ⊔ T : Submodule R M) = dual p (S ∪ T)
    := by nth_rw 2 [← dual_span]; simp

lemma dual_sup_dual_inf_dual (S T : Submodule R M) :
    dual p (S ⊔ T : Submodule R M) = dual p S ⊓ dual p T := by rw [dual_sup, dual_union]

/-- The dual submodule w.r.t. the standard dual map is the dual annihilator. -/
lemma dual_dualAnnihilator (S : Submodule R M) : dual (Dual.eval R M) S = S.dualAnnihilator := by
  ext x; simp; exact ⟨fun h _ hw => (h hw).symm, fun h w hw => (h w hw).symm⟩

/-- The dual submodule w.r.t. the standard dual map is the dual annihilator. -/
lemma dual_dualCoannihilator (S : Submodule R (Dual R M)) : dual .id S = S.dualCoannihilator := by
  ext x; simp; exact ⟨fun h _ hw => (h hw).symm, fun h w hw => (h w hw).symm⟩

lemma dual_dualCoannihilator' (S : Submodule R M) : dual p S = (map p S).dualCoannihilator := by
  ext x; simp; exact ⟨fun h _ hw => (h hw).symm, fun h w hw => (h w hw).symm⟩

-------------------

variable (p) in
abbrev dual' (S : Submodule R M) : Submodule R N := dual p S

-- variable (p) in
-- lemma dual_antimono' {S T : Submodule R M} (hST : S ≤ T) : dual p T ≤ dual p S := by
--   exact dual_antimono hST

lemma dual_gc' : GaloisConnection (toDual ∘ dual' p) (dual' p.flip ∘ ofDual) := by
  intro S T
  simp only [Function.comp_apply]
  nth_rw 1 [← toDual_ofDual T]
  rw [toDual_le_toDual]
  constructor <;>
    exact (le_trans subset_dual_dual <| dual_antitone ·)

def dual_gi : GaloisInsertion (dual' p ∘ ofDual) (toDual ∘ dual' p.flip) where
  choice S _ := toDual (dual' p S)
  gc := sorry -- dual_gc'
  le_l_u := fun _ => le_dual_dual
  choice_eq := by sorry

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

lemma dual_sSup (s : Set (Submodule R M)) :
    dual p (sSup s : Submodule R M) = dual p (sUnion (SetLike.coe '' s)) := by
  rw [sUnion_image]; nth_rw 2 [←dual_span]; rw [span_biUnion]

lemma dual_sup_dual_eq_inf_dual (S T : Submodule R M) :
    dual p (S ⊔ T : Submodule R M) = dual p S ⊓ dual p T := by rw [dual_sup, dual_union]

lemma dual_sSup_sInf_dual (s : Set (Submodule R M)) :
    dual p (sSup s : Submodule R M) = sInf (dual p '' (SetLike.coe '' s)) := by
  rw [dual_sSup, dual_sUnion]

lemma dual_sup_dual_le_dual_inf (S T : Submodule R M) :
    dual p S ⊔ dual p T ≤ dual p (S ⊓ T : Submodule R M) := by
  intro x h y ⟨hyS, hyT⟩
  simp only [mem_sup, mem_dual, SetLike.mem_coe] at h
  obtain ⟨x', hx', y', hy', hxy⟩ := h
  rw [← hxy, ← zero_add 0]
  nth_rw 1 [hx' hyS, hy' hyT, map_add]

----------------------

variable (p) in
abbrev IsDualClosed (S : Submodule R M) := dual p.flip (dual p S) = S

/-- A submodule is bipolar if it is equal to its double dual. -/
-- Potentially the more canonical name for `IsDualClosed`.
alias IsBipolar := IsDualClosed

@[simp] lemma IsDualClosed.def {S : Submodule R M} (hS : IsDualClosed p S) :
     dual p.flip (dual p S) = S := hS

lemma IsDualClosed.def_iff {S : Submodule R M} :
    IsDualClosed p S ↔ dual p.flip (dual p S) = S := by rfl

variable (p) in
@[simp] lemma dual_IsDualClosed (s : Set M) : (dual p s).IsDualClosed p.flip := by
  simp [IsDualClosed, flip_flip, dual_dual_flip_dual]

variable (p) in
@[simp] lemma dual_flip_IsDualClosed (s : Set N) : (dual p.flip s).IsDualClosed p
    := by simp [IsDualClosed]

lemma IsDualClosed.dual_inj {S T : Submodule R M} (hS : S.IsDualClosed p) (hT : T.IsDualClosed p)
    (hST : dual p S = dual p T) : S = T := by
  rw [← hS, ← hT, hST]

lemma IsDualClosed.dual_antitone_rev {S T : Submodule R M}
    (hS : S.IsDualClosed p) (hT : T.IsDualClosed p)
      (hST : dual p S ≤ dual p T) : T ≤ S := by
  rw [← hS, ← hT]; exact dual_antitone hST

lemma IsDualClosed.dual_le_of_dual_le {S : Submodule R M} {T : Submodule R N}
    (hS : S.IsDualClosed p) (hST : dual p S ≤ T) : dual p.flip T ≤ S := by
  rw [← hS]; exact dual_antitone hST

-- NOTE: This is the characterizing property of an antitone GaloisConnection.
lemma dual_le_iff_dual_le_of_isDualClosed {S : Submodule R M} {T : Submodule R N}
    (hS : S.IsDualClosed p) (hT : T.IsDualClosed p.flip) :
      dual p S ≤ T ↔ dual p.flip T ≤ S
    := ⟨hS.dual_le_of_dual_le, hT.dual_le_of_dual_le⟩

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
  exact ⟨subset_dual_dual, by simp only [top_coe, le_top]⟩

variable (p) in
@[simp] lemma dual_dual_top : dual p.flip (dual p ⊤) = ⊤
    := isDualClosed_top p

variable [Fact p.SeparatingLeft] in
@[simp] lemma isDualClosed_bot : IsDualClosed p ⊥ := by simp [IsDualClosed]

variable (p) [Fact p.SeparatingLeft] in
-- @[simp]
lemma dual_dual_bot : dual p.flip (dual p 0) = ⊥ := by simp

lemma IsDualClosed.inf {S T : Submodule R M}
    (hS : S.IsDualClosed p) (hT : T.IsDualClosed p) : (S ⊓ T).IsDualClosed p := by
  rw [← hS, ← hT, IsDualClosed, ← dual_sup_dual_eq_inf_dual, dual_flip_dual_dual_flip]

alias inf_isDualClosed := IsDualClosed.inf

lemma sInf_isDualClosed {s : Set (Submodule R M)} (hS : ∀ S ∈ s, S.IsDualClosed p) :
    (sInf s).IsDualClosed p := by
  have hs : s = dual p.flip '' (SetLike.coe '' (dual p '' (SetLike.coe '' s))) := by
    ext T; simp only [mem_image, exists_exists_and_eq_and]
    constructor
    · exact fun hT => ⟨T, hT, hS T hT⟩
    · intro h
      obtain ⟨t, hts, ht⟩ := h
      simpa [← ht, hS t hts] using hts
  rw [hs, ← dual_sSup_sInf_dual]
  exact dual_IsDualClosed _ _

-- variable (p) in
-- /-- The span of a set `s ⊆ M` is the smallest submodule of M that contains `s`. -/
-- def dualClosure (s : Set M) : Submodule R M := dual p.flip (dual p s)

-- lemma dualClosure_isDualClosed (s : Set M) : (dualClosure p s).IsDualClosed p := by
--   simp [dualClosure, IsDualClosed, dual_dual_flip_dual]

-- variable (p) in
-- theorem IsDualClosed.dualClosure_eq_sInf (s : Set M) :
--     dualClosure p s = sInf { S : Submodule R M | S.IsDualClosed p ∧ s ⊆ S } := by
--   rw [Eq.comm, le_antisymm_iff]
--   constructor
--   · exact sInf_le ⟨dual_IsDualClosed _ _, subset_dual_dual⟩
--   rw [SetLike.le_def]
--   intro x hx
--   simp only [mem_sInf, mem_setOf_eq, and_imp]
--   intro T hT hsT
--   rw [← hT]
--   exact (dual_dual_mono p hsT) hx

-- theorem IsDualClosed.eq_sInf {S : Submodule R M} (hS : S.IsDualClosed p) :
--     S = sInf { T : Submodule R M | T.IsDualClosed p ∧ S ≤ T } := by
--   nth_rw 1 [← hS]; exact dualClosure_eq_sInf p S

/- NOTE: This seems trivial. Perhaps this should not be its own lemma. 1. Find a shorter proof.
  Then replace where it is used (somewhere relating lineal). -/
/-- A dual closed submodule is the infiumum of all dual closed submodules that contain it. -/
theorem IsDualClosed.eq_sInf {S : Submodule R M} (hS : S.IsDualClosed p) :
    S = sInf { T : Submodule R M | T.IsDualClosed p ∧ S ≤ T } := by
  rw [Eq.comm, le_antisymm_iff]
  constructor
  · exact sInf_le ⟨hS, by simp⟩
  simp only [SetLike.le_def, mem_sInf, mem_setOf_eq, and_imp]
  intro x hx T hT hsT
  rw [← hT]; rw [← hS] at hx
  exact (dual_dual_mono p hsT) hx

-- !! Not true: S = ⊤, T = not dual closed
-- protected lemma IsDualClosed.inf {S T : Submodule R M} (hS : S.IsDualClosed p) :
--     (S ⊓ T).IsDualClosed p := by
--   rw [← hS]
--   sorry

-- This seems to be NOT TRUE!
-- lemma IsDualClosed.sup {S T : Submodule R M} (hS : S.IsDualClosed p) (hT : T.IsDualClosed p) :
--     (S ⊔ T).IsDualClosed p := by
--   obtain ⟨S', hSdc, rfl⟩ := hS.exists_of_dual_flip
--   obtain ⟨T', hTdc, rfl⟩ := hT.exists_of_dual_flip
--   unfold IsDualClosed
--   sorry

-- alias sup_isDualClosed := IsDualClosed.sup

lemma dual_inf_dual_sup_dual' {S T : Submodule R M} (hS : S.IsDualClosed p)
    (hT : T.IsDualClosed p) : dual p (S ∩ T) = dual p S ⊔ dual p T := by
  rw [le_antisymm_iff]
  constructor
  · rw [SetLike.le_def]
    simp [mem_sup]
    intro x hx
    sorry
  · sorry -- easy

  -- refine IsDualClosed.dual_inj (p := p) hS hT ?_
  -- rw [← IsDualClosed.dual_inj_iff hS hT]
  -- rw [← hS.def]

lemma dual_inf_dual_sup_dual_of_isDualClosed {S T : Submodule R M}
    (hS : S.IsDualClosed p) (hT : T.IsDualClosed p) :
    dual p (S ⊓ T : Submodule R M) = dual p S ⊔ dual p T := by

  sorry

---------------------

variable (p) in
lemma dual_dual_eval_le_dual_dual_bilin (s : Set M) :
    dual .id (dual (Dual.eval R M) s) ≤ dual p.flip (dual p s)
  := fun _ hx y hy => @hx (p.flip y) hy

lemma IsDualClosed.to_eval {S : Submodule R M} (hS : S.IsDualClosed p)
    : S.IsDualClosed (Dual.eval R M) := by
  have h := dual_dual_eval_le_dual_dual_bilin p S
  rw [hS] at h
  exact le_antisymm h subset_dual_dual

section Surjective

/- TODO: figure out what are the weakest conditions under which these results are true.
  is `IsPerfPair` really necessary? -/

variable {R M N : Type*}
  [CommRing R]
  [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]
  {p : M →ₗ[R] N →ₗ[R] R} [Fact (Surjective p.flip)]

variable (p) in
lemma dual_dual_bilin_eq_dual_dual_eval (s : Set M) :
    dual p.flip (dual p s) = dual .id (dual (Dual.eval R M) s) := by
  rw [le_antisymm_iff, and_comm]
  constructor
  · exact dual_dual_eval_le_dual_dual_bilin p s
  simp only [SetLike.le_def, mem_dual, SetLike.mem_coe, flip_apply, Dual.eval_apply, id_coe, id_eq]
  intro x hx y hy
  obtain ⟨x', hx'⟩ := (Fact.elim inferInstance : Surjective p.flip) y
  simp only [← hx', flip_apply] at hy
  specialize @hx x' hy
  rw [← flip_apply, hx'] at hx
  exact hx

variable (p) in
lemma IsDualClosed.to_bilin {S : Submodule R M} (hS : S.IsDualClosed (Dual.eval R M))
    : S.IsDualClosed p := by
  rw [IsDualClosed, dual_dual_bilin_eq_dual_dual_eval]
  exact hS

end Surjective

section Field

variable {R M N : Type*}
  [Field R]
  [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]
  {p : M →ₗ[R] N →ₗ[R] R}

variable (p)

-- TODO: do we need a `[Field R]`, or is `Surjective p` enough?
variable [Fact (Surjective p.flip)] in
/-- A submodule of a vector space is dual closed. -/
lemma isDualClosed (S : Submodule R M) : S.IsDualClosed p := by
  apply IsDualClosed.to_bilin
  nth_rw 1 [IsDualClosed, Dual.eval, flip_flip]
  rw [dual_dualCoannihilator, dual_dualAnnihilator]
  exact Subspace.dualAnnihilator_dualCoannihilator_eq

variable [Fact (Surjective p)] in
/-- Every submodule of a vector space is dual closed. -/
@[deprecated isDualClosed (since := "")]
lemma isDualClosed_flip (S : Submodule R N) : S.IsDualClosed p.flip := isDualClosed _ S

-- -- TODO: do we need a `[Field R]`, or is `Surjective p` enough?
-- variable [Fact (Surjective p)] in
-- /-- Every submodule of a vector space is dual closed. -/
-- lemma isDualClosed_flip (S : Submodule R N) : S.IsDualClosed p.flip := by
--   apply IsDualClosed.to_bilin
--   nth_rw 1 [IsDualClosed, Dual.eval, flip_flip]
--   rw [dual_dualCoannihilator, dual_dualAnnihilator]
--   exact Subspace.dualAnnihilator_dualCoannihilator_eq

-- variable [Fact (Surjective p.flip)] in
-- /-- Every submodule of a vector space is dual closed. -/
-- lemma isDualClosed (S : Submodule R M) : S.IsDualClosed p := isDualClosed_flip p.flip S

variable [Fact (Surjective p)] in
/-- Every submodule of a vector space is its own double dual. -/
@[simp] lemma dual_dual_flip (S : Submodule R N) : dual p (dual p.flip S) = S :=
    isDualClosed p.flip S

variable [Fact (Surjective p.flip)] in
/-- Every submodule of a vector space is its own double dual. -/
@[simp] lemma dual_flip_dual (S : Submodule R M) : dual p.flip (dual p S) = S :=
    dual_dual_flip p.flip S

variable [Fact (Surjective p)] in
lemma exists_set_dual (S : Submodule R N) : ∃ s : Set M, dual p s = S := by
  use dual p.flip S; exact dual_dual_flip p S

-- do we really need perf pair?
-- We need something, but maybe faithful suffices
variable [p.IsPerfPair] in
lemma dual_inf_dual_sup_dual (S T : Submodule R M) :
    dual p (S ∩ T) = dual p S ⊔ dual p T := by
  nth_rw 1 [← dual_flip_dual p S]
  nth_rw 1 [← dual_flip_dual p T]
  rw [← coe_inf]
  rw [← dual_sup_dual_inf_dual]
  exact dual_dual_flip p _



-- ### HIGH PRIORITY! This is needed in the cone theory!

lemma exists_smul_of_ker_le_ker {p q : M →ₗ[R] R} (h : ker p ≤ ker q) :
    ∃ a : R, q = a • p := by
  by_cases H : p = 0
  · exact ⟨0, by simpa [H] using h⟩
  rw [LinearMap.ext_iff] at H
  simp at H
  obtain ⟨x, hx⟩ := H
  use q x / p x
  ext y
  simp
  -- using hx, rewrite goal to
  --   qy px - qx py = 0
  --   q (y px - x py) = 0
  -- which, via h, follows from
  --   p (y px - x px) = 0
  -- which is true because this is just
  --   px py - py px = 0
  sorry

variable [Fact (Injective p)] in -- ! satisfied by both Dual.eval and .id
lemma dual_flip_dual_singleton (x : M) : dual p.flip (dual p {x}) = span R {x} := by
  ext y
  simp
  rw [mem_span_singleton]
  constructor
  · intro h
    obtain ⟨a, ha⟩ := exists_smul_of_ker_le_ker (fun _ hx => (h hx.symm).symm)
    use a
    rw [← LinearMap.map_smul] at ha
    have inj : Injective p := Fact.elim inferInstance
    replace ha := inj ha
    exact ha.symm
  · intro h _ hz
    obtain ⟨_, rfl⟩ := h
    simp [← hz]

-- variable [Fact (Injective p)] in
-- lemma IsDualClosed.singleton (x : M) : (span R {x}).IsDualClosed p := by
--   sorry -- TODO: derive from `singleton_dual_flip_dual` above

-- variable [Fact p.IsFaithfulPair] in
-- /- NOTE: in a field and with a surjective pairing, every submodule is dual closed. But maybe
--   if the submodule is FG, we don't need the surjective pairing, but a faithful one suffices. -/
-- lemma FG.dual_flip_dual_of_finite (s : Finset M) :
--     dual p.flip (dual p s) = span R s := sorry -- Submodule.dual_flip_dual p S

-- variable [Fact p.IsFaithfulPair] in
-- /- NOTE: in a field and with a surjective pairing, every submodule is dual closed. But maybe
--   if the submodule is FG, we don't need the surjective pairing, but a faithful one suffices. -/
-- lemma FG.dual_flip_dual {S : Submodule R M} (hS : S.FG) :
--     dual p.flip (dual p S) = S := sorry -- Submodule.dual_flip_dual p S

-- variable [Fact p.IsFaithfulPair] in
-- lemma FG.dual_dual_flip {S : Submodule R N} (hS : S.FG) : dual p (dual p.flip S) = S := by sorry

-- variable [Fact p.flip.IsFaithfulPair] in
-- /-- The span of a finite set is dual closed. -/
-- lemma isDualClosed_of_finite (s : Finset M) : IsDualClosed p (span R s) := by

--   sorry

-- variable [Fact p.flip.IsFaithfulPair] in
-- /-- An FG submodule is dual closed. -/
-- lemma FG.isDualClosed {S : Submodule R M} (hS : S.FG) : S.IsDualClosed p := by
--   sorry

------

-- vvvvv Work in Progress

-- **NOTE**: No need no Field so far!!

lemma exists_fun_dual_ker {ι : Type*} (f : M →ₗ[R] ((ι → R) →ₗ[R] R)) :
    ∃ g : (ι → R) →ₗ[R] (Dual R M), dual .id (LinearMap.range g) = ker f := by
  simp only [dual_dualCoannihilator, dualCoannihilator_range_eq_ker_flip]
  use f.flip; simp

lemma exists_fun_dual_ker' {ι : Type*} [Fintype ι] (f : M →ₗ[R] (ι → R)) :
    ∃ g : (ι → R) →ₗ[R] (Dual R M), dual .id (LinearMap.range g) = ker f := by
  let h := (Pi.basisFun R ι).constr (M' := R) R
  obtain ⟨g, hg⟩ := exists_fun_dual_ker (h.comp f)
  rw [LinearEquiv.ker_comp] at hg
  use g

lemma exists_fun_dual_ker'' {ι : Type*} [Fintype ι] (f : M →ₗ[R] (ι → R)) :
    ∃ g : ι → (Dual R M), dual .id (range g) = ker f := by
  obtain ⟨g, hg⟩ := exists_fun_dual_ker' f
  let h := (Pi.basisFun R ι).constr (M' := (Dual R M)) R
  use h.symm g
  rw [← hg]
  rw [← dual_span]
  unfold h
  -- rw [Basis.constr_apply]
  congr
  ext x
  simp [mem_span]
  constructor
  · intro h

    sorry
  · sorry

lemma exists_fun_dual_ker'''' {ι : Type*} [Fintype ι] (f : M →ₗ[R] (ι → R)) :
    ∃ g : ι → (Dual R M), dual .id (range g) = ker f := by classical
  let g := (Pi.basisFun R ι).constr (M' := R) R
  let f' := g.comp f
  use (f'.flip <| (Pi.basisFun R ι) ·)
  ext x
  simp
  -- rw [← flip_flip f']
  -- simp only [flip_apply f'.flip]
  -- unfold f'
  -- dsimp
  unfold f'; clear f'
  simp
  #check Pi.single
  constructor
  · intro h
    unfold g at h
  -- apply Module.Basis.forall_coord_eq_zero_iff
    -- rw [Pi.single_a]
    sorry
  · intro h
    rw [h]
    simp

variable [h : Fact (Surjective p)] in
lemma exists_fun_dual_ker''' {ι : Type*} [Fintype ι] (f : N →ₗ[R] (ι → R)) :
    ∃ g : ι → M, dual p (range g) = ker f := by
  obtain ⟨g, hg⟩ := exists_fun_dual_ker'' f
  use (surjInv h.out).comp g
  rw [← hg, range_comp]
  exact dual_id_surj _ _

variable [Fact (Surjective p)] in
lemma exists_finset_dual_ker' {ι : Type*} [Fintype ι] (f : N →ₗ[R] (ι → R)) :
    ∃ s : Finset M, dual p s = ker f := by
  obtain ⟨g, hg⟩ := exists_fun_dual_ker''' p f
  use (finite_range g).toFinset
  simpa using hg

end Field


-- ## COFG

section IsNoetherianRing

variable {R : Type*} [CommRing R] [IsNoetherianRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}

variable (p) in
theorem dual_singleton_cofg (x : M) : (dual p {x}).CoFG := by
  rw [dual_singleton]; exact ker_cofg _

variable (p) in
theorem dual_finset_cofg (s : Finset M) : (dual p s).CoFG := by
  rw [dual_ker_pi']; exact ker_cofg _

variable (p) in
theorem dual_finite_cofg {s : Set M} (hs : s.Finite) : (dual p s).CoFG := by
  rw [← hs.coe_toFinset]; exact dual_finset_cofg p hs.toFinset

variable (p) in
theorem dual_fg_cofg {S : Submodule R M} (hS : S.FG) : (dual p S).CoFG := by
  obtain ⟨s, rfl⟩ := hS
  simpa using dual_finset_cofg p s

end IsNoetherianRing


section Field

variable {R : Type*} [Field R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}

variable (p) [Fact p.SeparatingRight] in
theorem disjoint_dual_of_codisjoint {S T : Submodule R M} (hST : Codisjoint S T) :
    Disjoint (dual p S) (dual p T) := by
  rw [disjoint_iff]
  rw [← dual_sup_dual_inf_dual]
  rw [codisjoint_iff.mp hST]
  exact dual_univ

variable (p) [p.IsPerfPair] in
theorem codisjoint_dual_of_disjoint {S T : Submodule R M} (hST : Disjoint S T) :
    Codisjoint (dual p S) (dual p T) := by
  rw [codisjoint_iff]
  rw [← dual_inf_dual_sup_dual, ← coe_inf]
  rw [disjoint_iff.mp hST]
  simp only [bot_coe, dual_bot]

variable (p) [p.IsPerfPair] in
theorem IsCompl.dual {S T : Submodule R M} (hST : IsCompl S T) :
    IsCompl (dual p S) (dual p T) :=
  ⟨disjoint_dual_of_codisjoint p hST.codisjoint, codisjoint_dual_of_disjoint p hST.disjoint⟩


-- true ??
lemma dual_cofg_fg {S : Submodule R M} (hS : S.CoFG) : (dual p S).FG := sorry

end Field


end Submodule
