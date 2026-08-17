/-
Copyright (c) 2025 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/

import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.Geometry.Convex.Cone.Dual

import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Basic
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Lineal

/-! This file proves results about `PointedCone.dual` intended to go into Pointed/Dual. -/

namespace PointedCone

open Module LinearMap
open Submodule (span)

variable {R : Type*} [CommRing R] [PartialOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}

-- `PointedCone.map` should be an abbrev

@[deprecated dual_zero (since := "")]
alias dual_bot := dual_zero

-- For the proof, see the analogous statement for submodules
lemma dual_top_iff_le_ker {C : PointedCone R M} : dual p C = ⊤ ↔ C ≤ ker p := sorry
  -- constructor <;> intro h
  -- · intro x hx
  --   simp [Submodule.ext_iff] at h
  --   simp only [Submodule.ext_iff, mem_dual, SetLike.mem_coe, Submodule.mem_top, iff_true] at h
  --   simpa using inst.elim x (fun y => (h y hx).symm)
  -- · simp only [SeparatingLeft.ker_eq_bot, le_bot_iff] at h
  --   simp [h]

lemma dual_univ_ker : dual p .univ = ker p.flip := by
  ext x
  simp_rw [mem_dual, Set.mem_univ, forall_const, Submodule.restrictScalars_mem,
    mem_ker, LinearMap.ext_iff, flip_apply, zero_apply]
  constructor <;> intro h y
  · exact le_antisymm (by simpa using @h (-y)) (@h y)
  · rw [h y]

lemma dual_flip_univ_ker : dual p.flip .univ = ker p := by
  nth_rw 2 [← flip_flip p]; exact dual_univ_ker

-- Better version of dual.univ
variable [Fact p.SeparatingRight] in
@[simp] lemma dual_univ' : dual p .univ = ⊥ := by simp [dual_univ_ker]

-- TODO: are there instances missing that should make the proof automatic?
-- TODO: 0 in `dual_univ` simplifies to ⊥, so maybe it is not the best statement?
@[simp] lemma dual_top [p.IsPerfPair] : dual p .univ = ⊥
  := dual_univ (IsPerfPair.bijective_right p).1

variable (p) in
@[simp] lemma dual_eq_submodule_dual (S : Submodule R M) : dual p S = Submodule.dual p S := by
  ext x; constructor
  · intro h _ ha
    have h' := h (neg_mem_iff.mpr ha)
    simp only [LinearMap.map_neg, neg_apply, Left.nonneg_neg_iff] at h'
    exact le_antisymm (h ha) h'
  · intro h _ ha
    rw [h ha]

alias coe_dual := dual_eq_submodule_dual

@[simp]
lemma dual_coe_coe_eq_dual_coe (S : Submodule R M) : dual p (S : PointedCone R M) = dual p S := by
  rw [Submodule.coe_restrictScalars, dual_eq_submodule_dual]

-- TODO: Replace `dual_span` in Cone/Dual.lean
@[simp] lemma dual_hull' (s : Set M) : dual p (hull R s) = dual p s := dual_hull ..

@[simp low + 1] lemma mem_dual'_singleton {x : M} {y : N} : y ∈ dual p {x} ↔ 0 ≤ p x y := by simp

variable (p) in
/-- Any cone is a subcone of its double dual cone. -/
lemma dual_dual_mono {s t : Set M} (hSC : s ⊆ t) :
    dual p.flip (dual p s) ≤ dual p.flip (dual p t) := by
  exact dual_antitone <| dual_antitone hSC

lemma le_dual_of_le_dual {S : PointedCone R M} {T : PointedCone R N}
    (hSC : T ≤ dual p S) : S ≤ dual p.flip T :=
  le_trans subset_dual_dual (dual_antitone hSC)

-- NOTE: This is the characterizing property of an antitone GaloisConnection.
lemma le_dual_iff_le_dual {S : PointedCone R M} {T : PointedCone R N} :
    S ≤ dual p.flip T ↔ T ≤ dual p S := ⟨le_dual_of_le_dual, le_dual_of_le_dual⟩

-- lemma span_sSup_sInf_span (S : Set (PointedCone R M)) :
--     span R (sSup S : PointedCone R M) = sInf {span R (E:=M) C | C ∈ S} := by
--   sorry

-- lemma dual_sSup' (S : Set (Set M)) :
--     dual p (sSup S) = dual p (⋃ C ∈ S, C) := by
--   rw [← dual_span, span, Submodule.span_sSup, dual_span]

@[simp] lemma dual_submodule_span (s : Set M) :
    dual p (Submodule.span R s) = Submodule.dual p s := by
  ext x; simp

@[simp] lemma submodule_dual_hull (s : Set M) :
    Submodule.dual p (hull R s) = Submodule.dual p s := by
  rw [← Submodule.dual_span]; simp

-- NOT TRUE
example (s : Set M) : Submodule.span R (dual p s : Set N) = Submodule.dual p s := by sorry

lemma dual_sSup (S : Set (PointedCone R M)) :
    dual p (⋃ C ∈ S, C) = dual p (sSup S : PointedCone R M) := by
  rw [← dual_hull, hull, Submodule.span_biUnion]

lemma hull_sSup_coe (S : Set (PointedCone R M)) :
    hull R (sSup S : PointedCone R M) = hull R (sSup (SetLike.coe '' S)) := by
  simp
  sorry

example (S : Set (Set M)) : dual p (sSup S : Set M) = sInf (dual p '' S) := dual_sUnion S

lemma dual_sSup_sInf_dual (S : Set (PointedCone R M)) :
    -- dual p (sSup S : PointedCone R M) = sInf (dual p '' (SetLike.coe '' S)) := by
    dual p (sSup S : PointedCone R M) = sInf ((dual p ∘ SetLike.coe) '' S) := by
  rw [← dual_hull]
  simp only [Submodule.span_coe_eq_restrictScalars, Submodule.restrictScalars_self]
  --rw [Submodule.coe_sInf]
  sorry

example (S : Submodule R M) : ((S : PointedCone R M) : Set M) = (S : Set M)
    := by simp

variable {R : Type*} [CommRing R] [LinearOrder R] [IsOrderedRing R] in
variable {M : Type*} [AddCommGroup M] [Module R M] in
variable {N : Type*} [AddCommGroup N] [Module R N] in
variable {p : M →ₗ[R] N →ₗ[R] R} in
/-- For a dual closed cone, the dual of the lineality space is the submodule span of the dual.
  For the other direction, see `DualClosed.dual_lineal_span_dual`. -/
lemma span_dual_le_dual_lineal {C : PointedCone R M} : span R (dual p C) ≤ .dual p C.lineal := by
  simp only [lineal_eq_sSup, Submodule.dual_sSup_sInf_dual]
  refine sInf_le_sInf ?_
  intro T
  simp only [Set.mem_image, Set.mem_ofPred_eq, exists_exists_and_eq_and]
  intro h
  obtain ⟨S, hSC, hS⟩ := h
  rw [← hS]
  nth_rw 3 [← coe_ofSubmodule]
  rw [SetLike.coe_subset_coe, ← dual_eq_submodule_dual]
  exact dual_le_dual hSC

section Map

open Module

variable {M' N' : Type*}
  [AddCommGroup M'] [Module R M']
  [AddCommGroup N'] [Module R N']

-- TODO: generalize to arbitrary pairings
lemma dual_map (f : M →ₗ[R] M') (s : Set M) :
    comap f.dualMap (dual (Dual.eval R M) s) = dual (Dual.eval R M') (f '' s) := by
  ext; simp

lemma dual_map' (f : M →ₗ[R] M') (C : PointedCone R M) :
    comap f.dualMap (dual (Dual.eval R M) C) = dual (Dual.eval R M') (map f C) := by
  ext; simp

-- TODO: generalize to arbitrary pairings
-- lemma dual_map' (f : M →ₗ[R] M') (hf : Function.Injective f) (s : Set M) :
--     map f.dualMap.inverse (dual (Dual.eval R M) s) = dual (Dual.eval R M') (f '' s) := by
--   ext x; simp

end Map

open Pointwise in
@[simp]
lemma neg_dual {s : Set M} : -(dual p s) = dual p (-s) := by
  ext x -- TODO: make this proof an application of `map_dual`
  simp only [Submodule.mem_neg, mem_dual, _root_.map_neg, Left.nonneg_neg_iff, Set.mem_neg]
  constructor
  · intro hy y hy'
    specialize hy hy'
    simp_all only [LinearMap.map_neg, LinearMap.neg_apply, Left.neg_nonpos_iff]
  · intro hy y hy'
    rw [← _root_.neg_neg y] at hy'
    specialize hy hy'
    simp_all only [_root_.neg_neg, LinearMap.map_neg, LinearMap.neg_apply, Left.nonneg_neg_iff]

variable {M' : Type*} [AddCommGroup M'] [Module R M']

lemma dual_id (s : Set M) : dual p s = dual .id (p '' s) := by simp

lemma dual_id_map (C : PointedCone R M) : dual p C = dual .id (map p C) := by simp

example /- dual_inf -/ (C D : PointedCone R M) :
    dual p (C ⊓ D : PointedCone R M) = dual p (C ∩ D) := rfl
example (C D : PointedCone R M) : dual p (C ⊔ D) = dual p (C ∪ D) := rfl

alias dual_sup_dual_union := dual_sup

-- TODO: simp lemma?
lemma dual_sup_dual_inf_dual (C D : PointedCone R M) :
    dual p (C ⊔ D : PointedCone R M) = dual p C ⊓ dual p D := by rw [dual_sup, dual_union]

-- TODO: Does this even hold in general? Certainly if C and D are CoFG.
-- @[simp] lemma dual_flip_dual_union
example {C D : PointedCone R M} : -- (hC : C.FG) (hC' : D.FG) :
    dual p.flip (dual p (C ∪ D)) = C ⊔ D := by
  sorry

--------------

lemma submodule_dual_le_dual {s : Set M} : Submodule.dual p s ≤ dual p s := by
  sorry --  rw [← submodule_span_dual]; exact Submodule.subset_span



-------------

-- ## Neg

open Pointwise in
lemma dual_neg_neg (s : Set M) : -dual p (-s) = dual p s := by ext x; rw [dual_neg, neg_neg]

-----------

section LinearOrder

variable {R : Type*} [CommRing R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}

lemma dual_span_lineal_dual (s : Set M) :
    (dual p s).lineal = .dual p s := by
  rw [Eq.comm]
  rw [← ofSubmodule_inj]
  rw [← dual_submodule_span]
  rw [← PointedCone.coe_ofSubmodule]
  rw [← hull_union_neg_eq_submodule_span]
  rw [dual_hull]
  rw [dual_union]
  rw [dual_neg, lineal_inf_neg]
  try rw [inf_comm]

-- lemma dual_span_lineal_dual' (C : PointedCone R M) :
--     Submodule.dual p (Submodule.span R (C : Set M)) = (dual p C).lineal := by
--   rw [← ofSubmodule_inj]
--   rw [← dual_eq_submodule_dual]
--   rw [← PointedCone.ofSubmodule_coe]
--   rw [← sup_neg_eq_submodule_span]
--   rw [dual_sup_dual_inf_dual]
--   rw [Submodule.coe_set_neg]
--   rw [← dual_neg, lineal_inf_neg]

end LinearOrder

end PointedCone
