/-
Copyright (c) 2025 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/
module

public import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Basic
public import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Lineal
public import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Rank

import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.Geometry.Convex.Cone.Dual

/-! This file proves results about `PointedCone.dual` intended to go into Pointed/Dual.lean. -/

public section

namespace PointedCone

variable {R M M₁ M₂ N : Type*}

open Module LinearMap
open Submodule (span)

section CommRing

variable [CommRing R] [PartialOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]

variable {p : M →ₗ[R] N →ₗ[R] R}

-- TODO: `PointedCone.map` should be an abbrev

lemma dual_top_iff_le_ker {C : PointedCone R M} : dual p C = ⊤ ↔ C ≤ ker p := by
  constructor
  · intro h x hx
    simp only [Submodule.restrictScalars_mem, mem_ker, LinearMap.ext_iff]
    intro y
    have hpos : 0 ≤ p x y := by
      have : y ∈ dual p C := by rw [h]; simp
      exact this hx
    have hneg : 0 ≤ p x (-y) := by
      have : -y ∈ dual p C := by rw [h]; simp
      exact this hx
    exact le_antisymm (by simpa using hneg) hpos
  · intro h
    ext y
    refine ⟨by simp, fun _ _ hx => ?_⟩
    rw [h hx]
    simp

lemma dual_univ_ker : dual p .univ = ker p.flip := by
  ext x
  simp_rw [mem_dual, Set.mem_univ, forall_const, Submodule.restrictScalars_mem,
    mem_ker, LinearMap.ext_iff, flip_apply, zero_apply]
  constructor <;> intro h y
  · exact le_antisymm (by simpa using @h (-y)) (@h y)
  · rw [h y]

lemma dual_flip_univ_ker : dual p.flip .univ = ker p := by
  nth_rw 2 [← flip_flip p]; exact dual_univ_ker

-- NOTE: this is maybe a better version of of `dual.univ`.
variable [Fact p.SeparatingRight] in
@[simp] lemma dual_univ' : dual p .univ = ⊥ := by simp [dual_univ_ker]

alias dual_top := dual_univ'

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

variable (p) in
lemma dual_dual_mono {s t : Set M} (hSC : s ⊆ t) :
    dual p.flip (dual p s) ≤ dual p.flip (dual p t) :=
  dual_antitone <| dual_antitone hSC

variable (p) in
/-- Taking the double dual is monotone. -/
lemma dual_dual_monotone : Monotone fun s : Set M => dual p.flip (dual p s) :=
  fun _ _ => dual_dual_mono p

lemma le_dual_of_le_dual {S : PointedCone R M} {T : PointedCone R N}
    (hSC : T ≤ dual p S) : S ≤ dual p.flip T :=
  le_trans subset_dual_dual (dual_antitone hSC)

-- NOTE: This is the characterizing property of an antitone GaloisConnection.
lemma le_dual_iff_le_dual {S : PointedCone R M} {T : PointedCone R N} :
    S ≤ dual p.flip T ↔ T ≤ dual p S := ⟨le_dual_of_le_dual, le_dual_of_le_dual⟩

@[simp] lemma dual_submodule_span (s : Set M) :
    dual p (Submodule.span R s) = Submodule.dual p s := by
  ext x; simp

@[simp] lemma submodule_dual_hull (s : Set M) :
    Submodule.dual p (hull R s) = Submodule.dual p s := by
  rw [← Submodule.dual_span]; simp

lemma dual_sSup (S : Set (PointedCone R M)) :
    dual p (⋃ C ∈ S, C) = dual p (sSup S : PointedCone R M) := by
  rw [← dual_hull, hull, Submodule.span_biUnion]

lemma dual_sSup_sInf_dual (S : Set (PointedCone R M)) :
    dual p (sSup S : PointedCone R M) = sInf ((dual p ∘ SetLike.coe) '' S) := by
  rw [← dual_sSup (p := p) S]
  simpa [Function.comp_def, Set.image_image] using dual_sUnion (p := p) (SetLike.coe '' S)

lemma dual_sup_dual_le_dual_inf (C D : PointedCone R M) :
    dual p C ⊔ dual p D ≤ dual p (C ⊓ D) :=
  sup_le (dual_le_dual inf_le_left) (dual_le_dual inf_le_right)

lemma dual_id (s : Set M) : dual p s = dual .id (p '' s) := by simp

lemma dual_id_map (C : PointedCone R M) : dual p C = dual .id (map p C) := by simp

alias dual_sup_dual_union := dual_sup

lemma dual_sup_dual_inf_dual (C D : PointedCone R M) :
    dual p (C ⊔ D : PointedCone R M) = dual p C ⊓ dual p D := by rw [dual_sup, dual_union]

lemma submodule_dual_le_dual {s : Set M} :
    Submodule.dual p s ≤ dual p s := fun _ hy _ hx => by rw [← hy hx]

section Neg

open Pointwise

@[simp] lemma neg_dual {s : Set M} : -(dual p s) = dual p (-s) := by
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

lemma dual_neg_neg (s : Set M) : -dual p (-s) = dual p s := by ext x; rw [dual_neg, neg_neg]

end Neg

section Map

variable [AddCommGroup M₁] [Module R M₁]
variable [AddCommGroup M₂] [Module R M₂]

-- TODO: generalize to arbitrary pairings
lemma dual_map (f : M₁ →ₗ[R] M₂) (s : Set M₁) :
    comap f.dualMap (dual (Dual.eval R M₁) s) = dual (Dual.eval R M₂) (f '' s) := by
  ext; simp

lemma dual_map' (f : M₁ →ₗ[R] M₂) (C : PointedCone R M₁) :
    comap f.dualMap (dual (Dual.eval R M₁) C) = dual (Dual.eval R M₂) (map f C) := by
  ext; simp

end Map

end CommRing

section LinearOrder

variable [CommRing R] [LinearOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]

variable {p : M →ₗ[R] N →ₗ[R] R}

/-- The span of the dual cone is contained in the dual of the lineality space.

Equality does not hold in general, not even over fields, for dual closed cones or separating
pairing. Instead, it holds `(C.lineal)** = (span C*)**`, so an additional dual closure after
the span is necessary.
-/
lemma span_dual_le_dual_lineal {C : PointedCone R M} :
    span R (dual p C) ≤ .dual p C.lineal := by
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

lemma dual_lineal_eq_submodule_dual (s : Set M) :
    (dual p s).lineal = .dual p s := by
  rw [Eq.comm]
  rw [← ofSubmodule_inj]
  rw [← dual_submodule_span]
  rw [← PointedCone.coe_ofSubmodule]
  rw [span_eq_hull_neg_sup_hull]
  rw [← hull_union]
  rw [dual_hull]
  rw [dual_union]
  rw [dual_neg, lineal_inf_neg]
  rw [inf_comm]

lemma submodule_dual_span_eq_dual_lineal (C : PointedCone R M) :
    Submodule.dual p (Submodule.span R (C : Set M)) = (dual p C).lineal := by
  rw [Submodule.dual_span, ← dual_lineal_eq_submodule_dual]

end LinearOrder

section Field

variable {R : Type*} [Field R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]

variable {C : PointedCone R M}
variable {p : M →ₗ[R] N →ₗ[R] R}
/-
NOTE: The proof of `FinSalRank.dual_finSalRank` is AI generated and very messy. There is
a cleaner approach:
* prove that salRank is the rank of the quotient module span / lineal
* prove that if A / B is FG, then B* / A* is also FG, where A and B are submodules (with the
  correct inclusion relation) and * is submodule dual. -/
variable (p) in
/-- The dual of a cone with finite salient rank also has finite salient rank. -/
lemma FinSalRank.dual_finSalRank (hC : C.FinSalRank) : (dual p C).FinSalRank := by
  classical
  let T := span R (dual p C : Set N)
  let L := (dual p C).lineal
  obtain ⟨D, hDT, hDL, hsup⟩ := Submodule.exists_le_disjoint_sup_self T L
  have hLT : L ≤ T := lineal_le_span (dual p C)
  have hDLT : D ⊔ L = T := by simpa [sup_eq_left.mpr hLT] using hsup
  let Q := span R (C.salientQuot : Set (M ⧸ C.lineal))
  have hDdual : D ≤ Submodule.dual p C.lineal :=
    hDT.trans span_dual_le_dual_lineal
  let f : D →ₗ[R] Dual R Q :=
    Q.subtype.dualMap.comp
      ((Submodule.dual_linearMap_dual_quot (p := p) C.lineal).comp
        (Submodule.inclusion hDdual))
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot]
    ext y
    simp only [Submodule.mem_bot, LinearMap.mem_ker]
    constructor
    · intro hy
      apply Subtype.ext
      have hyL : (y : N) ∈ L := by
        change (y : N) ∈ (dual p C).lineal
        rw [← submodule_dual_span_eq_dual_lineal]
        rw [Submodule.dual_span, Submodule.mem_dual]
        intro x hx
        have hqx : C.lineal.mkQ x ∈ Q := Submodule.subset_span ⟨x, hx, rfl⟩
        have he := LinearMap.congr_fun hy ⟨C.lineal.mkQ x, hqx⟩
        change p x y = 0 at he
        exact he.symm
      exact (hDL.le_bot ⟨y.2, hyL⟩)
    · rintro rfl
      simp
  have hQ : Q.FG := hC
  have hD : D.FG := by
    let _ : Module.Finite R (Dual R Q) :=
      (Module.finite_dual_iff R).2 (Module.Finite.iff_fg.2 hQ)
    exact Module.Finite.iff_fg.1 (Module.Finite.of_injective f hf)
  change (span R ((dual p C).quot L : Set (N ⧸ L))).FG
  rw [span_quot]
  change (Submodule.map L.mkQ T).FG
  rw [← hDLT, Submodule.map_sup]
  simpa using hD.map L.mkQ

end Field

end PointedCone
