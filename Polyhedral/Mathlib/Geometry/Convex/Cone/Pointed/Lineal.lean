/-
Copyright (c) 2025 Olivia Röhrig, Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Olivia Röhrig, Martin Winter
-/
module

public import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.LinearMap
public import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Restrict

/-! This file proves facts about the lineality space of a cone. -/

@[expose] public section

namespace PointedCone

variable {R M M₁ M₂ N : Type*}

open Module Function LinearMap Pointwise
open Submodule (span)

section LinearOrderedRing

variable [Ring R] [LinearOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M]

variable {C : PointedCone R M}

/-- Every submodule contain in the cone is also contained in the lineality space. -/
lemma submodule_le_lineal {S : Submodule R M} (hS : S ≤ C) :
    S ≤ C.lineal := by simp only [lineal_eq_sSup]; exact le_sSup hS

example (x : M) (hx : x ∈ C.lineal) : -x ∈ C.lineal := neg_mem hx

lemma neg_mem_of_mem_lineal {x : M} (hx : x ∈ C.lineal) : -x ∈ C := by
  rw [← Submodule.neg_mem_iff] at hx
  exact lineal_le C hx

lemma mem_of_neg_mem_lineal {x : M} (hx : -x ∈ C.lineal) : x ∈ C := by
  rw [Submodule.neg_mem_iff] at hx
  exact lineal_le C hx

lemma lineal_inf_neg (C : PointedCone R M) : C.lineal = C ⊓ -C := by
  ext x; simp

lemma lineal_mem_neg (C : PointedCone R M) : C.lineal = {x ∈ C | -x ∈ C} := by
  ext x; simp

@[simp]
lemma lineal_inf (C D : PointedCone R M) : (C ⊓ D).lineal = C.lineal ⊓ D.lineal := by
  ext x; simp [mem_lineal]; aesop

/- TODO: this should be called `ofSubmodule_lineal`, but this name is currently taken by an
incorrectly named mathlib lemma. -/
@[simp] lemma submodule_lineal (S : Submodule R M) :
    (S : PointedCone R M).lineal = S := by
  ext x; simp [mem_lineal]

@[simp] lemma lineal_top : (⊤ : PointedCone R M).lineal = ⊤ := submodule_lineal ⊤

@[simp] lemma lineal_bot : (⊥ : PointedCone R M).lineal = ⊥ := submodule_lineal ⊥

lemma lineal_mono {C D : PointedCone R M} (h : C ≤ D) : C.lineal ≤ D.lineal := by
  intro x hx
  rw [mem_lineal] at *
  exact ⟨h hx.1, h hx.2⟩

lemma lineal_monotone : Monotone fun C : PointedCone R M => C.lineal :=
  fun _ _ => lineal_mono

lemma lineal_le_ker_of_le_nonneg {f : M →ₗ[R] R}
    (h : C ≤ f.nonneg) : C.lineal ≤ f.ker := by
  simpa using lineal_mono h

/- In this section we prove properties of lineal that also follow from lineal
being a face. But we need this earlier than faces, so we need to prove that
lineal is a face here. This can then be resused later.

Alternatively, lineal can be defined alongside faces. It is not clear yet what is best.
-/

lemma mem_lineal_of_add_mem_left {x y : M} (hx : x ∈ C) (hy : y ∈ C)
    (hxy : x + y ∈ C.lineal) : x ∈ C.lineal := by
  have hxy' := neg_mem_of_mem_lineal hxy
  have hx' := C.add_mem hy hxy'
  simp only [neg_add_rev, add_neg_cancel_left] at hx'
  exact mem_lineal.mpr ⟨hx, hx'⟩

lemma mem_lineal_of_add_mem_right {x y : M} (hx : x ∈ C) (hy : y ∈ C)
    (hxy : x + y ∈ C.lineal) : y ∈ C.lineal := by
  rw [add_comm] at hxy; exact mem_lineal_of_add_mem_left hy hx hxy

lemma mem_lineal_of_add_mem {x y : M} (hx : x ∈ C) (hy : y ∈ C)
    (hxy : x + y ∈ C.lineal) : x ∈ C.lineal ∧ y ∈ C.lineal :=
  ⟨mem_lineal_of_add_mem_left hx hy hxy, mem_lineal_of_add_mem_right hx hy hxy⟩

lemma lineal_isExtreme_right_of_inv {x y : M} (hx : x ∈ C) (hy : y ∈ C)
    {c : R} (hc : 0 < c) (hc' : Invertible c) (hxy : x + c • y ∈ C.lineal) : y ∈ C.lineal := by
  have h := mem_lineal_of_add_mem_right hx (C.smul_mem (le_of_lt hc) hy) hxy
  simpa using C.lineal.smul_mem (Invertible.invOf c) h

lemma lineal_isExtreme_left_of_inv {x y : M} (hx : x ∈ C) (hy : y ∈ C)
    {c : R} (hc : 0 < c) (hc' : Invertible c) (hxy : c • x + y ∈ C.lineal) : x ∈ C.lineal := by
  have h := mem_lineal_of_add_mem_left (C.smul_mem (le_of_lt hc) hx) hy hxy
  simpa using C.lineal.smul_mem (Invertible.invOf c) h

lemma subset_lineal_of_sum_mem {s : Finset M} (hs : (s : Set M) ⊆ C)
    (h : ∑ x ∈ s, x ∈ C.lineal) : (s : Set M) ⊆ C.lineal := by classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert _ _ hy H =>
    simp only [Set.subset_def, SetLike.mem_coe, Finset.coe_insert, Set.mem_insert_iff,
      forall_eq_or_imp, Finset.sum_insert hy] at *
    have h := mem_lineal_of_add_mem hs.1 (C.sum_mem hs.2) h
    exact ⟨h.1, H hs.2 h.2⟩

@[simp] lemma sup_lineal_eq (C : PointedCone R M) : C ⊔ C.lineal = C :=
    sup_of_le_left (lineal_le C)

-- NOTE: equality holds, e.g., if D is a face of C
lemma lineal_sup_le (C D : PointedCone R M) : C.lineal ⊔ D.lineal ≤ (C ⊔ D).lineal := by
  intro x
  simp only [Submodule.mem_sup, mem_lineal, forall_exists_index, and_imp]
  intro y hy hy' z hz hz' rfl
  exact ⟨⟨y, hy, by use z⟩, -y, hy', -z, hz', by simp [add_comm]⟩

lemma inf_sup_eq_self_of_le_of_codisjoint {D : PointedCone R M}
    {T : Submodule R M} (hT : T ≤ C) (hST : Codisjoint D T) : (C ⊓ D) ⊔ T = C := by
  simp [inf_sup_assoc_of_le_of_submodule_le _ hT, hST.eq_top]

/-- If `C` is a cone and `S` is codisjoint to the cone's lineality space, then `C` can
be written as `(C ⊓ S) ⊔ C.lineal`.

This result is used to reduce statements to salient cones while staying in the same ambient
space. If `S` is complementary to `C.lineal`, then `C ⊓ S ≃ C ⧸ C.lineal`, and the latter is
the salient quotient of `C` (see `salientQuot`). See also `Salient.inf_disjoint_lineal`.

This is a special case of `inf_sup_eq_self_of_le_of_codisjoint`. -/
lemma inf_sup_lineal {S : Submodule R M} (hCS : Codisjoint C.lineal S) :
    (C ⊓ S) ⊔ C.lineal = C := by
  rw [inf_sup_assoc_of_le_of_submodule_le _ (lineal_le C)]
  rw [← coe_sup, hCS.symm.eq_top]
  simp

/-- Intersecting a cone with a complement of its lineality space commutes with taking its
linear span. -/
lemma span_inf_of_codisjoint_lineal {S : Submodule R M} (hS : Codisjoint C.lineal S) :
    span R (C ⊓ S : PointedCone R M) = span R C ⊓ S := by
  nth_rw 2 [← C.inf_sup_lineal hS]
  rw [← coe_sup_submodule_span, Submodule.span_union, coe_ofSubmodule, Submodule.span_eq C.lineal]
  rw [sup_inf_assoc_of_le C.lineal (Submodule.span_le.mpr fun _ hx ↦ hx.2)]
  rw [Eq.comm, sup_eq_left]
  intro x hx
  apply Submodule.subset_span
  exact ⟨lineal_le C hx.1, hx.2⟩

lemma lineal_le_span (C : PointedCone R M) : C.lineal ≤ span R C := by
  rw [← ofSubmodule_le_ofSubmodule]
  exact le_trans (lineal_le C) Submodule.subset_span

/-- The linear span of `C ⊓ -C` is the lineality space of `C`. -/
lemma span_inf_neg_eq_lineal (C : PointedCone R M) : span R (C ⊓ -C) = C.lineal := by
  simpa [coe_lineal] using (Submodule.span_eq C.lineal)

-- ## MAP

variable [AddCommGroup M₁] [Module R M₁]
variable [AddCommGroup M₂] [Module R M₂]

lemma map_lineal_le (C : PointedCone R M₁) (f : M₁ →ₗ[R] M₂) :
    C.lineal.map f ≤ (C.map f).lineal := by
  intro y
  simp only [Submodule.mem_map, mem_lineal, mem_map, forall_exists_index, and_imp]
  intro x hx hmx hfxy
  exact ⟨⟨x, hx, hfxy⟩, ⟨-x, hmx, by rw [← hfxy, LinearMap.map_neg]⟩⟩

lemma map_lineal (C : PointedCone R M₁) {f : M₁ →ₗ[R] M₂} (hf : Injective f) :
    (C.map f).lineal = C.lineal.map f := by
  refine le_antisymm (fun _ ↦ ?_) (map_lineal_le C f)
  simp only [mem_lineal, mem_map, Submodule.mem_map, and_imp, forall_exists_index]
  refine fun y hy hfxy _ hz hfxz ↦ ⟨y, ⟨hy, ?_⟩, hfxy⟩
  rw [← hfxy, ← LinearMap.map_neg] at hfxz
  simpa [← hf hfxz] using hz

lemma comap_lineal (C : PointedCone R M₂) {f : M₁ →ₗ[R] M₂} :
    (C.comap f).lineal = C.lineal.comap f := by
  ext x; simp [mem_lineal]

@[simp] lemma neg_lineal (C : PointedCone R M) : (-C).lineal = C.lineal := by
  simp [← comap_id_eq_neg, comap_lineal]

lemma lineal_restrict (S : Submodule R M) (C : PointedCone R M) :
    (restrict S C).lineal = .restrict S C.lineal := by
  simp only [Submodule.submoduleOf, ← comap_lineal, comap]
  congr

lemma lineal_embed (S : Submodule R M) (C : PointedCone R S) :
    (embed C).lineal = .embed C.lineal := by
  apply map_lineal
  exact Submodule.injective_subtype S

variable [IsNoetherianRing R] in
/-- The lineality space of an FG cone is FG. -/
lemma lineal_fg (hC : C.FG) : C.lineal.FG :=
  Submodule.FG.of_le hC.span <| lineal_le_span C

end LinearOrderedRing

section DivisionRing

variable [DivisionRing R] [LinearOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M]

variable {C : PointedCone R M}

lemma lineal_isExtreme_left' {x y : M} (hx : x ∈ C) (hy : y ∈ C)
    {c : R} (hc : 0 < c) (hxy : c • x + y ∈ C.lineal) : x ∈ C.lineal := by
  exact lineal_isExtreme_left_of_inv hx hy hc (invertibleOfNonzero <| ne_of_gt hc) hxy

lemma lineal_isExtreme_right' {x y : M} (hx : x ∈ C) (hy : y ∈ C)
    {c : R} (hc : 0 < c) (hxy : x + c • y ∈ C.lineal) : y ∈ C.lineal := by
  exact lineal_isExtreme_right_of_inv hx hy hc (invertibleOfNonzero <| ne_of_gt hc) hxy

lemma subset_lineal_of_sum_mem' {s : Finset M} (hs : (s : Set M) ⊆ C)
    (c : M → R) (hc : ∀ x ∈ s, 0 < c x) (h : ∑ x ∈ s, c x • x ∈ C.lineal) :
    ∀ x ∈ s, c x ≠ 0 → x ∈ C.lineal := by classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert y s hy H =>
    simp only [Set.subset_def, SetLike.mem_coe, ne_eq, Finset.coe_insert,
      Set.mem_insert_iff, forall_eq_or_imp, Finset.mem_insert, Finset.sum_insert hy] at *
    have hsC := C.sum_mem (fun x hx ↦ C.smul_mem (le_of_lt <| hc.2 x hx) (hs.2 x hx))
    constructor
    · exact fun _ ↦ lineal_isExtreme_left' hs.1 hsC hc.1 h
    · exact H hs.2 hc.2 <| mem_lineal_of_add_mem_right (C.smul_mem (le_of_lt hc.1) hs.1) hsC h

/- Note: an equivalent theorem for faces exists, and can be used once we decide to define lineality
*after* the face theory is established. -/
variable (R) in
lemma hull_inter_lineal_eq_lineal (s : Set M) :
    hull R (s ∩ (hull R s).lineal) = (hull R s).lineal := by
  apply le_antisymm
  · exact Submodule.span_le.mpr fun _ hx ↦ hx.2
  · intro x hx
    obtain ⟨c, hc, hc₀, hcx⟩ := mem_hull_set.mp hx.1
    rw [mem_hull_set]
    refine ⟨c, fun _ hy ↦ ⟨hc hy, ?_⟩, hc₀, hcx⟩
    apply subset_lineal_of_sum_mem' (fun z hz ↦ subset_hull (hc hz)) c
    · intro z hz
      exact lt_of_le_of_ne (hc₀ z) (Ne.symm (Finsupp.mem_support_iff.mp hz))
    · have hsum : c.sum (fun m r ↦ r • m) ∈ (hull R s).lineal := hcx ▸ hx
      simpa only [Finsupp.sum] using hsum
    · exact hy
    · exact Finsupp.mem_support_iff.mp hy

end DivisionRing

-- # SALIENT

section Semiring

variable [Semiring R] [PartialOrder R] [IsOrderedRing R]
variable [AddCommMonoid M] [Module R M]

variable {C : PointedCone R M}

/-- A cone is salient if no two of its non-zero points add up to zero. If the module has negation,
then equivalently the cone does not contain both a non-zero point and its negative.
Over a linearly ordered ring, this is equivalent to the lineality space being ⊥.
This property is also called being *pointed*. -/
def Salient (C : PointedCone R M) := ∀ x ∈ C, ∀ y ∈ C, x + y = 0 → x = 0

lemma salient_iff_forall_mem_eq_zero_of_add_zero :
    C.Salient ↔ ∀ x ∈ C, ∀ y ∈ C, x + y = 0 → x = 0 := .rfl

@[simp] protected lemma Salient.bot : (⊥ : PointedCone R M).Salient := by simp [Salient]

lemma Salient.of_le_salient {C D : PointedCone R M} (hC : C.Salient) (hD : D ≤ C) : D.Salient :=
  fun _ hx _ hy ↦ hC _ (hD hx) _ (hD hy)

end Semiring

section IsStrictOrderedRing

variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [AddCommMonoid M] [Module R M]

variable {C : PointedCone R M}

lemma _root_.LinearMap.positive_salient (f : M →ₗ[R] R) : f.positive.Salient := by
  intro x hx y hy hxy
  by_contra hx'
  have h' := add_pos (hx hx') <| hy <| (eq_zero_iff_eq_zero_of_add_eq_zero hxy).not.mp hx'
  have h := congrArg f hxy
  simp at h
  simp [h] at h'

lemma Salient.of_le_positive {f : M →ₗ[R] R} (h : C ≤ f.positive) :
    C.Salient := of_le_salient f.positive_salient h

end IsStrictOrderedRing

section AddCommGroup

variable [Semiring R] [PartialOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M]

variable {C : PointedCone R M}

lemma salient_iff_forall_mem_eq_zero_of_neg_mem : C.Salient ↔ ∀ x ∈ C, -x ∈ C → x = 0 where
  mp h x hx hnx := h x hx (-x) hnx (add_neg_cancel _)
  mpr h x hx y hy hxy := by
    rw [add_comm, add_eq_zero_iff_eq_neg] at hxy
    rw [hxy] at hy
    exact h x hx hy

-- NOTE: this is a compatibility lemma, it will be removed eventually
lemma salient_iff_convexCone_salient : C.Salient ↔ (C : ConvexCone R M).Salient := by
  unfold ConvexCone.Salient
  conv => rhs; intro _ _; rw [not_imp_not]
  exact salient_iff_forall_mem_eq_zero_of_neg_mem

end AddCommGroup

section Ring

variable [Ring R] [PartialOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M]

-- NOTE: an easier proof via `salient_of_pos_linearMap` seems only possible if `R` is a field.
lemma Salient.of_hull_linearIndepOn {s : Set M} (h : LinearIndepOn R id s) :
    (hull R s).Salient := by classical
  -- next line needs fixing once ConvexCone is removed
  simp only [salient_iff_convexCone_salient, ConvexCone.Salient, mem_toConvexCone, ne_eq]
  intro x hxp hx0 hxn
  absurd hx0
  rw [Submodule.mem_span_iff_exists_finset_subset] at hxp hxn
  obtain ⟨fp, tp, htsp, hftp, rfl⟩ := hxp
  obtain ⟨fn, tn, htsn, hftn, hsum⟩ := hxn
  let t := tp ∪ tn
  let f := fun x ↦ fp x + fn x
  refine Finset.sum_eq_zero (fun x hx ↦ ?_)
  have hlin := linearIndepOn_iff'.mp h t (f ·) (by simp [t, htsp, htsn])
  simp only [id_eq, Nonneg.coe_smul] at hlin
  specialize hlin ?_ x (Finset.subset_union_left hx)
  · simp only [f, add_smul, Finset.sum_add_distrib]
    have hsum1 : ∑ x ∈ t, fp x • x = ∑ x ∈ tp, fp x • x := by -- restrict t to tp
      refine Finset.sum_union_eq_left fun _ _ h ↦ ?_
      simp [fp.notMem_support.mp fun h2 ↦ h <| hftp h2]
    have hsum2 : ∑ x ∈ t, fn x • x = ∑ x ∈ tn, fn x • x := by -- restrict t to tn
      refine Finset.sum_union_eq_right fun _ _ h ↦ ?_
      simp [fn.notMem_support.mp fun h2 ↦ h <| hftn h2]
    rw [hsum1, hsum2, hsum, add_neg_cancel]
  rw [Nonneg.coe_eq_zero, add_eq_zero_iff_of_nonneg zero_le zero_le] at hlin
  simp only [hlin, zero_smul]

section IsDomain

variable [IsDomain R] [IsTorsionFree R M]

lemma Salient.of_hull_singleton (x : M) : (R ∙₊ x).Salient := by
  by_cases h : x = 0
  · simp [h]
  · exact of_hull_linearIndepOn (by simp [h])

/- NOTE: there is also `ofSubmodule_salient_iff_eq_bot` below, which proven something stronger
for general rings, BUT assumes linear order. Is one setting better than the other? -/
/-- The full space is not salient unless its rank is zero. -/
lemma Salient.not_top (h : Module.rank R M ≠ 0) : ¬(⊤ : PointedCone R M).Salient := by
  simpa [salient_iff_convexCone_salient, ConvexCone.Salient, rank_zero_iff_forall_zero] using h

end IsDomain

end Ring

section LinearOrder

variable [Ring R] [LinearOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M]

variable {C : PointedCone R M}

/-- A cone is salient if and only if its lineality space is a point. -/
lemma salient_iff_lineal_bot : C.Salient ↔ C.lineal = ⊥ := by
  rw [salient_iff_forall_mem_eq_zero_of_neg_mem]
  constructor <;> intro h
  · ext x
    simp only [mem_lineal, Submodule.mem_bot]
    exact ⟨fun H ↦ h x H.1 H.2, by simp +contextual⟩
  · intro x hx hnx
    have hlin := mem_lineal.mpr ⟨hx, hnx⟩
    rw [h] at hlin
    exact hlin

/-- A submodule is salient if and only if it is a point. -/
@[simp] lemma salient_ofSubmodule_iff_eq_bot {S : Submodule R M} :
    (S : PointedCone R M).Salient ↔ S = ⊥ := by
  nth_rw 2 [← submodule_lineal S]
  exact salient_iff_lineal_bot

/-- If `S` is a submodule disjoint from the lineality space of a cone `C`, then `C ⊓ S` is
salient. -/
lemma Salient.inf_disjoint_lineal {S : Submodule R M} (hCS : Disjoint C.lineal S) :
    (C ⊓ S).Salient := by
  simp only [salient_iff_lineal_bot, lineal_inf, submodule_lineal, ← disjoint_iff, hCS]

end LinearOrder

section Ring_LinearOrder

-- # MAP

section Map

variable [Ring R] [LinearOrder R] [IsOrderedRing R]
variable [AddCommGroup M₁] [Module R M₁]
variable [AddCommGroup M₂] [Module R M₂]

variable {C : PointedCone R M₁}

lemma salient_map {f : M₁ →ₗ[R] M₂} (hC : C.Salient) (hf : Injective f) :
    (C.map f).Salient := by
  rw [salient_iff_lineal_bot] at *
  simp [map_lineal _ hf, hC]

lemma salient_comap {f : M₂ →ₗ[R] M₁} (hC : C.Salient) (hf : Injective f) :
    (C.comap f).Salient := by
  rw [salient_iff_lineal_bot] at *
  simpa [comap_lineal, hC] using LinearMap.ker_eq_bot_of_injective hf

lemma salient_map_iff (C : PointedCone R M₁) {f : M₁ →ₗ[R] M₂} (hf : Injective f) :
    (C.map f).Salient ↔ C.Salient where
  mpr h := salient_map h hf
  mp h := by
    have h := salient_comap h hf
    unfold comap map at h
    rwa [Submodule.comap_map_eq_of_injective] at h
    exact hf

lemma salient_neg (hC : C.Salient) : (-C).Salient := by
  simpa [← map_id_eq_neg] using salient_map hC (injective_neg_iff.mpr injective_id)

end Map

-- # SALIENT QUOT

variable [Ring R] [LinearOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M]

variable {C : PointedCone R M}

/- NOTE: we may rename this to `salience` as in "the salience of the cone" or
"the salient part of the cone". -/
/- NOTE: if we introduce faces early, we may denote this simply by `C ⧸ ⊥` as we already do
in the files that introduce quotients by faces. -/
/-- The quotient of a cone by its lineality space.

This notion is important for reducing statements about cones to their salient parts. If `S` is
a submodule complementary to `C.lineal`, then `salientQuot ≃ C ⊓ S`.
-/
abbrev salientQuot (C : PointedCone R M) := C.quot C.lineal

lemma salientQuot_eq_quot_lineal (C : PointedCone R M) : C.salientQuot = C.quot C.lineal := rfl

lemma salientQuot_salient (C : PointedCone R M) : Salient C.salientQuot := by
  rw [salient_iff_lineal_bot]
  refine le_antisymm ?_ bot_le
  rintro x ⟨hx, hnx⟩
  obtain ⟨y, hy, rfl⟩ := PointedCone.mem_map.mp hx
  obtain ⟨z, hz, hzq⟩ := PointedCone.mem_map.mp hnx
  rw [Submodule.mem_bot]
  have hyz : y + z ∈ C.lineal := by
    rw [← Submodule.ker_mkQ C.lineal, LinearMap.mem_ker]
    rw [map_add, hzq]
    simp
  have hylineal := mem_lineal_of_add_mem_left hy hz hyz
  simpa [Submodule.mkQ_apply] using
    (Submodule.Quotient.mk_eq_zero C.lineal).mpr hylineal

@[simp] lemma salientQuot_submodule_eq_bot (S : Submodule R M) :
    (S : PointedCone R M).salientQuot = ⊥ := by
  unfold salientQuot
  rw [submodule_lineal, ← Submodule.span_eq S]
  simp only [Submodule.span_coe_eq_restrictScalars, Submodule.restrictScalars_self]
  rw [← coe_ofSubmodule, quot_span]

@[simp] lemma salientQuot_bot : (⊥ : PointedCone R M).salientQuot = ⊥ :=
  salientQuot_submodule_eq_bot ⊥

@[simp] lemma salientQuot_top : (⊤ : PointedCone R M).salientQuot = ⊥ :=
  salientQuot_submodule_eq_bot ⊤

lemma lineal_eq_of_quot_salient {S : Submodule R M} (hS : S ≤ C)
    (h : (C.quot S).Salient) : S = C.lineal := by
  refine le_antisymm (submodule_le_lineal hS) fun x hx ↦ ?_
  have hxq := PointedCone.map_lineal_le C S.mkQ ⟨x, hx, rfl⟩
  rw [salient_iff_lineal_bot.mp h] at hxq
  exact (Submodule.Quotient.mk_eq_zero S).mp hxq

end Ring_LinearOrder

section NoZeroSMulDivisors

variable [Ring R] [LinearOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup M₁] [Module R M₁]
variable [AddCommGroup M₂] [Module R M₂] [NoZeroSMulDivisors R M₂]

/- NOTE: All proofs in this section are AI generated and rather messy. Maybe there is a better
way, or maybe there results are not needed eventually.

These results are mainly used in Polyhedral/Basic.lean (e.g. `exists_fg_salient_submoduel_eq_sup`).
-/

lemma salient_hull_surjInv {s : Set M₂} (h₀ : 0 ∉ s) {f : M₁ →ₗ[R] M₂}
    (hs : (hull R s).Salient) (hf : Surjective f) : (hull R (surjInv hf '' s)).Salient := by
  classical
  intro x hx y hy hxy
  have hmap : (hull R (surjInv hf '' s)).map f = hull R s := by
    simp [map_hull, Set.image_image, surjInv_eq]
  have hfxmem : f x ∈ hull R s := by
    rw [← hmap]
    exact PointedCone.mem_map.mpr ⟨x, hx, rfl⟩
  have hfymem : f y ∈ hull R s := by
    rw [← hmap]
    exact PointedCone.mem_map.mpr ⟨y, hy, rfl⟩
  have hfx : f x = 0 :=
    hs (f x) hfxmem (f y) hfymem (by simpa using congrArg f hxy)
  obtain ⟨c, hc, hc₀, hcx⟩ := mem_hull_set.mp hx
  let g : M₁ → R → M₂ := fun m a ↦ a • f m
  have hsum : c.sum g = 0 := by
    calc
      c.sum g = f (c.sum fun m a ↦ a • m) := by
        simp only [Finsupp.sum]
        rw [map_sum]
        exact Finset.sum_congr rfl fun m _ ↦ by simp [g]
      _ = f x := congrArg f hcx
      _ = 0 := hfx
  have hterm : ∀ m ∈ c.support, g m (c m) = 0 := by
    intro m hm
    have hmem : ∀ n ∈ c.support, g n (c n) ∈ hull R s := by
      intro n hn
      obtain ⟨w, hw, hnw⟩ := hc hn
      have hfn : f n = w := (congrArg f hnw.symm).trans (surjInv_eq hf w)
      change c n • f n ∈ hull R s
      rw [hfn]
      exact (hull R s).smul_mem (hc₀ _) (subset_hull hw)
    have hrest : c.sum g - g m (c m) ∈ hull R s := by
      rw [Finsupp.sum, ← Finset.sum_erase_add _ _ hm, add_sub_cancel_right]
      exact Submodule.sum_mem _ fun n hn ↦ hmem n (Finset.mem_of_mem_erase hn)
    apply hs _ (hmem m hm) _ hrest
    rw [← add_sub_assoc, hsum]
    abel
  have hc_eq_zero : c = 0 := by
    ext m
    by_cases hm : m ∈ c.support
    · obtain ⟨w, hw, hmw⟩ := hc hm
      have hfw : f m = w := (congrArg f hmw.symm).trans (surjInv_eq hf w)
      have hfm : f m ≠ 0 := hfw.symm ▸ fun hw₀ ↦ h₀ (hw₀ ▸ hw)
      exact (eq_zero_or_eq_zero_of_smul_eq_zero (hterm m hm)).resolve_right hfm
    · simpa [Finsupp.mem_support_iff] using hm
  rw [← hcx, hc_eq_zero]
  simp

lemma exists_salient_eq_map {C : PointedCone R M₂} {f : M →ₗ[R] M₂} (hC : C.Salient)
    (hf : Surjective f) : ∃ D : PointedCone R M, D.Salient ∧ C = D.map f := by
  let s : Set M₂ := C \ {0}
  have hs : hull R s = C := by
    apply le_antisymm
    · exact Submodule.span_le.mpr fun _ hx ↦ hx.1
    · intro x hx
      by_cases hx₀ : x = 0
      · simp [hx₀]
      · exact subset_hull ⟨hx, hx₀⟩
  use hull R (surjInv hf '' s)
  constructor
  · exact salient_hull_surjInv (by simp [s]) (hs ▸ hC) hf
  · simp [map_hull, Set.image_image, surjInv_eq, hs]

lemma exists_salient_eq_sup_lineal (C : PointedCone R M) [NoZeroSMulDivisors R (M ⧸ C.lineal)] :
    ∃ D : PointedCone R M, D.Salient ∧ C = D ⊔ C.lineal := by
  obtain ⟨D, hD, hCD⟩ := exists_salient_eq_map (C := C.salientQuot)
    (f := C.lineal.mkQ) (salientQuot_salient C) (Submodule.mkQ_surjective C.lineal)
  refine ⟨D, hD, ?_⟩
  exact (sup_eq_left.mpr (lineal_le C)).symm.trans (quot_eq_iff_sup_eq.mp hCD)

end NoZeroSMulDivisors

section DivisionRing

variable [DivisionRing R] [LinearOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M]

-- NOTE: This proof is AI generated and should be cleaned up.
/-- `s \ (hull R s.lineal)` spans a salient cone. -/
lemma Salient.hull_sdiff_hull_lineal {s : Set M} :
    Salient (hull R (s \ (hull R s).lineal)) := by
  rw [salient_iff_forall_mem_eq_zero_of_neg_mem]
  intro x hx hnx
  -- Since the smaller hull is contained in `hull R s`,
  -- `x` and `-x` both lie in `hull R s`, hence `x` is lineal there.
  have hxlin : x ∈ (hull R s).lineal := by
    rw [mem_lineal]
    exact ⟨hull_mono Set.sdiff_subset hx, hull_mono Set.sdiff_subset hnx⟩
  -- Write `x` as a nonnegative conic combination of generators outside
  -- the lineality space.
  obtain ⟨c, hc, hc₀, hcx⟩ := mem_hull_set.mp hx
  have hsC : (c.support : Set M) ⊆ hull R s := by
    intro y hy
    exact subset_hull (hc hy).1
  -- Coefficients on the support are nonzero, hence strictly positive.
  have hcpos : ∀ y ∈ c.support, 0 < c y := by
    intro y hy
    exact lt_of_le_of_ne
      (hc₀ y)
      (Ne.symm (Finsupp.mem_support_iff.mp hy))
  have hsum' :
      c.sum (fun y r ↦ r • y) ∈ (hull R s).lineal := by
    rw [hcx]
    exact hxlin
  have hsum : (∑ y ∈ c.support, c y • y) ∈ (hull R s).lineal := by
    simpa only [Finsupp.sum] using hsum'
  -- Every support generator must therefore lie in the lineality space.
  have hlin := subset_lineal_of_sum_mem'
    (C := hull R s) hsC (c : M → R) hcpos hsum
  -- But every support generator was chosen from `s \ lineal`.
  -- Hence the support must be empty.
  have hsupp : c.support = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro y hy
    exact (hc hy).2 (hlin y hy (Finsupp.mem_support_iff.mp hy))
  -- Thus the conic combination is empty, so `x = 0`.
  rw [← hcx]
  simp [Finsupp.sum, hsupp]

end DivisionRing

end PointedCone
