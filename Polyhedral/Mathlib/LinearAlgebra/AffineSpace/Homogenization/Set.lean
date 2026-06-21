/-
Copyright (c) 2026 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/

import Polyhedral.Mathlib.Data.Set.Lattice.Image
import Polyhedral.Mathlib.Algebra.Order.Nonneg.Ring
import Polyhedral.Mathlib.Algebra.Order.Nonneg.DivisionRing

import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.SubMulActionWithZero

import Polyhedral.Mathlib.LinearAlgebra.AffineSpace.Homogenization.Basic

/-! This file defines homogenization of general sets. The homogenization is of type
`SubMulActionWithZero R≥0 W`, which is closed under multiplication and always contains zero.
In particular, the homogenization is never empty. This enables to prove suitable order
isomorphisms. -/

namespace Affine

open Function SubMulActionWithZero IsHomogenization

variable {R V A W : Type*}

local notation3 "R≥0" => {c : R // 0 ≤ c}

section Ring

variable [Ring R] [PartialOrder R] [IsOrderedRing R]
variable [AddCommGroup V] [Module R V]
variable [AddTorsor V A]
variable [AddCommGroup W] [Module R W]

variable [hom : IsHomogenization R A W]

variable {x : A} {s : Set A}

variable (R W) in
def homogenize (s : Set A) : SubMulActionWithZero R≥0 W := R≥0 ∙ (hom.ofPoint '' s)

-- potential notations for homogenization: `R≥0 ∙[W] s` or `R ∙₊[W] s`
--
-- /- Note that the character `∙` U+2219 used below is different from the scalar multiplication
-- character `•` U+2022. -/
-- /-- Notation for the homogenizationof a set `s`, short for `homogenize R W s`. -/
-- scoped notation:70 R:70 " ∙[" W "] " s:70 => homogenize R W s

lemma mem_homogenize {s : Set A} {x : W} :
    x ∈ homogenize R W s ↔ x = 0 ∨ ∃ y ∈ s, ∃ r : R, 0 ≤ r ∧ x = r • hom.ofPoint y := by
  simp [homogenize, mem_smulSet]

lemma mem_homogenize_iff_exist_lt_zero {s : Set A} {x : W} (hx : x ∈ homogenize R W s) :
    x = 0 ∨ ∃ y ∈ s, ∃ r : R, 0 < r ∧ x = r • hom.ofPoint y := by
  obtain (rfl | ⟨y, ⟨z, hz, rfl⟩, _, ⟨r, _⟩, hr0, rfl⟩) := mem_smulSet_iff_exists_ne_zero hx
  · exact .inl rfl
  · exact .inr ⟨z, hz, r, by rwa [← zero_lt_iff] at hr0, rfl⟩

lemma mem_homogenize_iff_ne_zero {s : Set A} {x : W} (hx : x ≠ 0) :
    x ∈ homogenize R W s ↔ ∃ y ∈ s, ∃ r : R, 0 ≤ r ∧ x = r • hom.ofPoint y := by
  simp [homogenize, mem_smulSet_of_ne_zero hx]

lemma mem_homogenize_iff_nonempty {s : Set A} {x : W} (hs : s.Nonempty) :
    x ∈ homogenize R W s ↔ ∃ y ∈ s, ∃ r : R, 0 ≤ r ∧ x = r • hom.ofPoint y := by
  have : (hom.ofPoint '' s).Nonempty := Set.image_nonempty.mpr hs
  simp [homogenize, mem_smulSet_of_nonempty this]

@[simp] lemma homogenize_empty : homogenize R W (∅ : Set A) = ⊥ := by
  ext x; simp [homogenize]

lemma ofPoint_image_subset_homogenize : hom.ofPoint '' s ⊆ homogenize R W s :=
  subset_smulSet

lemma ofPoint_mem_homogenize (hx : x ∈ s) : hom.ofPoint x ∈ homogenize R W s :=
  ofPoint_image_subset_homogenize ⟨x, hx, rfl⟩

lemma smul_ofPoint_mem_homogenize {r : R} (hr : 0 ≤ r) (h : x ∈ s) :
    r • hom.ofPoint x ∈ homogenize R W s :=
  smul_mem _ ⟨r, hr⟩ (ofPoint_mem_homogenize h)

lemma homogenize_mono {s t : Set A} (h : s ⊆ t) : homogenize R W s ≤ homogenize R W t :=
  smulSet_mono <| Set.image_mono h

lemma homogenize_monotone : Monotone (homogenize R W : Set A → SubMulActionWithZero R≥0 W) :=
  fun _ _ => homogenize_mono

/-- Homogenization from sets to `SubMulActionWithZero` as an order homomorphism. -/
def homogenizeOrderHom : Set A →o SubMulActionWithZero R≥0 W where
  toFun := homogenize R W
  monotone' := homogenize_monotone

lemma homogenize_union (s t : Set A) :
    homogenize R W (s ∪ t) = homogenize R W s ⊔ homogenize R W t := by
  simp only [homogenize, Set.image_union, smulSet_union]

lemma homogenize_inter_le (s t : Set A) :
    homogenize R W (s ∩ t) ≤ homogenize R W s ⊓ homogenize R W t := by
  unfold homogenize
  rw [Set.image_inter hom.ofPoint_injective]
  exact smulSet_inter_le _ _

lemma homogenize_sSup (S : Set (Set A)) :
    homogenize R W (sSup S) = sSup (homogenize R W '' S) := by
  unfold homogenize
  rw [Set.image_sSup, smulSet_sSup, Set.image_image]

def homogenizeSSupHom : sSupHom (Set A) (SubMulActionWithZero R≥0 W) where
  toFun := homogenize R W
  map_sSup' := homogenize_sSup

lemma homogenize_sInf_le (S : Set (Set A)) :
    homogenize R W (sInf S) ≤ sInf (homogenize R W '' S) := by
  unfold homogenize
  apply le_trans <| smulSet_mono (Set.image_sInter_subset_sInf_image _ _)
  apply le_trans (smulSet_sInf_le _)
  rw [Set.image_image]

section Nontrivial

variable [Nontrivial R]

@[simp] lemma ofPoint_mem_homogenize_iff {x : A} {s : Set A} :
    hom.ofPoint x ∈ homogenize R W s ↔ x ∈ s where
  mp := by
    rintro (h | ⟨x, ⟨y, hy, rfl⟩, r, h⟩)
    · exfalso; exact ofPoint_ne_zero _ h
    · have := congrArg hom.weight h
      simp only [weight_one, ← Nonneg.coe_smul, map_smul, smul_eq_mul, mul_one,
        Eq.comm, Nonneg.coe_eq_one] at this
      rw [this, one_smul] at h
      rwa [hom.ofPoint_injective h]
  mpr := ofPoint_mem_homogenize

lemma ofPoint_mem_homogenize_singleton {x y : A} :
    hom.ofPoint x ∈ homogenize R W {y} ↔ x = y := by simp

lemma homogenize_injective :
    Injective (homogenize R W : Set A → SubMulActionWithZero R≥0 W) := by
  intro s t h; ext
  repeat rw [← ofPoint_mem_homogenize_iff (R := R) (W := W)]
  rw [h]

@[simp] lemma homogenize_inj {s t : Set A} : homogenize R W s = homogenize R W t ↔ s = t :=
  homogenize_injective.eq_iff

lemma homogenize_strictMono : StrictMono (homogenize R W : Set A → SubMulActionWithZero R≥0 W) :=
  homogenize_monotone.strictMono_of_injective homogenize_injective

lemma homogenize_mono_iff {s t : Set A} :
    homogenize R W s ≤ homogenize R W t ↔ s ⊆ t where
  mp := by
    intro h x hx
    rw [← ofPoint_mem_homogenize_iff (R := R) (W := W)] at ⊢ hx
    exact h hx
  mpr := homogenize_mono

lemma homogenize_singleton_eq {x y : A} :
    homogenize R W {x} = homogenize R W {y} ↔ x = y := by simp

end Nontrivial

variable (A) in
def _root_.SubMulActionWithZero.dehomogenize (S : SubMulActionWithZero R≥0 W) : Set A :=
  hom.ofPoint ⁻¹' S

omit [IsOrderedRing R] in
lemma dehomogenize_mono {S T : SubMulActionWithZero R≥0 W} (h : S ≤ T) :
    dehomogenize A S ≤ dehomogenize A T :=
  Set.preimage_mono h

omit [IsOrderedRing R] in
lemma dehomogenize_monotone : Monotone (dehomogenize A : SubMulActionWithZero R≥0 W → Set A) :=
  fun _ _ => dehomogenize_mono

/-- Homogenization from sets to `SubMulActionWithZero` as an order homomorphism. -/
def dehomogenizeOrderHom : SubMulActionWithZero R≥0 W →o Set A where
  toFun := dehomogenize A
  monotone' := dehomogenize_monotone

omit [IsOrderedRing R] in
lemma dehomogenize_top : dehomogenize A (⊤ : SubMulActionWithZero R≥0 W) = Set.univ := by
  ext x; simp [dehomogenize]

omit [IsOrderedRing R] in
lemma dehomogenize_inf (s t : SubMulActionWithZero R≥0 W) :
    dehomogenize A (s ⊓ t) = dehomogenize A s ∩ dehomogenize A t := by
  ext x; simp [dehomogenize]

omit [IsOrderedRing R] in
lemma dehomogenize_sup (s t : SubMulActionWithZero R≥0 W) :
    dehomogenize A (s ⊔ t) = dehomogenize A s ∪ dehomogenize A t := by
  ext x; simp [dehomogenize]

def dehomogenizeLatticeHom : LatticeHom (SubMulActionWithZero R≥0 W) (Set A) where
  toFun := dehomogenize A
  map_sup' := dehomogenize_sup
  map_inf' := dehomogenize_inf

omit [IsOrderedRing R] in
lemma dehomogenize_sInf (S : Set (SubMulActionWithZero R≥0 W)) :
    dehomogenize A (sInf S) = sInf (dehomogenize A '' S) := by
  ext x; simp [dehomogenize]

section Nontrivial

variable [Nontrivial R]

lemma dehomogenize_sSup (S : Set (SubMulActionWithZero R≥0 W)) :
    dehomogenize A (sSup S) = sSup (dehomogenize A '' S) := by
  ext x; simpa [dehomogenize] using fun h => (ofPoint_ne_zero x h).elim

def dehomogenizeCompleteLatticeHom : CompleteLatticeHom (SubMulActionWithZero R≥0 W) (Set A) where
  toFun := dehomogenize A
  map_sInf' := dehomogenize_sInf
  map_sSup' := dehomogenize_sSup

@[simp] lemma dehomogenize_bot : (⊥ : SubMulActionWithZero R≥0 W).dehomogenize A = ∅ := by
  ext x; simpa using ofPoint_ne_zero _

/-- Dehomogenizing the homogenization of a set yields the same set again. -/
@[simp] theorem dehomogenize_homogenize (s : Set A) :
    dehomogenize A (homogenize R W s) = s := by
  ext x; simp [dehomogenize]

end Nontrivial

lemma homogenize_gc : GaloisConnection (homogenize R W) (dehomogenize A) := by
  -- TODO: we could use GaloisConnection.compose:
  --  * homogenize = closure ∘ image
  --  * dehomogenize = preimage ∘ coe
  sorry

end Ring

section IsStrictOrderedRing

variable [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [AddCommGroup V] [Module R V]
variable [AddTorsor V A]
variable [AddCommGroup W] [Module R W]

variable [hom : IsHomogenization R A W]

@[simp] lemma dehomogenize_weight_positive :
    dehomogenize A (hom.weight.positive : SubMulActionWithZero R≥0 W) = Set.univ := by
  ext x; simp [dehomogenize, weight_one]

-- TODO: move
-- TODO: have a version for `c ≥ 0` instead of 1 when `R` is a division ring?
lemma nonneg_smulSet_preimage_one_le_positive (f : W →ₗ[R] R) :
    R≥0 ∙ f ⁻¹' {1} ≤ f.positive := by
  intro x h hx0
  rw [mem_smulSet_of_ne_zero hx0] at h
  obtain ⟨y, hy, ⟨r, hr⟩, rfl⟩ := h
  rw [Set.mem_preimage, Set.mem_singleton_iff] at hy
  rw [Nonneg.mk_smul, map_smul, hy, smul_eq_mul, mul_one]
  by_cases hr0 : 0 = r
  · simp [← hr0] at hx0
  exact lt_of_le_of_ne hr hr0

-- TODO: delete in favor of `nonneg_smulSet_preimage_one_le_positive`
@[deprecated nonneg_smulSet_preimage_one_le_positive (since := "")]
lemma nonneg_smulSet_ofPoint_range_le_weight_positive :
    R≥0 ∙ (hom.ofPoint.range : Set W) ≤ hom.weight.positive := by
  rw [ofPoint_range_eq_preimage_weight_one]
  exact nonneg_smulSet_preimage_one_le_positive _

@[simp] lemma homogenize_univ_le_weight_positive :
    homogenize R W (Set.univ : Set A) ≤ hom.weight.positive := by
  simpa [homogenize] using nonneg_smulSet_ofPoint_range_le_weight_positive

lemma homogenize_le_weight_positive (s : Set A) :
    homogenize R W s ≤ hom.weight.positive :=
  le_trans (homogenize_mono (Set.subset_univ _)) homogenize_univ_le_weight_positive

@[simp] theorem homogenize_dehomogenize_le_weight_positive {S : SubMulActionWithZero R≥0 W} :
    homogenize R W (S.dehomogenize A) ≤ S ⊓ hom.weight.positive := by
  have aux : Set.range hom.ofPoint = hom.ofPoint.range := rfl
  rw [homogenize, dehomogenize, Set.image_preimage_eq_inter_range, aux]
  refine le_trans (smulSet_inter_le _ _) ?_
  simp only [smulSet_eq, le_inf_iff, inf_le_left, true_and]
  exact le_trans inf_le_right nonneg_smulSet_ofPoint_range_le_weight_positive

end IsStrictOrderedRing

section IsCancelMulZero_IsTorsionFree

variable [Ring R] [PartialOrder R] [IsOrderedRing R] [Nontrivial R] [IsCancelMulZero R]
variable [AddCommGroup V] [Module R V]
variable [AddTorsor V A]
variable [AddCommGroup W] [Module R W] [Module.IsTorsionFree R W]

variable [hom : IsHomogenization R A W]

/-- For the weaker vsion with `r = 1` see `ofPoint_mem_homogenize_iff`. -/
@[simp] lemma smul_ofPoint_mem_homogenize_iff {r : R} (hr : 0 < r) {x : A} (s : Set A) :
    r • hom.ofPoint x ∈ homogenize R W s ↔ x ∈ s where
  mp := by
    rintro (h | ⟨x, ⟨y, hy, rfl⟩, ⟨r', hr'⟩, h⟩)
    · exfalso
      exact smul_ne_zero hr.ne.symm (ofPoint_ne_zero x) h
    · have := congrArg hom.weight h
      simp only [map_smul, weight_one, smul_eq_mul, mul_one, Nonneg.mk_smul] at this
      rw [this] at hr h
      rw [Nonneg.mk_smul, smul_right_inj hr.ne.symm, ofPoint_injective.eq_iff] at h
      rwa [h]
  mpr := smul_ofPoint_mem_homogenize hr.le

lemma homogenize_inter (s t : Set A) :
    homogenize R W (s ∩ t) = homogenize R W s ⊓ homogenize R W t := by
  apply le_antisymm
  · exact homogenize_inter_le s t
  · rintro x hx
    obtain (rfl | ⟨y, hys, r, hr, rfl⟩) := mem_homogenize_iff_exist_lt_zero hx.1
    · exact SubMulActionWithZero.zero_mem
    refine smul_ofPoint_mem_homogenize hr.le ⟨hys, ?_⟩
    exact (smul_ofPoint_mem_homogenize_iff hr t).mp hx.2

/-- Homogenization from sets to `SubMulActionWithZero` as a lattice homomorphism. -/
def homogenizeLatticeHom : LatticeHom (Set A) (SubMulActionWithZero R≥0 W) where
  toFun := homogenize R W
  map_sup' := homogenize_union
  map_inf' := homogenize_inter

lemma homogenize_sInf {S : Set (Set A)} (hS : S.Nonempty) :
    homogenize R W (sInf S) = sInf (homogenize R W '' S) := by
  apply le_antisymm
  · exact homogenize_sInf_le S
  intro x hx
  simp only [SetLike.mem_sInf, Set.mem_image, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂] at hx
  obtain (rfl | ⟨y, hys, r, hr, rfl⟩) := mem_homogenize_iff_exist_lt_zero (hx _ hS.choose_spec)
  · exact SubMulActionWithZero.zero_mem
  exact smul_ofPoint_mem_homogenize hr.le fun t ht =>
    (smul_ofPoint_mem_homogenize_iff hr t).mp (hx _ ht)

lemma homogenize_inter' (s t : Set A) :
    homogenize R W (s ∩ t) = homogenize R W s ⊓ homogenize R W t := by
  simpa only [sInf_insert, sInf_singleton, Set.inf_eq_inter, Set.image_pair] using
    homogenize_sInf (R := R) (W := W) (S := {s, t}) (Set.insert_nonempty ..)

end IsCancelMulZero_IsTorsionFree

section DivisionRing

variable [DivisionRing R] [PartialOrder R] [IsOrderedRing R]
variable [AddCommGroup V] [Module R V]
variable [AddTorsor V A]
variable [AddCommGroup W] [Module R W]

variable [hom : IsHomogenization R A W]

-- TODO: move
-- TODO: generalize to `c ≥ 0` instead of 1?
lemma nonneg_smulSet_preimage_one_eq_positive (f : W →ₗ[R] R) : --{c : R} (hc : 0 < c):
    R≥0 ∙ (f ⁻¹' {1}) = f.positive := by
  apply le_antisymm
  · exact nonneg_smulSet_preimage_one_le_positive f
  intro x h
  by_cases hx0 : x = 0
  · simp [hx0]
  rw [mem_smulSet_of_ne_zero hx0]
  use (f x)⁻¹ • x
  specialize h hx0
  constructor
  · simp [inv_mul_cancel₀ h.ne.symm]
  · use ⟨_, h.le⟩
    simp [smul_smul, mul_inv_cancel₀ h.ne.symm]

-- TODO: delete in favor of `nonneg_smulSet_preimage_one_eq_positive`?
@[deprecated nonneg_smulSet_preimage_one_eq_positive (since := "")]
lemma nonneg_smulSet_ofPoint_range :
    R≥0 ∙ (hom.ofPoint.range : Set W) = hom.weight.positive := by
  rw [ofPoint_range_eq_preimage_weight_one]
  exact nonneg_smulSet_preimage_one_eq_positive _

@[simp] lemma homogenize_univ : homogenize R W (Set.univ : Set A) = hom.weight.positive := by
  simpa [homogenize] using nonneg_smulSet_ofPoint_range

end DivisionRing

section LinearOrderDivisionRing

variable [DivisionRing R] [LinearOrder R] [IsOrderedRing R]
variable [AddCommGroup V] [Module R V]
variable [AddTorsor V A]
variable [AddCommGroup W] [Module R W]

variable [hom : IsHomogenization R A W]

@[simp] theorem homogenize_dehomogenize {S : SubMulActionWithZero R≥0 W} :
    homogenize R W (S.dehomogenize A) = S ⊓ hom.weight.positive := by
  have aux : Set.range hom.ofPoint = hom.ofPoint.range := rfl
  rw [homogenize, dehomogenize, Set.image_preimage_eq_inter_range, smulSet_inter_left, aux,
    nonneg_smulSet_ofPoint_range]

@[simp] theorem homogenize_dehomogenize_of_le_weight_positive {S : SubMulActionWithZero R≥0 W}
    (hS : S ≤ hom.weight.positive) : homogenize R W (S.dehomogenize A) = S := by
  simp [homogenize_dehomogenize, hS]

def homogenizeOrderIso : Set A ≃o Set.Iic (hom.weight.positive : SubMulActionWithZero R≥0 W) where
  toFun s := ⟨_, homogenize_le_weight_positive s⟩
  invFun S := S.1.dehomogenize A
  left_inv := dehomogenize_homogenize
  right_inv S := by simp only [homogenize_dehomogenize_of_le_weight_positive S.2]
  map_rel_iff' := homogenize_mono_iff

end LinearOrderDivisionRing

end Affine
