/-
Copyright (c) 2026 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/
module

public import Polyhedral.Mathlib.GroupTheory.GroupAction.SubMulActionWithZero.Nonneg
public import Polyhedral.Mathlib.LinearAlgebra.AffineSpace.Homogenization.Basic

import Polyhedral.Mathlib.Data.Set.Lattice.Image
import Polyhedral.Mathlib.Algebra.Order.Nonneg.Ring
import Polyhedral.Mathlib.Algebra.Order.Nonneg.DivisionRing

/-! This file defines homogenization of general sets. The homogenization is of type
`SubMulAction₀ R≥0 W`, which is closed under multiplication and always contains zero.
In particular, the homogenization is never empty. This enables to prove suitable order
isomorphisms. -/

@[expose] public section

namespace Affine.Set

open Function SubMulAction₀ IsHomogenization

variable {R V A W : Type*}

local notation3 "R≥0" => {c : R // 0 ≤ c}

section Ring

variable [Ring R] [PartialOrder R] [IsOrderedRing R]
variable [AddCommGroup V] [Module R V]
variable [AddTorsor V A]
variable [AddCommGroup W] [Module R W]

variable (hom : IsHomogenization R A W)

variable {x : A} {s : Set A}

def homogenize (s : Set A) : SubMulAction₀ R≥0 W := R≥0 ∙ (hom.ofPoint '' s)

-- potential notations for homogenization: `R≥0 ∙[W] s` or `R ∙₊[W] s`
--
-- /- Note that the character `∙` U+2219 used below is different from the scalar multiplication
-- character `•` U+2022. -/
-- /-- Notation for the homogenizationof a set `s`, short for `homogenize hom s`. -/
-- scoped notation:70 R:70 " ∙[" W "] " s:70 => homogenize hom s

lemma mem_homogenize {s : Set A} {x : W} :
    x ∈ homogenize hom s ↔ x = 0 ∨ ∃ y ∈ s, ∃ r : R, 0 ≤ r ∧ x = r • hom.ofPoint y := by
  simp [homogenize, mem_smulSet]

variable {hom} in
lemma mem_homogenize_iff_exist_lt_zero {s : Set A} {x : W} (hx : x ∈ homogenize hom s) :
    x = 0 ∨ ∃ y ∈ s, ∃ r : R, 0 < r ∧ x = r • hom.ofPoint y := by
  obtain (rfl | ⟨y, ⟨z, hz, rfl⟩, _, ⟨r, _⟩, hr0, rfl⟩) := mem_smulSet_iff_exists_ne_zero hx
  · exact .inl rfl
  · exact .inr ⟨z, hz, r, by rwa [← zero_lt_iff] at hr0, rfl⟩

lemma mem_homogenize_iff_ne_zero {s : Set A} {x : W} (hx : x ≠ 0) :
    x ∈ homogenize hom s ↔ ∃ y ∈ s, ∃ r : R, 0 ≤ r ∧ x = r • hom.ofPoint y := by
  simp [homogenize, mem_smulSet_of_ne_zero hx]

lemma mem_homogenize_iff_nonempty {s : Set A} {x : W} (hs : s.Nonempty) :
    x ∈ homogenize hom s ↔ ∃ y ∈ s, ∃ r : R, 0 ≤ r ∧ x = r • hom.ofPoint y := by
  have : (hom.ofPoint '' s).Nonempty := Set.image_nonempty.mpr hs
  simp [homogenize, mem_smulSet_of_nonempty this]

@[simp] lemma homogenize_empty : homogenize hom (∅ : Set A) = ⊥ := by
  ext x; simp [homogenize]

lemma ofPoint_image_subset_homogenize : hom.ofPoint '' s ⊆ homogenize hom s :=
  subset_smulSet

lemma ofPoint_mem_homogenize (hx : x ∈ s) : hom.ofPoint x ∈ homogenize hom s :=
  ofPoint_image_subset_homogenize _ ⟨x, hx, rfl⟩

lemma smul_ofPoint_mem_homogenize {r : R} (hr : 0 ≤ r) (h : x ∈ s) :
    r • hom.ofPoint x ∈ homogenize hom s :=
  smul_mem _ ⟨r, hr⟩ (ofPoint_mem_homogenize _ h)

lemma homogenize_mono {s t : Set A} (h : s ⊆ t) : homogenize hom s ≤ homogenize hom t :=
  smulSet_mono <| Set.image_mono h

lemma homogenize_monotone : Monotone (homogenize hom : Set A → SubMulAction₀ R≥0 W) :=
  fun _ _ => homogenize_mono _

/-- Homogenization from sets to `SubMulAction₀` as an order homomorphism. -/
def homogenizeOrderHom : Set A →o SubMulAction₀ R≥0 W where
  toFun := homogenize hom
  monotone' := homogenize_monotone _

lemma homogenize_union (s t : Set A) :
    homogenize hom (s ∪ t) = homogenize hom s ⊔ homogenize hom t := by
  simp only [homogenize, Set.image_union, smulSet_union]

lemma homogenize_inter_le (s t : Set A) :
    homogenize hom (s ∩ t) ≤ homogenize hom s ⊓ homogenize hom t := by
  unfold homogenize
  rw [Set.image_inter hom.ofPoint_injective]
  exact smulSet_inter_le _ _

lemma homogenize_sSup (S : Set (Set A)) :
    homogenize hom (sSup S) = sSup (homogenize hom '' S) := by
  unfold homogenize
  rw [Set.image_sSup, smulSet_sSup, Set.image_image]

def homogenizeSSupHom : sSupHom (Set A) (SubMulAction₀ R≥0 W) where
  toFun := homogenize hom
  map_sSup' := homogenize_sSup _

lemma homogenize_sInf_le (S : Set (Set A)) :
    homogenize hom (sInf S) ≤ sInf (homogenize hom '' S) := by
  unfold homogenize
  apply le_trans <| smulSet_mono (Set.image_sInter_subset_sInf_image _ _)
  apply le_trans (smulSet_sInf_le _)
  rw [Set.image_image]

section Nontrivial

variable [Nontrivial R]

@[simp] lemma ofPoint_mem_homogenize_iff {x : A} {s : Set A} :
    hom.ofPoint x ∈ homogenize hom s ↔ x ∈ s where
  mp := by
    rintro (h | ⟨x, ⟨y, hy, rfl⟩, r, h⟩)
    · exfalso; exact ofPoint_ne_zero _ _ h
    · have := congrArg hom.weight h
      simp only [weight_one, ← Nonneg.coe_smul, map_smul, smul_eq_mul, mul_one,
        Eq.comm, Nonneg.coe_eq_one] at this
      rw [this, one_smul] at h
      rwa [hom.ofPoint_injective h]
  mpr := ofPoint_mem_homogenize _

lemma ofPoint_mem_homogenize_singleton {x y : A} :
    hom.ofPoint x ∈ homogenize hom {y} ↔ x = y := by simp

lemma homogenize_injective :
    Injective (homogenize hom : Set A → SubMulAction₀ R≥0 W) := by
  intro s t h; ext
  repeat rw [← ofPoint_mem_homogenize_iff (R := R) (W := W)]
  rw [h]

@[simp] lemma homogenize_inj {s t : Set A} : homogenize hom s = homogenize hom t ↔ s = t :=
  (homogenize_injective _).eq_iff

lemma homogenize_strictMono : StrictMono (homogenize hom : Set A → SubMulAction₀ R≥0 W) :=
  (homogenize_monotone _).strictMono_of_injective (homogenize_injective _)

lemma homogenize_mono_iff {s t : Set A} :
    homogenize hom s ≤ homogenize hom t ↔ s ⊆ t where
  mp := by
    intro h x hx
    rw [← ofPoint_mem_homogenize_iff (R := R) (W := W)] at ⊢ hx
    exact h hx
  mpr := homogenize_mono _

lemma homogenize_singleton_eq {x y : A} :
    homogenize hom {x} = homogenize hom {y} ↔ x = y := by simp

end Nontrivial

end Ring

section Ring_no_OrderedRing

variable [Ring R] [PartialOrder R]
variable [AddCommGroup V] [Module R V]
variable [AddTorsor V A]
variable [AddCommGroup W] [Module R W]

variable (hom : IsHomogenization R A W)

variable {x : A} {s : Set A}

def _root_.SubMulAction₀.dehomogenize (S : SubMulAction₀ R≥0 W) : Set A :=
  hom.ofPoint ⁻¹' S

lemma dehomogenize_mono {S T : SubMulAction₀ R≥0 W} (h : S ≤ T) :
    dehomogenize hom S ≤ dehomogenize hom T :=
  Set.preimage_mono h

lemma dehomogenize_monotone : Monotone (dehomogenize hom : SubMulAction₀ R≥0 W → Set A) :=
  fun _ _ => dehomogenize_mono _

/-- Homogenization from sets to `SubMulAction₀` as an order homomorphism. -/
def dehomogenizeOrderHom : SubMulAction₀ R≥0 W →o Set A where
  toFun := dehomogenize hom
  monotone' := dehomogenize_monotone _

lemma dehomogenize_top : dehomogenize hom (⊤ : SubMulAction₀ R≥0 W) = Set.univ := by
  ext x; simp [dehomogenize]

lemma dehomogenize_inf (s t : SubMulAction₀ R≥0 W) :
    dehomogenize hom (s ⊓ t) = dehomogenize hom s ∩ dehomogenize hom t := by
  ext x; simp [dehomogenize]

lemma dehomogenize_sup (s t : SubMulAction₀ R≥0 W) :
    dehomogenize hom (s ⊔ t) = dehomogenize hom s ∪ dehomogenize hom t := by
  ext x; simp [dehomogenize]

def dehomogenizeLatticeHom : LatticeHom (SubMulAction₀ R≥0 W) (Set A) where
  toFun := dehomogenize hom
  map_sup' := dehomogenize_sup _
  map_inf' := dehomogenize_inf _

lemma dehomogenize_sInf (S : Set (SubMulAction₀ R≥0 W)) :
    dehomogenize hom (sInf S) = sInf (dehomogenize hom '' S) := by
  ext x; simp [dehomogenize]

section Nontrivial

variable [Nontrivial R]

lemma dehomogenize_sSup (S : Set (SubMulAction₀ R≥0 W)) :
    dehomogenize hom (sSup S) = sSup (dehomogenize hom '' S) := by
  ext x; simpa [dehomogenize] using fun h => (ofPoint_ne_zero _ x h).elim

def dehomogenizeCompleteLatticeHom : CompleteLatticeHom (SubMulAction₀ R≥0 W) (Set A) where
  toFun := dehomogenize hom
  map_sInf' := dehomogenize_sInf _
  map_sSup' := dehomogenize_sSup _

@[simp] lemma dehomogenize_bot : (⊥ : SubMulAction₀ R≥0 W).dehomogenize hom = ∅ := by
  ext x; simp only [Set.mem_empty_iff_false, iff_false]; exact ofPoint_ne_zero _ _

variable [IsOrderedRing R] in
/-- Dehomogenizing the homogenization of a set yields the same set again. -/
@[simp] theorem dehomogenize_homogenize (s : Set A) :
    dehomogenize hom (homogenize hom s) = s := by
  ext x; simp [dehomogenize]

end Nontrivial

variable [IsOrderedRing R] in
lemma homogenize_gc : GaloisConnection (homogenize hom) (dehomogenize hom) :=
  .compose Set.image_preimage smulSet_gc

end Ring_no_OrderedRing

section IsStrictOrderedRing

variable [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [AddCommGroup V] [Module R V]
variable [AddTorsor V A]
variable [AddCommGroup W] [Module R W]

variable (hom : IsHomogenization R A W)

@[simp] lemma dehomogenize_weight_positive :
    dehomogenize hom (hom.weight.positive : SubMulAction₀ R≥0 W) = Set.univ := by
  ext x; simp [dehomogenize, weight_one]

lemma nonneg_smulSet_ofPoint_range_le_weight_positive :
    R≥0 ∙ (Set.range hom.ofPoint) ≤ hom.weight.positive := by
  rw [ofPoint_range_eq_preimage_weight_one]
  exact nonneg_smulSet_preimage_one_le_positive _

@[simp] lemma homogenize_univ_le_weight_positive :
    homogenize hom (Set.univ : Set A) ≤ hom.weight.positive := by
  simpa [homogenize] using nonneg_smulSet_ofPoint_range_le_weight_positive _

lemma homogenize_le_weight_positive (s : Set A) :
    homogenize hom s ≤ hom.weight.positive :=
  le_trans (homogenize_mono _ (Set.subset_univ _)) (homogenize_univ_le_weight_positive _)

@[simp] theorem homogenize_dehomogenize_le_weight_positive {S : SubMulAction₀ R≥0 W} :
    homogenize hom (S.dehomogenize hom) ≤ S ⊓ hom.weight.positive := by
  have aux : Set.range hom.ofPoint = hom.ofPoint.range := rfl
  rw [homogenize, dehomogenize, Set.image_preimage_eq_inter_range, aux]
  refine le_trans (smulSet_inter_le _ _) ?_
  simp only [smulSet_eq, le_inf_iff, inf_le_left, true_and]
  exact le_trans inf_le_right (nonneg_smulSet_ofPoint_range_le_weight_positive _)

end IsStrictOrderedRing

section IsCancelMulZero_IsTorsionFree

variable [Ring R] [PartialOrder R] [IsOrderedRing R] [Nontrivial R] [IsCancelMulZero R]
variable [AddCommGroup V] [Module R V]
variable [AddTorsor V A]
variable [AddCommGroup W] [Module R W] [Module.IsTorsionFree R W]

variable (hom : IsHomogenization R A W)

/-- For the weaker version with `r = 1` see `ofPoint_mem_homogenize_iff`. -/
@[simp] lemma smul_ofPoint_mem_homogenize_iff {r : R} (hr : 0 < r) {x : A} (s : Set A) :
    r • hom.ofPoint x ∈ homogenize hom s ↔ x ∈ s where
  mp := by
    rintro (h | ⟨x, ⟨y, hy, rfl⟩, ⟨r', hr'⟩, h⟩)
    · exfalso
      exact smul_ne_zero hr.ne.symm (ofPoint_ne_zero _ x) h
    · have := congrArg hom.weight h
      simp only [map_smul, weight_one, smul_eq_mul, mul_one, Nonneg.mk_smul] at this
      rw [this] at hr h
      rw [Nonneg.mk_smul, smul_right_inj hr.ne.symm, hom.ofPoint_injective.eq_iff] at h
      rwa [h]
  mpr := smul_ofPoint_mem_homogenize _ hr.le

lemma homogenize_inter (s t : Set A) :
    homogenize hom (s ∩ t) = homogenize hom s ⊓ homogenize hom t := by
  apply le_antisymm
  · exact homogenize_inter_le _ s t
  · rintro x hx
    obtain (rfl | ⟨y, hys, r, hr, rfl⟩) := mem_homogenize_iff_exist_lt_zero hx.1
    · exact SubMulAction₀.zero_mem
    refine smul_ofPoint_mem_homogenize _ hr.le ⟨hys, ?_⟩
    exact (smul_ofPoint_mem_homogenize_iff _ hr t).mp hx.2

/-- Homogenization from sets to `SubMulAction₀` as a lattice homomorphism. -/
def homogenizeLatticeHom : LatticeHom (Set A) (SubMulAction₀ R≥0 W) where
  toFun := homogenize hom
  map_sup' := homogenize_union _
  map_inf' := homogenize_inter _

lemma homogenize_sInf {S : Set (Set A)} (hS : S.Nonempty) :
    homogenize hom (sInf S) = sInf (homogenize hom '' S) := by
  apply le_antisymm
  · exact homogenize_sInf_le _ S
  intro x hx
  simp only [SetLike.mem_sInf, Set.mem_image, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂] at hx
  obtain (rfl | ⟨y, hys, r, hr, rfl⟩) := mem_homogenize_iff_exist_lt_zero (hx _ hS.choose_spec)
  · exact SubMulAction₀.zero_mem
  exact smul_ofPoint_mem_homogenize _ hr.le fun t ht =>
    (smul_ofPoint_mem_homogenize_iff _ hr t).mp (hx _ ht)

end IsCancelMulZero_IsTorsionFree

section DivisionRing

variable [DivisionRing R] [PartialOrder R] [IsOrderedRing R]
variable [AddCommGroup V] [Module R V]
variable [AddTorsor V A]
variable [AddCommGroup W] [Module R W]

variable (hom : IsHomogenization R A W)

lemma nonneg_smulSet_ofPoint_range :
    R≥0 ∙ (Set.range hom.ofPoint) = hom.weight.positive := by
  rw [ofPoint_range_eq_preimage_weight_one]
  exact nonneg_smulSet_preimage_one_eq_positive _

@[simp] lemma homogenize_univ : homogenize hom (Set.univ : Set A) = hom.weight.positive := by
  simpa [homogenize] using nonneg_smulSet_ofPoint_range _

end DivisionRing

section LinearOrderDivisionRing

variable [DivisionRing R] [LinearOrder R] [IsOrderedRing R]
variable [AddCommGroup V] [Module R V]
variable [AddTorsor V A]
variable [AddCommGroup W] [Module R W]

variable (hom : IsHomogenization R A W)

@[simp] theorem homogenize_dehomogenize {S : SubMulAction₀ R≥0 W} :
    homogenize hom (S.dehomogenize hom) = S ⊓ hom.weight.positive := by
  rw [homogenize, dehomogenize, Set.image_preimage_eq_inter_range, smulSet_inter_left,
    nonneg_smulSet_ofPoint_range]

variable {hom} in
@[simp] theorem homogenize_dehomogenize_of_le_weight_positive {S : SubMulAction₀ R≥0 W}
    (hS : S ≤ hom.weight.positive) : homogenize hom (S.dehomogenize hom) = S := by
  simp [homogenize_dehomogenize, hS]

def homogenizeOrderIso : Set A ≃o Set.Iic (hom.weight.positive : SubMulAction₀ R≥0 W) where
  toFun s := ⟨_, homogenize_le_weight_positive _ s⟩
  invFun S := S.1.dehomogenize hom
  left_inv := dehomogenize_homogenize _
  right_inv S := by simp only [homogenize_dehomogenize_of_le_weight_positive S.2]
  map_rel_iff' := homogenize_mono_iff _

end LinearOrderDivisionRing

end Affine.Set
