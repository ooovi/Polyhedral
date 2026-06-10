
import Mathlib.Geometry.Convex.ConvexSpace.Module

import Polyhedral.Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Polyhedral.Mathlib.LinearAlgebra.AffineSpace.Homogenization.Canonical
import Polyhedral.Mathlib.LinearAlgebra.AffineSpace.Homogenization.Basic

import Polyhedral.Mathlib.GroupTheory.GroupAction.SubMulActionWithZero
import Polyhedral.Mathlib.GroupTheory.GroupAction.SubMulActionWithZero.Closure
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.SubMulActionWithZero

import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.LinearMap

/-! This file defines homogenization of general sets. The homogenization is of type
`SubMulActionWithZero R≥0 W`, which is closed under multiplication and always contains zero.
In particular, the homogenization is never empty. This enables to prove suitable order
isomorphisms. -/

namespace Affine.IsHomogenization

open Function SubMulActionWithZero

variable {R V A W : Type*}

local notation3 "R≥0" => {c : R // 0 ≤ c}

section Ring

variable [Ring R] [PartialOrder R]
variable [AddCommGroup V] [Module R V]
variable [AddTorsor V A]
variable [AddCommGroup W] [Module R W]

variable [hom : IsHomogenization R A W]

variable (R W) in
def homogenize (s : Set A) : SubMulActionWithZero R≥0 W := closure R≥0 (hom.ofPoint '' s)

@[simp] lemma homogenize_empty : homogenize R W (∅ : Set A) = ⊥ := by
  ext x; simp [homogenize]

lemma homogenize_mono {s t : Set A} (h : s ⊆ t) : homogenize R W s ≤ homogenize R W t :=
  closure_mono <| Set.image_mono h

lemma homogenize_monotone : Monotone (homogenize R W : Set A → SubMulActionWithZero R≥0 W) :=
  fun _ _ => homogenize_mono

/-- Homogenization from sets to `SubMulActionWithZero` as an order homomorphism. -/
def homogenizeOrderHom : Set A →o SubMulActionWithZero R≥0 W where
  toFun := homogenize R W
  monotone' := homogenize_monotone

lemma homogenize_union (s t : Set A) :
    homogenize R W (s ∪ t) = homogenize R W s ⊔ homogenize R W t := by
  simp only [homogenize, Set.image_union, closure_union]

lemma homogenize_inter (s t : Set A) :
    homogenize R W (s ∩ t) = homogenize R W s ⊓ homogenize R W t := by
  simp only [homogenize, Set.image_inter ofPoint_injective, closure_inter]

/-- Homogenization from sets to `SubMulActionWithZero` as an order homomorphism. -/
def homogenizeLatticeHom : LatticeHom (Set A) (SubMulActionWithZero R≥0 W) where
  toFun := homogenize R W
  map_sup' := homogenize_union
  map_inf' := homogenize_inter

lemma homogenize_sInf (s : Set (Set A)) :
    homogenize R W (sInf s) = sInf (homogenize R W '' s) := by
  sorry

lemma homogenize_sSup (s : Set (Set A)) :
    homogenize R W (sSup s) = sSup (homogenize R W '' s) := by
  sorry -- simp only [homogenize, Set.image_sSup, closure_sSup]

/-- Homogenization from sets to `SubMulActionWithZero` as an order homomorphism. -/
def homogenizeCompleteLatticeHom : CompleteLatticeHom (Set A) (SubMulActionWithZero R≥0 W) where
  toFun := homogenize R W
  map_sInf' := homogenize_sInf
  map_sSup' := homogenize_sSup

variable (A) in
def _root_.SubMulActionWithZero.dehomogenize (S : SubMulActionWithZero R≥0 W) : Set A :=
  hom.ofPoint ⁻¹' S

-- TODO: Move
variable [IsOrderedRing R] in
@[simp] lemma _root_.Nonneg.coe_eq_one (a : R≥0) : (a : R) = 1 ↔ a = 1 := by aesop

lemma homogenize_gc : GaloisConnection (homogenize R W) (dehomogenize A) := by
  -- TODO: we could use GaloisConnection.compose:
  --  * homogenize = closure ∘ image
  --  * dehomogenize = preimage ∘ coe
  sorry

section Nontrivial

variable [Nontrivial R]

@[simp] lemma dehomogenize_bot : (⊥ : SubMulActionWithZero R≥0 W).dehomogenize A = ∅ := by
  ext x; simpa using ofPoint_ne_zero _

variable [IsOrderedRing R] in
@[simp] lemma ofPoint_mem_homogenize {x : A} {s : Set A} :
    hom.ofPoint x ∈ homogenize R W s ↔ x ∈ s := by
  by_cases hs : s = ∅
  · simpa [hs] using ofPoint_ne_zero _
  simp only [homogenize]
  constructor <;> intro h
  · rw [mem_closure_iff_exists_smul] at h
    · obtain ⟨y, ⟨z, hz, rfl⟩, r, h⟩ := h
      have := congrArg hom.weight h
      simp only [weight_one, ← Nonneg.coe_smul, map_smul, smul_eq_mul, mul_one,
        Nonneg.coe_eq_one] at this
      simp only [this, one_smul] at h
      rwa [hom.ofPoint_injective h.symm]
    · simpa using Set.nonempty_iff_ne_empty.mpr hs
  · rw [mem_closure]
    exact fun _ hp => hp (Set.mem_image_of_mem hom.ofPoint h)

variable [IsOrderedRing R] in
/-- Dehomogenizing the homogenization of a set yields the same set again. -/
@[simp] theorem dehomogenize_homogenize (s : Set A) :
    dehomogenize A (homogenize R W s) = s := by
  ext x; simp [dehomogenize]

end Nontrivial

end Ring

section IsStrictOrderedRing

variable [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [AddCommGroup V] [Module R V]
variable [AddTorsor V A]
variable [AddCommGroup W] [Module R W]

variable [hom : IsHomogenization R A W]

lemma dehomogenize_top : dehomogenize A (⊤ : SubMulActionWithZero R≥0 W) = Set.univ := sorry

lemma dehomogenize_weight_positive :
    dehomogenize A (hom.weight.positive : SubMulActionWithZero R≥0 W) = Set.univ := sorry

lemma closure_ofPoint_range_le_weight_positive :
    closure R≥0 (hom.ofPoint.range : Set W) ≤ hom.weight.positive := by
  intro x h hx0
  rw [mem_closure_iff_exists_smul_of_not_zero hx0] at h
  obtain ⟨y, ⟨z, rfl⟩, r, rfl⟩ := h
  obtain ⟨r, hr⟩ := r
  simp only [LinearMap.map_smul_of_tower, weight_one, Nonneg.mk_smul, smul_eq_mul, mul_one]
  have hr0 : r ≠ 0 := by
    by_contra hr
    simp [hr] at hx0
  exact lt_of_le_of_ne hr hr0.symm

@[simp] lemma homogenize_univ_le_weight_positive :
    homogenize R W (Set.univ : Set A) ≤ hom.weight.positive := by
  simpa [homogenize] using closure_ofPoint_range_le_weight_positive

lemma homogenize_le_weight_positive (s : Set A) :
    homogenize R W s ≤ hom.weight.positive :=
  le_trans (homogenize_mono (Set.subset_univ _)) homogenize_univ_le_weight_positive

@[simp] theorem homogenize_dehomogenize_le_weight_positive {S : SubMulActionWithZero R≥0 W} :
    homogenize R W (S.dehomogenize A) ≤ S ⊓ hom.weight.positive := by
  -- simp only [homogenize, dehomogenize, Set.image_preimage_eq_inter_range,
  --   closure_inter, closure_eq]
  -- congr; exact closure_ofPoint_range_le_weight_positive
  sorry

end IsStrictOrderedRing

section DivisionRing

variable [DivisionRing R] [PartialOrder R] [IsOrderedRing R]
variable [AddCommGroup V] [Module R V]
variable [AddTorsor V A]
variable [AddCommGroup W] [Module R W]

variable [hom : IsHomogenization R A W]

lemma closure_ofPoint_range : closure R≥0 (hom.ofPoint.range : Set W) = hom.weight.positive := by
  apply le_antisymm
  · exact closure_ofPoint_range_le_weight_positive
  intro x h
  by_cases hx0 : x = 0
  · simp [hx0]
  rw [mem_closure_iff_exists_smul_of_not_zero hx0]
  use (hom.weight x)⁻¹ • x
  specialize h hx0
  constructor
  · simp [ofPoint_range_eq_preimage_weight_one, inv_mul_cancel₀ h.ne.symm]
  · use ⟨_, h.le⟩
    simp [smul_smul, mul_inv_cancel₀ h.ne.symm]

@[simp] lemma homogenize_univ : homogenize R W (Set.univ : Set A) = hom.weight.positive := by
  simpa [homogenize] using closure_ofPoint_range

@[simp] theorem homogenize_dehomogenize {S : SubMulActionWithZero R≥0 W} :
    homogenize R W (S.dehomogenize A) = S ⊓ hom.weight.positive := by
  simp only [homogenize, dehomogenize, Set.image_preimage_eq_inter_range,
    closure_inter, closure_eq]
  congr; exact closure_ofPoint_range

@[simp] theorem homogenize_dehomogenize_of_le_weight_positive {S : SubMulActionWithZero R≥0 W}
    (hS : S ≤ hom.weight.positive) : homogenize R W (S.dehomogenize A) = S := by
  simp [homogenize_dehomogenize, hS]

def homogenizeOrderIso : Set A ≃o Set.Iic (hom.weight.positive : SubMulActionWithZero R≥0 W) where
  toFun s := ⟨_, homogenize_le_weight_positive s⟩
  invFun S := S.1.dehomogenize A
  left_inv := dehomogenize_homogenize
  right_inv S := by simp only [homogenize_dehomogenize_of_le_weight_positive S.2]
  map_rel_iff' := by
    intro s t
    simp
    sorry

end DivisionRing

end Affine.IsHomogenization
