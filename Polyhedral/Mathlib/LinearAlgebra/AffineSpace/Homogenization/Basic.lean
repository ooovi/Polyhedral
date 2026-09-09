/-
Copyright (c) 2026 Olivia Röhrig, Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Olivia Röhrig, Martin Winter
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.Homogenization
public import Polyhedral.Mathlib.LinearAlgebra.AffineSpace.AffineMap

import Mathlib.Geometry.Convex.ConvexSpace.Module
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic

/-! This file defines affine homogenization axiomatically and proves every object fulfilling the
axioms is linearly equivalent to `Homogenization`, the canonical homogenization from Mathlib.

## Implementation notes
* The axiomatization in the literature is redundant. The universal property can be proven solely
from the subset of axioms used in `IsHomogenization`, as is done in lemma `extend`. It is
convenient to use the linear equivalence between any homogenization and `Homogenization`
for the proof.

## References

* [J. Gallier, *Geometric Methods and Applications for Computer Science and
  Engineering*][Gallier2011GeometricMethods]
 -/

@[expose] public section

namespace Affine

section Ring

open Function Submodule

variable {R : Type*} [Ring R]
variable {V : Type*} [AddCommGroup V] [Module R V]
variable {A : Type*} [AddTorsor V A]
variable {W : Type*} [AddCommGroup W] [Module R W]

variable (R A W) in
/-- An embedding of an affine space `A` into a vector space `W` s.t. the image of `A` is exactly the
weight-1 hyperplane under a given linear weight map.
Follows Definition 4.2 in [Gallier2011GeometricMethods]
https://www.cis.upenn.edu/~jean/gma-v2-root.pdf -/
structure IsHomogenization where
  ofPoint : A →ᵃ[R] W
  ofPoint_injective : Injective ofPoint
  weight : W →ₗ[R] R
  ofPoint_range_eq_preimage_weight_one : Set.range ofPoint = weight ⁻¹' {1}

variable (R A) in
/-- The canonical homogenization is a homogenization. -/
noncomputable def IsHomogenization.canonical :
    IsHomogenization R A (Homogenization R A) where
  ofPoint := Homogenization.ofPoint
  ofPoint_injective := Homogenization.ofPoint_injective
  weight := Homogenization.weight
  ofPoint_range_eq_preimage_weight_one := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      simp
    · exact fun hx ↦ (Homogenization.weight_eq_one_iff.mp hx).imp fun _ hp ↦ hp.symm

namespace IsHomogenization

variable (ℋ : IsHomogenization R A W)

abbrev ofVector := ℋ.ofPoint.linear

theorem ofVector_injective : Injective ℋ.ofVector := by
  simp [ℋ.ofPoint_injective]

/-- Embedding the underlying vector space is exactly the weight-0 hyperplane. -/
theorem ofVector_range_eq_weight_ker : ℋ.ofVector.range = ℋ.weight.ker := by
  ext x
  let a₀ := Classical.arbitrary A
  simp only [LinearMap.mem_range, LinearMap.mem_ker]
  have : (∃ y, ℋ.ofVector y = x) ↔ ∃ a b : A, ℋ.ofVector (a -ᵥ b) = x :=
    ⟨fun ⟨y, hy⟩ => ⟨y +ᵥ a₀, a₀, by simp [vadd_vsub, hy]⟩, fun ⟨a, b, hab⟩ => ⟨a -ᵥ b, hab⟩⟩
  rw [this]
  have hh := Set.ext_iff.mp ℋ.ofPoint_range_eq_preimage_weight_one
  constructor
  · rintro ⟨a, b, hab⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hh
    simp [← hab, map_sub, (hh (ℋ.ofPoint b)).mp ⟨b, rfl⟩, (hh (ℋ.ofPoint a)).mp ⟨a, rfl⟩]
  · intro h
    have ha := Set.mem_preimage.mp <| (hh (ℋ.ofPoint a₀)).mp (by simp)
    obtain ⟨b, hb⟩ : x + ℋ.ofPoint a₀ ∈ (Set.range ℋ.ofPoint) := by
      simpa [ℋ.ofPoint_range_eq_preimage_weight_one, Set.mem_preimage, map_add, h]
    exact ⟨b, a₀, by simp [AffineMap.linearMap_vsub, hb]⟩

/-- The homogenization of a point in `A` has weight 1. -/
lemma weight_one (a₀ : A) : ℋ.weight (ℋ.ofPoint a₀) = 1 := by
  convert Set.ext_iff.mp ℋ.ofPoint_range_eq_preimage_weight_one (ℋ.ofPoint a₀)
  simp [exists_apply_eq_apply, Set.mem_preimage, Set.mem_singleton_iff, true_iff]

variable [Nontrivial R] in
theorem ofPoint_ne_zero (x : A) : ℋ.ofPoint x ≠ (0 : W) := by
  intro hn
  have := congrArg ℋ.weight hn
  simp [ℋ.weight_one x] at this

/-- The homogenization of a point in `V` has weight 0. -/
lemma weight_zero (v : V) : ℋ.weight (ℋ.ofVector v) = 0 := by
  simp [LinearMap.mem_ker.mp, ← ofVector_range_eq_weight_ker]

theorem span_range_ofPoint : span R (Set.range ℋ.ofPoint) = ⊤ := by
  refine eq_top_iff'.mpr (fun x ↦ ?_)
  let a₀ := Classical.arbitrary A
  -- projecting x to weight 0 along a₀ gives sth in the span of image of ofPoint
  have hlin : x - ℋ.weight x • ℋ.ofPoint a₀ ∈ Submodule.span R ℋ.ofPoint.range := by
    obtain ⟨v, hv⟩ : x - ℋ.weight x • ℋ.ofPoint a₀ ∈ ℋ.ofVector.range := by
      simp [ofVector_range_eq_weight_ker, ℋ.weight_one a₀]
    have : ℋ.ofVector v = ℋ.ofPoint (v +ᵥ a₀) - ℋ.ofPoint a₀ := by simp
    rw [← hv, this]
    apply Submodule.sub_mem <;> apply Submodule.subset_span
    · exact ⟨v +ᵥ a₀, rfl⟩
    · exact ⟨a₀, rfl⟩
  simpa using
    Submodule.add_mem _ hlin <| smul_mem _ (ℋ.weight x) (subset_span ⟨a₀, rfl⟩)

/-- The canonical linear map from `Homogenization R A` to any homogenization `W` of `A`. -/
noncomputable def ofCanonical : Homogenization R A →ₗ[R] W := Homogenization.lift ℋ.ofPoint

@[simp] lemma ofCanonical_ofPoint (a : A) :
    ℋ.ofCanonical (Homogenization.ofPoint a) = ℋ.ofPoint a := by
  simp [ofCanonical]

@[simp] lemma ofCanonical_ofVector (v : V) :
    ℋ.ofCanonical (Homogenization.ofVector v) = ℋ.ofVector v := by
  simp [ofCanonical]

lemma weight_comp_ofCanonical :
    ℋ.weight ∘ₗ ℋ.ofCanonical = (Homogenization.weight : Homogenization R A →ₗ[R] R) :=
  Homogenization.hom_ext fun a ↦ by simp [weight_one]

@[simp] lemma weight_ofCanonical (x : Homogenization R A) :
    ℋ.weight (ℋ.ofCanonical x) = Homogenization.weight x :=
  congr($(weight_comp_ofCanonical _) x)

theorem ofCanonical_bijective : Bijective ℋ.ofCanonical := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have hw : Homogenization.weight x = 0 := by
      rw [← ℋ.weight_ofCanonical x, hx, map_zero]
    obtain ⟨v, rfl⟩ := Homogenization.weight_eq_zero_iff.mp hw
    rw [ofCanonical_ofVector, map_eq_zero_iff _ ℋ.ofVector_injective] at hx
    simp [hx]
  · rw [← LinearMap.range_eq_top, ← top_le_iff, ← ℋ.span_range_ofPoint, Submodule.span_le,
      Set.range_subset_iff]
    exact fun a ↦ ⟨Homogenization.ofPoint a, by simp⟩

/-- Every homogenization is linearly equivalent to the canonical homogenization. -/
noncomputable def canonEquiv : W ≃ₗ[R] Homogenization R A :=
  (LinearEquiv.ofBijective _ ℋ.ofCanonical_bijective).symm

@[simp] lemma canonEquiv_symm_apply (x : Homogenization R A) :
    ℋ.canonEquiv.symm x = ℋ.ofCanonical x :=
  rfl

@[simp] lemma ofCanonical_canonEquiv (x : W) : ℋ.ofCanonical (ℋ.canonEquiv x) = x :=
  ℋ.canonEquiv.symm_apply_apply x

@[simp] lemma canonEquiv_ofPoint (a : A) :
    ℋ.canonEquiv (ℋ.ofPoint a) = Homogenization.ofPoint a :=
  ℋ.canonEquiv.symm.injective <| by simp

theorem canonEquiv_canonical_ofPoint :
    ℋ.canonEquiv ∘ ℋ.ofPoint = Homogenization.ofPoint := by
  ext a; simp

theorem weight_canonEquiv : Homogenization.weight ∘ ℋ.canonEquiv = ℋ.weight := by
  ext x
  rw [Function.comp_apply, ← ℋ.weight_ofCanonical (ℋ.canonEquiv x),
    ofCanonical_canonEquiv]

-- proving the universal property using the equiv
/-- A homogenization `W` of `A` satisfies the universal property that every affine map from `A`
into any vector space extends uniquely to a linear map from `W` to the vector space. -/
theorem extend (U : Type*) [AddCommGroup U] [Module R U]
    (f : A →ᵃ[R] U) :
    ∃! (F : W →ₗ[R] U), F ∘ ℋ.ofPoint = f := by
  refine ⟨Homogenization.lift f ∘ₗ ℋ.canonEquiv.toLinearMap, funext fun a ↦ by simp, ?_⟩
  intro g hg
  have : g ∘ₗ ℋ.canonEquiv.symm.toLinearMap = Homogenization.lift f :=
    Homogenization.hom_ext fun a ↦ by simpa using congrFun hg a
  rw [← this, LinearMap.comp_assoc]
  simp

open AffineMap LinearEquiv in
/-- The linear equivalence between the underlying vector space and its embedding. -/
noncomputable def ofVectorRangeEquiv : V ≃ₗ[R] ℋ.ofVector.range := {
  toFun v := ⟨ℋ.ofVector v, ℋ.ofVector.mem_range_self v⟩
  map_add' v w := by simp
  map_smul' r v := by simp
  invFun :=
    (ofInjective ℋ.ofVector (linear_injective_iff _ |>.mpr ℋ.ofPoint_injective)).invFun
  left_inv :=
    (ofInjective ℋ.ofVector (linear_injective_iff _ |>.mpr ℋ.ofPoint_injective)).left_inv
  right_inv v' := by simp
}

/-- The affine equivalence between the affine space space and its embedding. -/
public noncomputable def ofPointRangeEquiv : A ≃ᵃ[R] ℋ.ofPoint.range :=
  .ofBijective
    ⟨ℋ.ofPoint.rangeRestrict_injective_iff.mpr ℋ.ofPoint_injective, fun ⟨_, a, rfl⟩ => ⟨a, rfl⟩⟩

lemma apply_ofPointRangeEquiv_symm (x : ℋ.ofPoint.range) :
    ℋ.ofPoint (ℋ.ofPointRangeEquiv.symm x) = x := by
  rw [← ℋ.ofPointRangeEquiv.right_inv x]
  congr; exact ℋ.ofPointRangeEquiv.symm_apply_apply _

end IsHomogenization

end Ring

end Affine
