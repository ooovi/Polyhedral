/-
Copyright (c) 2026 Olivia Röhrig, Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Olivia Röhrig, Martin Winter
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.Homogenization
public import Polyhedral.Mathlib.LinearAlgebra.AffineSpace.AffineMap
public import Polyhedral.Mathlib.LinearAlgebra.AffineSpace.Homogenization.Canonical

/-! This file defines affine homogenization as any vector space linearly equivalent to
`Homogenization`, the canonical homogenization from Mathlib. It also proves every such object
satisfies the axiomatic description from [Gallier2011GeometricMethods].

## Implementation notes
* The axiomatization in the literature is redundant. The universal property can be proven solely
from the subset of axioms used in the `ofEmbed` constructor, as is done by providing `lift`.

## References

* [J. Gallier, *Geometric Methods and Applications for Computer Science and
  Engineering*][Gallier2011GeometricMethods]
 -/

public noncomputable section

namespace Affine

section Ring

open Function Submodule

variable {R : Type*} [Ring R]
variable {V : Type*} [AddCommGroup V] [Module R V]
variable {A : Type*} [AddTorsor V A]
variable {W : Type*} [AddCommGroup W] [Module R W]

variable (R A W) in
/-- A triple of a ring `R`, `R`-affine space `A` and `R`-vector space `W` is a homogenization if
`W` is linearly equivalent to the canonical homogenization. -/
structure IsHomogenization where ofRepr ::
  repr : W ≃ₗ[R] Homogenization R A

namespace IsHomogenization

variable (ℋ : IsHomogenization R A W)

/-- The embedding of the affine space into the homogenization. -/
@[expose]
def ofPoint : A →ᵃ[R] W := ℋ.repr.symm.toAffineMap.comp Homogenization.ofPoint

/-- The embedding of the vector space into the homogenization. -/
@[expose]
def ofVector : V →ₗ[R] W := ℋ.repr.symm.toLinearMap ∘ₗ Homogenization.ofVector

/-- The linear map that is constantly `1` when restricted to `A`. -/
def weight : W →ₗ[R] R := Homogenization.weight ∘ₗ ℋ.repr.toLinearMap

lemma ofPoint_injective : Injective ℋ.ofPoint := by
  simpa [ofPoint] using Homogenization.ofPoint_injective

theorem ofVector_injective : Injective ℋ.ofVector := by
  simpa [ofVector] using Homogenization.ofVector_injective

theorem weight_eq_zero_iff {x : W} : ℋ.weight x = 0 ↔ ∃ v, x = ℋ.ofVector v := by
  simpa [← LinearEquiv.symm_apply_eq, weight, ofVector] using Homogenization.weight_eq_zero_iff

theorem weight_eq_one_iff {x : W} : ℋ.weight x = 1 ↔ ∃ p, x = ℋ.ofPoint p := by
  simpa [← LinearEquiv.symm_apply_eq, weight, ofPoint] using Homogenization.weight_eq_one_iff

lemma ofPoint_range_eq_preimage_weight_one : Set.range ℋ.ofPoint = ℋ.weight ⁻¹' {1} := by
  ext; simp [↓weight_eq_one_iff, eq_comm]

lemma ofVector_range_eq_preimage_weight_zero : Set.range ℋ.ofVector = ℋ.weight ⁻¹' {0} := by
  ext; simp [↓weight_eq_zero_iff, eq_comm]

/-- The homogenization of a point in `A` has weight 1. -/
@[simp]
lemma weight_ofPoint (a₀ : A) : ℋ.weight (ℋ.ofPoint a₀) = 1 := by simp [weight, ofPoint]

/-- The homogenization of a point in `V` has weight 0. -/
@[simp]
lemma weight_ofVector (v : V) : ℋ.weight (ℋ.ofVector v) = 0 := by simp [weight, ofVector]

-- the following two are in canonical hom in #43448
theorem ofPoint_ne_ofVector [Nontrivial R] (x : A) (v : V) : ℋ.ofPoint x ≠ ℋ.ofVector v :=
  ne_of_apply_ne ℋ.weight <| by simp

theorem ofPoint_ne_zero [Nontrivial R] (x : A) : ℋ.ofPoint x ≠ 0 := by
  simpa using ℋ.ofPoint_ne_ofVector x 0

/-- Embedding the underlying vector space is exactly the weight-0 hyperplane. -/
theorem ofVector_range_eq_weight_ker : ℋ.ofVector.range = ℋ.weight.ker := by
  apply SetLike.ext'
  rw [LinearMap.coe_range, ofVector_range_eq_preimage_weight_zero, LinearMap.ker]
  ext x
  simp

theorem span_range_ofPoint : span R (Set.range ℋ.ofPoint) = ⊤ := by
  simpa [Set.range_comp, ofPoint] using Homogenization.span_range_ofPoint

lemma weight_comp_repr :
    ℋ.weight ∘ₗ ℋ.repr.symm = Homogenization.weight (P := A) := by
  simp [weight, LinearMap.comp_assoc]

theorem repr_comp_ofPoint :
    ℋ.repr ∘ ℋ.ofPoint = Homogenization.ofPoint := by
  ext a; simp [ofPoint]

variable {U : Type*} [AddCommGroup U] [Module R U] in
/-- An affine map on `A` taking values in a vector space extends uniquely to a linear map on `W`.
-/
abbrev lift : (A →ᵃ[R] U) ≃+ (W →ₗ[R] U) :=
  Homogenization.lift.trans (ℋ.repr.arrowCongrAddEquiv (LinearEquiv.refl ..)).symm

open AffineMap LinearEquiv in
/-- The linear equivalence between the underlying vector space and its embedding. -/
def ofVectorRangeEquiv : V ≃ₗ[R] ℋ.ofVector.range where
  toFun v := ⟨ℋ.ofVector v, ℋ.ofVector.mem_range_self v⟩
  map_add' v w := by simp
  map_smul' r v := by simp
  invFun := (ofInjective ℋ.ofVector (linear_injective_iff _ |>.mpr ℋ.ofPoint_injective)).invFun
  left_inv := LinearEquiv.left_inv _
  right_inv := LinearEquiv.right_inv _

/-- The affine equivalence between the affine space space and its embedding. -/
public def ofPointRangeEquiv : A ≃ᵃ[R] ℋ.ofPoint.range :=
  .ofBijective
    ⟨ℋ.ofPoint.rangeRestrict_injective_iff.mpr ℋ.ofPoint_injective, fun ⟨_, a, rfl⟩ => ⟨a, rfl⟩⟩

lemma apply_ofPointRangeEquiv_symm (x : ℋ.ofPoint.range) :
    ℋ.ofPoint (ℋ.ofPointRangeEquiv.symm x) = x := by
  rw [← ℋ.ofPointRangeEquiv.right_inv x]
  congr; exact ℋ.ofPointRangeEquiv.symm_apply_apply _

section Instances

variable (R A) in
/-- The canonical homogenization is a homogenization. -/
def canonical : IsHomogenization R A (Homogenization R A) := ofRepr <| LinearEquiv.refl ..

/-- Construct `IsHomogenization R A W` from an embedding of the affine space `A` into the vector
space `W` and a weight map that is the constant 1-map on the embedded `A`. This follows the
axiomatization in Definition 4.2 of [Gallier2011GeometricMethods]
https://www.cis.upenn.edu/~jean/gma-v2-root.pdf -/
def ofEmbed {embed : A →ᵃ[R] W} (embed_inj : Injective embed) {weight : W →ₗ[R] R}
    (embed_range : Set.range embed = weight ⁻¹' {1}) :
  IsHomogenization R A W where
  repr := (LinearEquiv.ofBijective (Homogenization.lift embed)
    (Homogenization.lift_bijective_of_injective_of_range_preimage embed_inj embed_range)).symm

/-- The embedding used in the construction becomes the embedding in the homogenization. -/
theorem ofEmbed_ofPoint {embed : A →ᵃ[R] W} (embed_inj : Injective embed)
    {weight : W →ₗ[R] R} (embed_range : Set.range embed = weight ⁻¹' {1}) :
    (ofEmbed embed_inj embed_range).ofPoint = embed := by
  ext p
  exact Homogenization.lift_apply_ofPoint ..

/-- The weight used in the construction becomes the weight in the homogenization. -/
theorem ofEmbed_weight {embed : A →ᵃ[R] W} (embed_inj : Injective embed)
    {weight : W →ₗ[R] R} (embed_range : Set.range embed = weight ⁻¹' {1}) :
    (ofEmbed embed_inj embed_range).weight = weight := by
  ext w
  unfold IsHomogenization.weight
  have : Homogenization.lift embed ((ofEmbed embed_inj embed_range).repr w) = w := by
    rw [← LinearEquiv.ofBijective_apply]
    exact LinearEquiv.apply_symm_apply _ w
  rw [LinearMap.coe_comp, ← this, ← LinearMap.comp_apply]
  congr
  exact (Homogenization.comp_lift_eq_weight_of_range_preimage embed_range).symm

/-- A module is a homogenization of the weight-one hyperplane of any linear functional,
provided that hyperplane is nonempty. -/
def ofWeightOne (g : W →ₗ[R] R) [Nonempty ((affineSpan R {1}).comap g.toAffineMap)] :
    IsHomogenization R ((affineSpan R {1}).comap g.toAffineMap) W :=
  ofEmbed (weight := g) (AffineSubspace.subtype_injective _) (by simp; rfl)

@[simp]
lemma ofWeightOne_weight (g : W →ₗ[R] R) [Nonempty ((affineSpan R {1}).comap g.toAffineMap)] :
    (ofWeightOne g).weight = g := by
  simp [ofWeightOne, ofEmbed_weight]

end Instances

end IsHomogenization

end Ring

end Affine
