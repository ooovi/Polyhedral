import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Convexity
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Lineal
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.AffineSpace
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Lattice
import Polyhedral.Mathlib.LinearAlgebra.AffineSpace.Homogenization.Basic

/-! This file defines homogenization of convex sets in affine spaces. -/

open Convexity Pointwise Set PointedCone Submodule

namespace Convexity.ConvexSet

section Ring

open Convexity

variable {R : Type*} [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
variable {V : Type*} [AddCommGroup V] [Module R V]
variable {A : Type*} [AddTorsor V A]
variable {W : Type*} [AddCommGroup W] [Module R W]
variable [hom : Affine.IsHomogenization R A W]

attribute [local instance] AddTorsor.toConvexSpace

variable (W) in
/-- The homogenization cone of a convex set in an affine space. -/
def homogenize (P : ConvexSet R A) : PointedCone R W := hull R (hom.ofPoint '' P)

/-- Homogenization from convex set to convex cones as an order homomorphism. -/
def homogenizeOrderHom : ConvexSet R A →o PointedCone R W where
  toFun := homogenize W
  monotone' _ _ PlQ := Submodule.span_mono <| Set.image_mono PlQ

lemma homogenize_bot : homogenize W (⊥ : ConvexSet R A) = ⊥ := by
  simp [homogenize, Bot.bot]

lemma homogenize_top : homogenize W (⊤ : ConvexSet R A) = hom.weight.positive := by
  rw [homogenize, LinearMap.positive_eq_hull_preimage_singleton hom.weight 1 one_ne_zero,
    ← hom.ofPoint_range_eq_preimage_weight_one]
  congr
  ext x
  simp

lemma homogenize_mono {K₁ K₂ : ConvexSet R A} (h : K₁ ≤ K₂) :
    K₁.homogenize W ≤ K₂.homogenize W := span_mono <| Set.image_mono h

lemma homogenize_le_weight_positive (K : ConvexSet R A) :
    homogenize W K ≤ hom.weight.positive := by
  exact LinearMap.hull_le_positive_of_subset_preimage_singleton one_ne_zero fun _ ↦ by
    rintro ⟨x, -, rfl⟩
    simp [hom.weight_one]

lemma weight_pos_of_mem_homogenize {x} {P : ConvexSet R A} (h : x ∈ homogenize W P)
    (hx : x ≠ 0) :
    0 < hom.weight x :=
  (homogenize_le_weight_positive (W := W) P h) hx

lemma weight_nonneg_of_mem_homogenize {x : W} {P : ConvexSet R A} (h : x ∈ homogenize W P) :
    0 ≤ hom.weight x :=
  (LinearMap.mem_positive'.mp (homogenize_le_weight_positive (W := W) P h)).1

lemma homogenize_salient {K : ConvexSet R A} : PointedCone.Salient (homogenize W K) :=
  Salient.of_le_salient hom.weight.positive_salient (homogenize_le_weight_positive K)

attribute [local instance] AddTorsor.toConvexSpace
variable [IsModuleConvexSpace R W] -- WARNING: this is currently inferred! This is dangerous

variable (A) in
def dehomogenize (C : PointedCone R W) : ConvexSet R A :=
  ⟨_, C.isConvexSet.preimage hom.ofPoint.isAffineMap⟩

alias _root_.PointedCone.dehomogenize := dehomogenize

lemma dehomogenize_bot : dehomogenize A (⊥ : PointedCone R W) = ⊥ := sorry

lemma dehomogenize_top : dehomogenize A (⊤ : PointedCone R W) = ⊤ := sorry

lemma dehomogenize_weight_positive : dehomogenize A hom.weight.positive = ⊤ := sorry

variable (A) in
lemma dehomogenize_mono {C₁ C₂ : PointedCone R W} (h : C₁ ≤ C₂) :
    dehomogenize A C₁ ≤ dehomogenize A C₂ := Set.preimage_mono <| Set.preimage_mono h
    -- Q: why Set.preimage_mono twice?

-- This lemma is just `Set.image_preimage_eq_inter_range` in disguise. It is likely not needed.
lemma ofPoint_dehomogenize_eq_inter_ofPoint (C : PointedCone R W) :
    hom.ofPoint '' dehomogenize A C = (C : Set W) ∩ hom.ofPoint.range := by
  ext x
  simp only [Set.mem_image, SetLike.mem_coe, Set.mem_inter_iff, AffineMap.mem_range]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨hy, by use y⟩
  · rintro ⟨hxC, y, rfl⟩
    use y
    simpa

end Ring

section Field

variable {R : Type*} [Field R] [LinearOrder R] [IsOrderedRing R]
variable {V : Type*} [AddCommGroup V] [Module R V]
variable {A : Type*} [AddTorsor V A]
variable {W : Type*} [AddCommGroup W] [Module R W]
variable [hom : Affine.IsHomogenization R A W]

attribute [local instance] AddTorsor.toConvexSpace
variable [IsModuleConvexSpace R W]

lemma smul_pos_of_mem_homogenize {P : ConvexSet R A} {x} (h : x ∈ homogenize W P) (hx : x ≠ 0) :
    x ∈ Set.Ioi (0 : R) • hom.ofPoint '' (P : Set A) :=
  (mem_hull_iff_mem_pos_smul_of_convex_nonzero
    (P.isConvexSet.image hom.ofPoint.isAffineMap) hx).mp h

-- TODO: This lemma should be proven for general sets (homogenizing to SubMulAction) and then
--  applied here as a special case.
variable (W) in
lemma ofPoint_mem_homogenize_iff_mem (x : A) (P : ConvexSet R A) :
    hom.ofPoint x ∈ homogenize W P ↔ x ∈ P := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simpa using mem_span_of_mem (Set.mem_image_of_mem hom.ofPoint h)⟩
  obtain ⟨_, _, h'⟩ := smul_pos_of_mem_homogenize (Set.mem_preimage.mpr h) (hom.ofPoint_ne_zero x)
  obtain ⟨_, ⟨_, _, hyy'⟩, hy'⟩ := Set.mem_smul_set.mp h'
  have := congrArg hom.weight hy'
  simp [← hyy', hom.weight_one] at this
  simp only [this, Set.mem_image, one_smul, exists_eq_right] at h'
  obtain ⟨_, _, hxx'⟩ := h'
  simpa [← hom.ofPoint_injective hxx']

/-- Dehomogenizing the homogenization of a convex set yields the same set again. -/
@[simp] theorem dehomogenize_homogenize (P : ConvexSet R A) :
    dehomogenize A (homogenize W P) = P := by
  ext x; exact ofPoint_mem_homogenize_iff_mem _ _ _

/-- If the entire cone save the origin are at positive weight, homogenizing the dehomogenization
of the homogenize yields the cone again. -/
theorem homogenize_dehomogenize_of_le_positive {C : PointedCone R W}
    (hC : C ≤ hom.weight.positive) : homogenize W (dehomogenize A C) = C := by
  by_cases hbot : C = ⊥
  · simp [hbot, homogenize, dehomogenize]
  · apply SetLike.ext'
    unfold homogenize
    rw [eq_Ici_zero_smul_inter_preimage_of_pos_of_ne_bot hC zero_lt_one hbot,
      ofPoint_dehomogenize_eq_inter_ofPoint, ← hom.ofPoint_range_eq_preimage_weight_one]
    convert hull_eq_smul ?_ (C.isConvexSet.inter hom.ofPoint.range_isConvexSet)
    · obtain ⟨y, hyC, hy0⟩ := exists_mem_ne_zero_of_ne_bot hbot
      obtain ⟨_, hy'⟩ : (hom.weight y)⁻¹ • y ∈ (hom.ofPoint.range : Set W) := by
        simpa [hom.ofPoint_range_eq_preimage_weight_one]
          using inv_mul_cancel₀ (@hC y hyC hy0).ne.symm
      use (hom.weight y)⁻¹ • y, C.smul_mem (inv_nonneg.mpr (@hC y hyC hy0).le) hyC
      simp [← hy']

lemma homogenize_mono_iff {K₁ K₂ : ConvexSet R A} :
    K₁.homogenize W ≤ K₂.homogenize W ↔ K₁ ≤ K₂ where
  mp h := by simpa using dehomogenize_mono A h
  mpr := homogenize_mono

-- Issue #66
/-- The lattice of convex sets is isomorphic to the lattice of convex sub-cones of the
positive cone. -/
def homogenizeOrderEquiv : ConvexSet R A ≃o Set.Iic hom.weight.positive where
  toFun K := ⟨_, K.homogenize_le_weight_positive⟩
  invFun C := dehomogenize A C.1
  left_inv K := dehomogenize_homogenize K
  right_inv C := by dsimp; congr; exact homogenize_dehomogenize_of_le_positive C.2
  map_rel_iff' := homogenize_mono_iff

end Field

end Convexity.ConvexSet
