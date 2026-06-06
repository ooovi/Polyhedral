import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Convexity
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Lineal
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.AffineSpace
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Lattice
import Polyhedral.Mathlib.LinearAlgebra.AffineSpace.Homogenization.Basic

namespace Affine.IsHomogenization

section Ring

open Convexity

variable {R : Type*} [Ring R]
variable [PartialOrder R] [IsStrictOrderedRing R]
variable {V : Type*} [AddCommGroup V] [Module R V]
variable {A : Type*} [AddTorsor V A]
variable {W : Type*} [AddCommGroup W] [Module R W]
variable [hom : Affine.IsHomogenization R A W]

attribute [local instance] AddTorsor.toConvexSpace

variable (W) in
/-- The homogenization cone of a convex set in an affine space. -/
def homogenize (P : ConvexSet R A) := PointedCone.hull R (hom.ofPoint '' P)

lemma homogenize_bot : homogenize W (⊥ : ConvexSet R A) = ⊥ := by
  simp [homogenize, Bot.bot]

def homogenizeHom :
    OrderHom (ConvexSet R A) (PointedCone R W) where
  toFun P := homogenize W P
  monotone' _ _ PlQ := Submodule.span_mono <| Set.image_mono PlQ

variable [IsModuleConvexSpace R W]

variable (A) in
def dehomogenize (C : PointedCone R W) : ConvexSet R A :=
  ⟨_, C.isConvexSet.preimage hom.ofPoint.isAffineMap⟩

lemma ofPoint_dehomogenize_eq_inter_ofPoint (C : PointedCone R W) :
    hom.ofPoint '' (dehomogenize A C) = (C : Set W) ∩ hom.ofPoint.range := by
  ext x
  simp only [dehomogenize, Set.mem_image, SetLike.mem_coe, Set.mem_inter_iff,
    AffineMap.mem_range]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨hy, by use y⟩
  · rintro ⟨hxC, y, rfl⟩
    use y
    simpa

end Ring

section Field

open Pointwise Set Convexity PointedCone Submodule

variable {R : Type*} [Field R]
variable [LinearOrder R] [IsOrderedRing R]
variable {V : Type*} [AddCommGroup V] [Module R V]
variable {A : Type*} [AddTorsor V A]
variable {W : Type*} [AddCommGroup W] [Module R W]
variable [hom : Affine.IsHomogenization R A W]

attribute [local instance] AddTorsor.toConvexSpace
variable [IsModuleConvexSpace R W]

theorem homogenize_salient {P : ConvexSet R A} : PointedCone.Salient (homogenize W P) := by
  simp [homogenize]
  -- use salient_of_pos_linearMap with hom.weight and weight_nonneg_of_mem_homogenize
  -- issue #33
  sorry

lemma smul_pos_of_mem_homogenize {P : ConvexSet R A} {x} (h : x ∈ homogenize W P) (hx : x ≠ 0) :
    x ∈ Ioi (0 : R) • hom.ofPoint '' (P : Set A) :=
  (mem_hull_iff_mem_pos_smul_of_convex_nonzero (P.isConvexSet.image ofPoint.isAffineMap) hx).mp h

lemma weight_pos_of_mem_homogenize {x} {P : ConvexSet R A} (h : x ∈ homogenize W P) (hx : x ≠ 0) :
    0 < hom.weight x := by
  obtain ⟨_, r0, ⟨_, ⟨_, _, hy⟩, hry⟩⟩ := smul_pos_of_mem_homogenize h hx
  apply congrArg hom.weight at hy
  by_contra
  simp only [← hry, map_smul, ← hy, weight_one, smul_eq_mul, mul_one] at this
  simp_all

lemma weight_nonneg_of_mem_homogenize {x : W} {P : ConvexSet R A} (h : x ∈ homogenize W P) :
    0 ≤ hom.weight x := by
  by_cases hx : x = 0
  · simp [hx]
  · exact (weight_pos_of_mem_homogenize h hx).le

variable (W) in
lemma ofPoint_mem_homogenize_iff_mem (x : A) (P : ConvexSet R A) :
    hom.ofPoint x ∈ homogenize W P ↔ x ∈ P := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simpa using mem_span_of_mem (Set.mem_image_of_mem ofPoint h)⟩
  obtain ⟨_, _, h'⟩ := smul_pos_of_mem_homogenize (Set.mem_preimage.mpr h) (ofPoint_ne_zero x)
  obtain ⟨_, ⟨_, _, hyy'⟩, hy'⟩ := Set.mem_smul_set.mp h'
  have := congrArg hom.weight hy'
  simp [← hyy', weight_one] at this
  simp only [this, Set.mem_image, one_smul, exists_eq_right] at h'
  obtain ⟨_, _, hxx'⟩ := h'
  simpa [← hom.ofPoint_injective hxx']

/-- Dehomogenizing the homogenization of a convex set yields the same set again. -/
theorem dehomogenize_homogenize (P : ConvexSet R A) :
    dehomogenize A (homogenize W P) = P := by
  ext x; exact ofPoint_mem_homogenize_iff_mem _ _ _

/-- If the entire cone save the origin are at positive weight, homogenizing the dehomogenization
of the homogenize yields the cone again. -/
theorem homogenize_dehomogenize_of_pos {C : PointedCone R W}
    (hC : ∀ x ∈ C, x ≠ 0 → 0 < hom.weight x) :
    homogenize W (dehomogenize A C) = C := by
  by_cases hbot : C = ⊥
  · simp [hbot, homogenize, dehomogenize]
  · apply SetLike.ext'
    unfold homogenize
    rw [eq_Ici_zero_smul_inter_preimage_of_pos_of_ne_bot hC zero_lt_one hbot,
      ofPoint_dehomogenize_eq_inter_ofPoint, ← hom.ofPoint_range_eq_preimage_weight_one]
    convert hull_eq_smul ?_ (C.isConvexSet.inter hom.ofPoint.range_isConvexSet)
    · obtain ⟨y, hyC, hy0⟩ := exists_mem_ne_zero_of_ne_bot hbot
      obtain ⟨_, hy'⟩ : (hom.weight y)⁻¹ • y ∈ (hom.ofPoint.range : Set W) := by
        simpa [ofPoint_range_eq_preimage_weight_one] using inv_mul_cancel₀ (hC y hyC hy0).ne.symm
      use (hom.weight y)⁻¹ • y, C.smul_mem (inv_nonneg.mpr (hC y hyC hy0).le) hyC
      simp [← hy']

end Field

end IsHomogenization

end Affine
