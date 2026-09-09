/-
Copyright (c) 2026 Olivia Röhrig, Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter, Olivia Röhrig
-/
module

public import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Convexity
public import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Lineal
public import Polyhedral.Mathlib.LinearAlgebra.AffineSpace.Homogenization.Basic

import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.AffineMap
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Lattice

/-! This file defines homogenization of convex sets in affine spaces. -/

@[expose] public section

open Convexity Pointwise Set PointedCone Submodule

namespace Convexity.ConvexSet

variable {R V A W : Type*}

section Ring

open Convexity

variable [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [AddCommGroup V] [Module R V]
variable [AddCommGroup W] [Module R W]
variable [AddTorsor V A] [ConvexSpace R A]

variable (ℋ : Affine.IsHomogenization R A W)

/-- The homogenization cone of a convex set in an affine space. -/
def homogenize (P : ConvexSet R A) : PointedCone R W := hull R (ℋ.ofPoint '' P)

lemma homogenize_mono {K₁ K₂ : ConvexSet R A} (h : K₁ ≤ K₂) :
    K₁.homogenize ℋ ≤ K₂.homogenize ℋ := Submodule.span_mono <| Set.image_mono h

lemma homogenize_monotone : Monotone (homogenize ℋ : ConvexSet R A → PointedCone R W) :=
  fun _ _ => homogenize_mono _

/-- Homogenization from convex set to convex cones as an order homomorphism. -/
def homogenizeOrderHom : ConvexSet R A →o PointedCone R W where
  toFun := homogenize ℋ
  monotone' := homogenize_monotone _

@[simp]
lemma homogenize_bot : homogenize ℋ (⊥ : ConvexSet R A) = ⊥ := by
  simp [homogenize, Bot.bot]

@[simp]
lemma homogenize_eq_bot_iff (P : ConvexSet R A) : homogenize ℋ P = ⊥ ↔ P = ⊥ := by
  refine ⟨fun h ↦ ?_, by simp +contextual [-SetLike.bot_eq_empty]⟩
  ext x
  simp only [homogenize, span_eq_bot, mem_image, SetLike.mem_coe, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂] at h
  simpa using fun hx ↦ ℋ.ofPoint_ne_zero _ (h x hx)

/- NOTE: `homogenize_top`, stating `homogenize ℋ (⊤ : ConvexSet R A) = ℋ.weight.positive`,
only holds over linearly ordered fields and is proven in the `Field` section below. Over a
general ordered ring it fails: for `R = ℤ[ε]` with `ε` a positive infinitesimal, the point
`(1, ε)` lies in `weight.positive` but not in the cone hull of the weight-one hyperplane, since
all nonnegative coefficients bounded by `ε` lie in the ideal `(ε)`. -/

lemma homogenize_le_weight_positive (K : ConvexSet R A) :
    homogenize ℋ K ≤ ℋ.weight.positive := by
  exact LinearMap.hull_le_positive_of_subset_preimage_singleton one_pos fun _ ↦ by
    rintro ⟨x, -, rfl⟩
    simp [ℋ.weight_one]

variable {hom} in
lemma weight_pos_of_mem_homogenize {x} {P : ConvexSet R A} (h : x ∈ homogenize ℋ P) (hx : x ≠ 0) :
    0 < ℋ.weight x := homogenize_le_weight_positive _ P h hx

variable {hom} in
lemma weight_nonneg_of_mem_homogenize {x : W} {P : ConvexSet R A} (h : x ∈ homogenize ℋ P) :
    0 ≤ ℋ.weight x :=
  (LinearMap.mem_positive'.mp (homogenize_le_weight_positive _ P h)).1

lemma homogenize_salient (K : ConvexSet R A) : PointedCone.Salient (homogenize ℋ K) :=
  Salient.of_le_salient ℋ.weight.positive_salient (homogenize_le_weight_positive _ K)

variable {hom} in
theorem homogenize_fg_ofPoint_range {C : ConvexSet R A} (h : (homogenize ℋ C).FG) :
    ∃ g : Finset W, PointedCone.hull R g = homogenize ℋ C ∧
      (g : Set W) ⊆ Set.range ℋ.ofPoint := by
  obtain ⟨g, hg⟩ := h
  -- express each generator as a positive combo of stuff in the embedding of C
  have gsum {x} (hx : x ∈ g) := mem_hull_set.mp (hg ▸ (Submodule.mem_span_of_mem hx))
  classical
  -- collect all said stuff and use as the new generators
  let g' := g.attach.biUnion (fun x => (Classical.choose (gsum x.2)).support)
  use g'
  have g'sub : (g' : Set W) ⊆ ℋ.ofPoint '' C := by
    simpa [g'] using fun _ b ↦ (Classical.choose_spec (gsum b)).1
  have gsubhull : (g : Set W) ⊆ hull R (g' : Set W) := by
    intro x hx
    obtain ⟨_, hnn, hsum⟩ := Classical.choose_spec (gsum hx)
    refine hsum ▸ mem_hull_set.mpr ⟨Classical.choose (gsum hx), ?_, hnn, rfl⟩
    simpa using Finset.subset_biUnion_of_mem
      (fun p ↦ (Classical.choose (gsum p.2)).support) (Finset.mem_attach g ⟨x, hx⟩)
  refine ⟨le_antisymm (hull_mono g'sub) ?_, g'sub.trans (by simp)⟩
  simpa [hg] using hull_mono (R := R) gsubhull

section Module

variable [ConvexSpace R W] [IsModuleConvexSpace R W] [IsAffineConvexSpace R V A]

def dehomogenize (C : PointedCone R W) : ConvexSet R A :=
  ⟨_, C.isConvexSet.preimage ℋ.ofPoint.isAffineMap⟩

alias _root_.PointedCone.dehomogenize := dehomogenize

@[simp]
lemma dehomogenize_bot : dehomogenize ℋ (⊥ : PointedCone R W) = ⊥ := by
  ext
  simp [dehomogenize, Affine.IsHomogenization.ofPoint_ne_zero]

@[simp]
lemma dehomogenize_top : dehomogenize ℋ (⊤ : PointedCone R W) = ⊤ := by
  ext
  simp [dehomogenize, SetLike.mem_coe.mp]

@[simp]
lemma dehomogenize_weight_positive : dehomogenize ℋ ℋ.weight.positive = ⊤ :=
  SetLike.eq_top_of_forall fun _ ↦ LinearMap.mem_positive'.mpr (by simp [ℋ.weight_one])

lemma dehomogenize_mono {C₁ C₂ : PointedCone R W} (h : C₁ ≤ C₂) :
    dehomogenize ℋ C₁ ≤ dehomogenize ℋ C₂ := Set.preimage_mono <| Set.preimage_mono h
    -- Q: why Set.preimage_mono twice?

lemma dehomogenize_monotone : Monotone (dehomogenize ℋ : PointedCone R W → ConvexSet R A) :=
  fun _ _ => dehomogenize_mono _

-- This lemma is just `Set.image_preimage_eq_inter_range` in disguise. It is likely not needed.
lemma ofPoint_dehomogenize_eq_inter_ofPoint (C : PointedCone R W) :
    ℋ.ofPoint '' dehomogenize ℋ C = (C : Set W) ∩ ℋ.ofPoint.range := by
  ext x
  simp only [Set.mem_image, SetLike.mem_coe, Set.mem_inter_iff, AffineMap.mem_range]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨hy, by use y⟩
  · rintro ⟨hxC, y, rfl⟩
    use y
    simpa

/-- The preimage of the conic hull of a set in the homogenization plane is the convex hull of the
preimage of the set. -/
theorem hull_image_ofPoint_eq_homogenize_convexHull {s : Set A} :
    hull R (ℋ.ofPoint '' s) = homogenize ℋ (ConvexSet.convexHull R s) := by
  simp [homogenize, ConvexSet.convexHull, ℋ.ofPoint.isAffineMap.image_convexHull]

end Module

end Ring

section Field

variable [Field R] [LinearOrder R] [IsOrderedRing R]
variable [AddCommGroup V] [Module R V]
variable [AddCommGroup W] [Module R W]
variable [AddTorsor V A] [ConvexSpace R A]

variable (ℋ : Affine.IsHomogenization R A W)

/-- The homogenization of the full affine space is the positive cone of the weight functional. -/
lemma homogenize_top : homogenize ℋ (⊤ : ConvexSet R A) = ℋ.weight.positive := by
  rw [homogenize, LinearMap.positive_eq_hull_preimage_singleton ℋ.weight one_pos,
    ← ℋ.ofPoint_range_eq_preimage_weight_one]
  congr! with x
  simp

variable [ConvexSpace R W] [IsModuleConvexSpace R W] [IsAffineConvexSpace R V A]

variable {ℋ} in
lemma smul_pos_of_mem_homogenize {P : ConvexSet R A} {x} (h : x ∈ homogenize ℋ P) (hx : x ≠ 0) :
    x ∈ Set.Ioi (0 : R) • ℋ.ofPoint '' (P : Set A) :=
  (mem_hull_iff_mem_pos_smul_of_convex_nonzero
    (P.isConvexSet.image ℋ.ofPoint.isAffineMap) hx).mp h

-- TODO: This lemma should be proven for general sets (homogenizing to SubMulAction) and then
--  applied here as a special case.
lemma ofPoint_mem_homogenize_iff_mem (x : A) (P : ConvexSet R A) :
    ℋ.ofPoint x ∈ homogenize ℋ P ↔ x ∈ P := by
  refine ⟨fun h ↦ ?_, fun h ↦ mem_span_of_mem (Set.mem_image_of_mem ℋ.ofPoint h)⟩
  obtain ⟨_, _, h'⟩ := smul_pos_of_mem_homogenize (Set.mem_preimage.mpr h) (ℋ.ofPoint_ne_zero x)
  obtain ⟨_, ⟨_, _, hyy'⟩, hy'⟩ := Set.mem_smul_set.mp h'
  have := congrArg ℋ.weight hy'
  simp [← hyy', ℋ.weight_one] at this
  simp only [this, Set.mem_image, one_smul, exists_eq_right] at h'
  obtain ⟨_, _, hxx'⟩ := h'
  simpa [← ℋ.ofPoint_injective hxx']

/-- Dehomogenizing the homogenization of a convex set yields the same set again. -/
@[simp] theorem dehomogenize_homogenize (P : ConvexSet R A) :
    dehomogenize ℋ (homogenize ℋ P) = P := by
  ext x; exact ofPoint_mem_homogenize_iff_mem _ _ _

lemma homogenize_injective : Function.Injective (homogenize ℋ) := by
  intro P Q h
  have hh := congr_arg (ConvexSet.dehomogenize ℋ) h
  simp [dehomogenize_homogenize] at hh
  assumption

variable {ℋ} in
/-- If the entire cone save the origin are at positive weight, homogenizing the dehomogenization
of the homogenize yields the cone again. -/
theorem homogenize_dehomogenize_of_le_positive {C : PointedCone R W}
    (hC : C ≤ ℋ.weight.positive) : homogenize ℋ (dehomogenize ℋ C) = C := by
  by_cases hbot : C = ⊥
  · simp [hbot, homogenize, dehomogenize]
  · apply SetLike.ext'
    unfold homogenize
    rw [eq_Ici_zero_smul_inter_preimage_of_pos_of_ne_bot hC zero_lt_one hbot,
      ofPoint_dehomogenize_eq_inter_ofPoint, ← ℋ.ofPoint_range_eq_preimage_weight_one]
    apply hull_eq_smul
    · obtain ⟨y, hyC, hy0⟩ := exists_mem_ne_zero_of_ne_bot hbot
      let y' := (ℋ.weight y)⁻¹ • y
      have hy'C : y' ∈ C :=
        C.smul_mem (inv_nonneg.mpr (@hC y hyC hy0).le) hyC
      have hy' : y' ∈ Set.range ℋ.ofPoint := by
        simpa [y', ℋ.ofPoint_range_eq_preimage_weight_one]
          using inv_mul_cancel₀ (@hC y hyC hy0).ne.symm
      exact ⟨y', hy'C, hy'⟩
    · exact C.isConvexSet.inter ℋ.ofPoint.range_isConvexSet

lemma homogenize_mono_iff {K₁ K₂ : ConvexSet R A} :
    K₁.homogenize ℋ ≤ K₂.homogenize ℋ ↔ K₁ ≤ K₂ where
  mp h := by simpa using dehomogenize_mono ℋ h
  mpr := homogenize_mono _

-- Issue #66
/-- The lattice of convex sets is isomorphic to the lattice of convex sub-cones of the
positive cone. -/
def homogenizeOrderEquiv : ConvexSet R A ≃o Set.Iic ℋ.weight.positive where
  toFun K := ⟨_, K.homogenize_le_weight_positive _⟩
  invFun C := dehomogenize ℋ C.1
  left_inv K := dehomogenize_homogenize _ K
  right_inv C := by dsimp; congr; exact homogenize_dehomogenize_of_le_positive C.2
  map_rel_iff' := homogenize_mono_iff _

end Field

end Convexity.ConvexSet
