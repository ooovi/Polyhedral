/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/
module

public import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Finite.Face.Basic
public import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.Homogenization
public import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.KreinMilman

/-! In this file we prove the Krein-Milman theorem for FG cones: every finitely generated
cone is spanned by its rays, that is, by the finite set of its 1-dimensional faces.

The theorem is derived from the Krein-Milman theorem for polytopes
(`IsPolytope.krein_milman`): a salient FG cone admits a linear functional that is positive on
all of its nonzero elements, the slice of the cone at weight one is a polytope, and the cone
is the homogenization of that slice, so its rays are the homogenizations of the vertices of
the slice. -/

@[expose] public section

namespace PointedCone

variable {R M : Type*}

section Field

variable [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable [AddCommGroup M] [Module R M]

variable {C : PointedCone R M}

open Convexity ConvexSet Affine Affine.IsHomogenization

/-- Krein-Milman theorem: every finitely generated cone is spanned by its rays, that is,
by the finite set of its 1-dimensional faces. -/
lemma FG.krein_milman (hfg : C.FG) (hsal : C.Salient) :
    ∃ s : Finset M, hull R s = C ∧ ∀ x ∈ s, (R ∙₊ x).IsFaceOf C := by
  classical
  by_cases hbot : C = ⊥
  · exact ⟨∅, by simp [hbot]⟩
  -- a linear functional that is positive on all nonzero elements of `C`
  obtain ⟨g, hg, hgker⟩ := IsExposedFaceOf.lineal hfg
  have hker : C ⊓ g.ker = ⊥ := by
    rw [← hgker]
    ext y
    simp [salient_iff_lineal_bot.mp hsal]
  have hgC : C ≤ g.positive := by
    intro y hy
    rw [LinearMap.mem_positive']
    refine ⟨hg hy, fun hgy ↦ ?_⟩
    have : y ∈ C ⊓ g.ker := ⟨hy, hgy⟩
    rw [hker] at this
    simpa using this
  -- the weight-one slice of `C` is nonempty
  obtain ⟨y, hyC, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  have hgy : 0 < g y := by
    obtain ⟨h1, h2⟩ := LinearMap.mem_positive'.mp (hgC hyC)
    exact lt_of_le_of_ne h1 fun h => hy0 (h2 h.symm)
  -- choose the homogenization whose affine space is the weight-one plane
  let weightOnePlane := (affineSpan R {1}).comap g.toAffineMap
  have : Nonempty weightOnePlane :=
    ⟨⟨(g y)⁻¹ • y, by simp [inv_mul_cancel₀ hgy.ne', weightOnePlane]⟩⟩
  let ℋ : IsHomogenization R weightOnePlane M := ofWeightOne g
  -- view `C` as the homogenization of its weight-one slice
  let : ConvexSpace R M := ConvexSpace.ofModule
  let := ConvexSpace.ofAddTorsor (R := R) (P := (affineSpan R {1}).comap g.toAffineMap)
  have hCP : homogenize ℋ (dehomogenize ℋ C) = C :=
    homogenize_dehomogenize_of_le_positive ((ofWeightOne_weight g).symm ▸ hgC)
  -- the slice is a polytope; apply the Krein-Milman theorem for polytopes
  have hP : IsPolytope R (dehomogenize ℋ C : Set weightOnePlane) := by
    rw [IsPolytope.iff_homogenize_fg (W := M), hCP]
    exact hfg
  obtain ⟨s, hs, hface⟩ := IsPolytope.krein_milman hP
  refine ⟨s.image ℋ.ofPoint, ?_, ?_⟩
  · rw [Finset.coe_image, hull_image_ofPoint_eq_homogenize_convexHull, hs, hCP]
  · intro x hx
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
    have h := homogenize_isFaceOf ℋ (hface q hq)
    rwa [homogenize_singleton, hCP] at h

end Field

end PointedCone
