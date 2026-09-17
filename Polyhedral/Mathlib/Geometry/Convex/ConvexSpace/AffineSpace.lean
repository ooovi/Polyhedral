/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/
module


public import Mathlib.Geometry.Convex.ConvexSpace.AffineSpace
public import Mathlib.Geometry.Convex.ConvexSpace.Module
public import Mathlib.Geometry.Convex.ConvexSpace.Prod

/-!
# Convex combinations in affine convex spaces

This file proves that indexed convex combinations in an affine convex space commute with
pointwise translation (`iConvexComb_vadd`) and pointwise difference (`iConvexComb_vsub`),
and deduces that translation (`isAffineMap_vadd`) and point subtraction (`isAffineMap_vsub`)
are affine maps on the product convex space, together with the compositional forms
`IsAffineMap.vadd` and `IsAffineMap.vsub` for use by `fun_prop`.

-/

public section

open Convexity Finset AddTorsor
open scoped Pointwise

namespace AffineMap
variable {R V₁ V₂ P₁ P₂ : Type*}
variable [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [AddCommGroup V₁] [Module R V₁] [AddTorsor V₁ P₁]
variable [AddCommGroup V₂] [Module R V₂] [AddTorsor V₂ P₂]
variable [ConvexSpace R P₁] [IsAffineConvexSpace R V₁ P₁]
variable [ConvexSpace R P₂] [IsAffineConvexSpace R V₂ P₂]
variable (f : P₁ →ᵃ[R] P₂)

-- PR #39437
lemma isAffineMap : IsAffineMap R f where
  map_sConvexComb s := by
    rw [sConvexComb_eq_affineCombination, sConvexComb_map, iConvexComb_eq_affineCombination]
    simpa only [Function.comp_id] using
      map_affineCombination (s := s.weights.support) _root_.id s.weights s.total f

@[simp] lemma map_sConvexComb (w : StdSimplex R P₁) :
    f (sConvexComb w) = sConvexComb (w.map f) := f.isAffineMap.map_sConvexComb w

lemma isConvexSet_image {s : Set P₁} (hs : IsConvexSet R s) : IsConvexSet R (f '' s) :=
  hs.image f.isAffineMap

lemma isConvexSet_range : IsConvexSet R (Set.range f) := by
  simpa using f.isConvexSet_image .univ

end AffineMap

namespace Convexity
variable {R V P I : Type*}
variable [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [AddCommGroup V] [Module R V] [AddTorsor V P]
variable [ConvexSpace R P] [IsAffineConvexSpace R V P]

lemma _root_.AffineSubspace.isConvexSet (S : AffineSubspace R P) : IsConvexSet R (S : Set P) := by
  refine .of_sConvexComb_mem fun w hw ↦ ?_
  rw [sConvexComb_eq_convexComb (V := V), AddTorsor.convexCombination, ← S.affineSpan_coe,
    ← (S : Set P).image_id]
  exact affineCombination_mem_affineSpan_image (by simpa [Finsupp.sum] using w.total) (by grind) _

variable [ConvexSpace R V] [IsModuleConvexSpace R V]

/-- A convex combination of pointwise translates splits as the convex combination of the
translations acting on the convex combination of the base points. -/
theorem iConvexComb_vadd (w : StdSimplex R I) (g : I → V) (q : I → P) :
    w.iConvexComb (fun i => g i +ᵥ q i) = w.iConvexComb g +ᵥ w.iConvexComb q := by
  obtain ⟨b⟩ : Nonempty P := inferInstance
  rw [iConvexComb_eq_affineCombination (f := fun i => g i +ᵥ q i),
    iConvexComb_eq_affineCombination (f := q), iConvexComb_eq_sum,
    Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one (h := w.total) (b := b),
    Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one (h := w.total) (b := b),
    Finset.weightedVSubOfPoint_apply, Finset.weightedVSubOfPoint_apply, Finsupp.sum]
  simp_rw [vadd_vsub_assoc, smul_add, Finset.sum_add_distrib, add_vadd]

/-- A convex combination of pointwise differences is the difference of the convex
combinations. -/
theorem iConvexComb_vsub (w : StdSimplex R I) (p q : I → P) :
    w.iConvexComb (fun i => p i -ᵥ q i) = w.iConvexComb p -ᵥ w.iConvexComb q := by
  rw [iConvexComb_eq_sum, iConvexComb_eq_affineCombination (f := p),
    iConvexComb_eq_affineCombination (f := q), Finsupp.sum,
    ← Finset.sum_smul_vsub_eq_affineCombination_vsub]

/-- Translation `(v, p) ↦ v +ᵥ p` is an affine map on the product convex space. -/
lemma isAffineMap_vadd : IsAffineMap R (fun x : V × P => x.1 +ᵥ x.2) where
  map_sConvexComb w := by
    simp only [sConvexComb_map, iConvexComb_vadd, Prod.fst_sConvexComb, Prod.snd_sConvexComb]

/-- Point subtraction `(p, q) ↦ p -ᵥ q` is an affine map on the product convex space. -/
lemma isAffineMap_vsub : IsAffineMap R (fun x : P × P => x.1 -ᵥ x.2) where
  map_sConvexComb w := by
    simp only [sConvexComb_map, iConvexComb_vsub, Prod.fst_sConvexComb, Prod.snd_sConvexComb]

/-- The pointwise translation of an affine map by an affine map is affine.

This is the compositional form of `isAffineMap_vadd` for use by `fun_prop`. -/
@[fun_prop]
lemma IsAffineMap.vadd {X : Type*} [ConvexSpace R X] {f : X → V} {g : X → P}
    (hf : IsAffineMap R f) (hg : IsAffineMap R g) : IsAffineMap R fun x => f x +ᵥ g x :=
  isAffineMap_vadd.comp (hf.prodMk hg)

/-- The pointwise difference of two affine maps is affine.

This is the compositional form of `isAffineMap_vsub` for use by `fun_prop`. -/
@[fun_prop]
lemma IsAffineMap.vsub {X : Type*} [ConvexSpace R X] {f g : X → P}
    (hf : IsAffineMap R f) (hg : IsAffineMap R g) : IsAffineMap R fun x => f x -ᵥ g x :=
  isAffineMap_vsub.comp (hf.prodMk hg)

protected lemma IsConvexSet.vadd {K₁ : Set V} {K₂ : Set P} (hK₁ : IsConvexSet R K₁)
    (hK₂ : IsConvexSet R K₂) : IsConvexSet R (K₁ +ᵥ K₂) := by
  rw [← Set.vadd_image_prod]; exact (hK₁.prod hK₂).image isAffineMap_vadd

lemma IsConvexSet.vadd_set (v : V) {K : Set P} (hK : IsConvexSet R K) : IsConvexSet R (v +ᵥ K) := by
  rw [← Set.singleton_vadd]; exact .vadd .singleton hK

/- TODO: there should also be a version `(K : ConvexSet R V) +ᵥ (p : A)`, but there is not even
a version for sets yet. -/

protected lemma IsConvexSet.vsub {K₁ K₂ : Set P} (hK₁ : IsConvexSet R K₁) (hK₂ : IsConvexSet R K₂) :
    IsConvexSet R (K₁ -ᵥ K₂) := by
  rw [← Set.image_vsub_prod]; exact (hK₁.prod hK₂).image isAffineMap_vsub

end Convexity
