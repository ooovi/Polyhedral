/-
Copyright (c) 2026 Olivia Röhrig, Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter, Olivia Röhrig
-/
module

public import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Basic
public import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Module

import Mathlib.Geometry.Convex.ConvexSpace.AffineSpace
import Mathlib.Geometry.Convex.Set
import Polyhedral.Mathlib.LinearAlgebra.AffineSpace.AffineMap

/-!
# Affine maps and convexity

This file proves results about affine maps and convexity.

It also shows that the bundled affine maps between two convex spaces `X` and `Y` themselves form a
convex space under pointwise convex combinations, and that this structure is the one coming from
the module structure when `Y := N` is a module.

## Main declarations

* `Convexity.isAffineMap_iConvexComb`: A pointwise convex combination of affine maps is affine.
* `Convexity.ConvexSpace.AffineMap.instConvexSpace`: The affine maps between two convex spaces form
  a convex space.
* `Convexity.ConvexSpace.AffineMap.instIsModuleConvexSpace`: The convex space structure on the
  affine maps into a module is given by weighted sums.

## TODO

Show that `Convexity.ConvexSpace.AffineMap.comp` is affine in each variable.
-/

public section

open Affine Convexity

variable {R V V₁ V₂ P P₁ P₂ I : Type*}

variable [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [AddCommGroup V] [Module R V] [AddTorsor V P]
variable [AddCommGroup V₁] [Module R V₁] [AddTorsor V₁ P₁]
variable [AddCommGroup V₂] [Module R V₂] [AddTorsor V₂ P₂]

variable [ConvexSpace R P] [IsAffineConvexSpace R V P]
variable [ConvexSpace R P₁] [IsAffineConvexSpace R V₁ P₁]
variable [ConvexSpace R P₂] [IsAffineConvexSpace R V₂ P₂]

open Convexity Finset AddTorsor

namespace AffineMap

variable (f : P₁ →ᵃ[R] P₂)

-- PR #39437
lemma isAffineMap : IsAffineMap R f where
  map_sConvexComb s := by
    rw [sConvexComb_eq_affineCombination, sConvexComb_map, iConvexComb_eq_affineCombination]
    simpa only [Function.comp_id] using
      map_affineCombination (s := s.weights.support) _root_.id s.weights s.total f

@[simp] lemma map_sConvexComb (w : StdSimplex R P₁) :
    f (sConvexComb w) = sConvexComb (w.map f) := f.isAffineMap.map_sConvexComb w

lemma image_isConvexSet {s : Set P₁} (hs : IsConvexSet R s) : IsConvexSet R (f '' s) :=
  hs.image f.isAffineMap

lemma range_isConvexSet : IsConvexSet R (Set.range f) := by
  rw [← Set.image_univ]
  exact f.image_isConvexSet .univ

end AffineMap

namespace Convexity

/-! ### The convex space of affine maps between convex spaces -/

section Pointwise
variable {R X Y I : Type*} [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R]
  [ConvexSpace R X] [ConvexSpace R Y]

/-- A pointwise convex combination of affine maps is affine.

This genuinely needs the scalars to be commutative, since the proof exchanges the weights of the
convex combination of maps with the weights of the convex combination of points. -/
lemma isAffineMap_iConvexComb {f : I → X → Y} (hf : ∀ i, IsAffineMap R (f i))
    (w : StdSimplex R I) : IsAffineMap R fun x ↦ w.iConvexComb (f · x) where
  map_sConvexComb s := by
    have hfs (i : I) : f i s.sConvexComb = s.iConvexComb (f i) := (hf i).map_sConvexComb s
    simp only [hfs, sConvexComb_map]
    exact iConvexComb_comm ..

namespace ConvexSpace.AffineMap

/-- Affine maps between two convex spaces form a convex space under pointwise convex
combinations. -/
noncomputable instance instConvexSpace : ConvexSpace R (ConvexSpace.AffineMap R X Y) := .mk
  (fun w ↦ ⟨fun x ↦ w.iConvexComb (· x), isAffineMap_iConvexComb (fun f ↦ f.isAffineMap) w⟩)
  (fun f ↦ by ext x; exact iConvexComb_single ..)
  (fun W ↦ by
    ext x
    exact (iConvexComb_map W _ _).trans <|
      (iConvexComb_assoc W (f := fun w ↦ w) (g := (· x))).trans <|
        congrArg (·.iConvexComb (· x)) (iConvexComb_id' W))

lemma coe_sConvexComb (w : StdSimplex R (ConvexSpace.AffineMap R X Y)) :
    ⇑w.sConvexComb = fun x ↦ w.iConvexComb (· x) := rfl

@[simp]
lemma sConvexComb_apply (w : StdSimplex R (ConvexSpace.AffineMap R X Y)) (x : X) :
    w.sConvexComb x = w.iConvexComb (· x) := rfl

/-- Evaluation at a point is affine in the affine map. -/
@[fun_prop]
lemma isAffineMap_apply (x : X) : IsAffineMap R fun f : ConvexSpace.AffineMap R X Y ↦ f x where
  map_sConvexComb _ := sConvexComb_apply ..

@[simp]
lemma iConvexComb_apply (w : StdSimplex R I) (f : I → ConvexSpace.AffineMap R X Y) (x : X) :
    w.iConvexComb f x = w.iConvexComb fun i ↦ f i x := (isAffineMap_apply x).map_iConvexComb ..

@[simp]
lemma convexCombPair_apply (a b : R) (ha hb hab) (f g : ConvexSpace.AffineMap R X Y) (x : X) :
    convexCombPair a b ha hb hab f g x = convexCombPair a b ha hb hab (f x) (g x) :=
  (isAffineMap_apply x).map_convexCombPair ..

end ConvexSpace.AffineMap
end Pointwise

/-! ### Compatibility with the module structure -/

section Module
variable {R X N : Type*} [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R]
  [ConvexSpace R X] [AddCommMonoid N] [Module R N] [ConvexSpace R N] [IsModuleConvexSpace R N]

/-- The pointwise convex space structure on the affine maps into a module is the one coming from
the module structure. -/
instance ConvexSpace.AffineMap.instIsModuleConvexSpace :
    IsModuleConvexSpace R (ConvexSpace.AffineMap R X N) where
  sConvexComb_eq_sum w := by ext x; simp [Finsupp.sum]

end Module
end Convexity
