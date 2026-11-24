/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Geometry.Convex.ConvexSpace.Defs
public import Polyhedral.Mathlib.Data.Finsupp.Basic

/-!
# Additional definitions and lemmas about convex spaces

This file contains material destined for `Mathlib/Geometry/Convex/ConvexSpace/Defs.lean`.
-/

public section

namespace Convexity

attribute [simp] StdSimplex.nonneg

private lemma convexPairWeights_cases {R : Type*} [Semiring R] [PartialOrder R]
    (s t : R) {P : Prop} (valid : 0 ≤ s → 0 ≤ t → s + t = 1 → P)
    (invalid : ¬(0 ≤ s ∧ 0 ≤ t ∧ s + t = 1) → P) : P := by
  rcases em (0 ≤ s ∧ 0 ≤ t ∧ s + t = 1) with ⟨hs, ht, hst⟩ | h
  · exact valid hs ht hst
  · exact invalid h

namespace StdSimplex

variable {R X Y : Type*} [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]

/-- Assign weights `s` and `t` to `x` and `y` when the weights are nonnegative and sum to one.
For all other weights, put all the weight on `x`. -/
noncomputable def duple' (x y : X) (s t : R) : StdSimplex R X := by classical
  exact if h : 0 ≤ s ∧ 0 ≤ t ∧ s + t = 1 then duple x y h.1 h.2.1 h.2.2 else single x

lemma duple'_eq_duple {s t : R} (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t = 1) (x y : X) :
    duple' x y s t = duple x y hs ht hst := by
  simp [duple', hs, ht, hst]

open Classical in
@[simp] lemma weights_duple' (x y : X) (s t : R) :
    (duple' x y s t).weights =
      if 0 ≤ s ∧ 0 ≤ t ∧ s + t = 1 then Finsupp.single x s + Finsupp.single y t
      else Finsupp.single x 1 := by
  simp [duple', apply_dite weights]

/-- Split a goal about `duple' x y s t` into the `duple` and `single` cases. -/
@[elab_as_elim]
lemma duple'_cases {motive : StdSimplex R X → Prop} (x y : X) (s t : R)
    (valid : ∀ (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t = 1), motive (duple x y hs ht hst))
    (invalid : ¬(0 ≤ s ∧ 0 ≤ t ∧ s + t = 1) → motive (single x)) : motive (duple' x y s t) := by
  refine convexPairWeights_cases s t (fun hs ht hst ↦ ?_) (fun h ↦ ?_)
  · simpa only [duple'_eq_duple hs ht hst] using valid hs ht hst
  · simpa [duple', h] using invalid h

@[simp] lemma map_duple' (x y : X) (s t : R) (f : X → Y) :
    (duple' x y s t).map f = duple' (f x) (f y) s t := by
  refine convexPairWeights_cases s t (fun hs ht hst ↦ ?_) (fun h ↦ ?_)
  · simp only [duple'_eq_duple hs ht hst, map_duple]
  · simp [duple', h]

end StdSimplex

section convexCombPair'
variable {R X : Type*} [Semiring R] [PartialOrder R] [IsStrictOrderedRing R] [ConvexSpace R X]

/-- Take a convex combination of two points when both weights are nonnegative and sum to one.
Returns the first point for all other weights. -/
noncomputable def convexCombPair' (s t : R) (x y : X) : X :=
  sConvexComb (.duple' x y s t)

lemma convexCombPair'_eq_sConvexComb_duple' (s t : R) (x y : X) :
    convexCombPair' s t x y = sConvexComb (.duple' x y s t) := by rfl

lemma convexCombPair'_eq_sConvexComb {s t : R} (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t = 1)
    (x y : X) : convexCombPair' s t x y = sConvexComb (.duple x y hs ht hst) := by
  simp only [convexCombPair', StdSimplex.duple'_eq_duple hs ht hst]

lemma convexCombPair'_eq_convexCombPair {s t : R} (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t = 1)
    (x y : X) : convexCombPair' s t x y = convexCombPair s t hs ht hst x y :=
  convexCombPair'_eq_sConvexComb hs ht hst x y

/-- Use this to prove a property of `convexCombPair' s t x y`. Use this as
`refine convexCombPair'_cases s t x y ?_ ?_`. The valid branch gives the three weight proofs and
replaces the combination with `sConvexComb` of the corresponding simplex. The invalid branch
replaces the combination with `x`. -/
@[elab_as_elim]
lemma convexCombPair'_cases {motive : X → Prop} (s t : R) (x y : X)
    (valid : ∀ (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t = 1),
      motive (sConvexComb (.duple x y hs ht hst)))
    (invalid : ¬(0 ≤ s ∧ 0 ≤ t ∧ s + t = 1) → motive x) : motive (convexCombPair' s t x y) := by
  unfold convexCombPair'
  refine StdSimplex.duple'_cases x y s t valid (fun h ↦ ?_)
  simpa only [sConvexComb_single] using invalid h

@[simp] lemma convexCombPair'_zero {x y : X} : convexCombPair' (0 : R) 1 x y = y := by
  simp [convexCombPair', StdSimplex.duple', StdSimplex.duple, StdSimplex.mk_single]

@[simp] lemma convexCombPair'_one {x y : X} : convexCombPair' (1 : R) 0 x y = x := by
  simp [convexCombPair', StdSimplex.duple', StdSimplex.duple, StdSimplex.mk_single]

@[simp] lemma convexCombPair'_same (s t : R) (x : X) : convexCombPair' s t x x = x :=
  convexCombPair'_cases s t x x (fun hs ht hst ↦ convexCombPair_same hs ht hst) (fun _ ↦ rfl)

lemma convexCombPair'_symm {s t : R} (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t = 1) (x y : X) :
    convexCombPair' s t x y = convexCombPair' t s y x := by
  rw [convexCombPair'_eq_convexCombPair hs ht hst,
    convexCombPair'_eq_convexCombPair ht hs ((add_comm _ _).trans hst), convexCombPair_symm]

variable {Y : Type*} [ConvexSpace R Y]

lemma IsAffineMap.map_convexCombPair' {f : X → Y} (hf : IsAffineMap R f) (s t : R) (x y : X) :
    f (convexCombPair' s t x y) = convexCombPair' s t (f x) (f y) := by
  simp only [convexCombPair', hf.map_sConvexComb, StdSimplex.map_duple']

end convexCombPair'

section CommSemiring
variable {R X I : Type*} [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R]
  [ConvexSpace R X]

lemma iConvexComb_convexCombPair'_comm (s t : R) (w : StdSimplex R I) (e₁ e₂ : I → X) :
    w.iConvexComb (fun i ↦ convexCombPair' s t (e₁ i) (e₂ i)) =
      convexCombPair' s t (w.iConvexComb e₁) (w.iConvexComb e₂) := by
  refine convexPairWeights_cases s t (fun hs ht hst ↦ ?_) (fun h ↦ ?_)
  · simp only [convexCombPair'_eq_convexCombPair hs ht hst, iConvexComb_convexCombPair_comm]
  · simp [convexCombPair', StdSimplex.duple', h]

end CommSemiring

section iConvexComb
variable {R M I : Type*}
variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R] [ConvexSpace R M]

/-- Evaluating convex combinations is affine in the weights. -/
@[fun_prop]
lemma isAffineMap_sConvexComb :
    IsAffineMap R (sConvexComb : StdSimplex R M → M) :=
  ⟨sConvexComb_sConvexComb⟩

/-- Taking convex combinations of a fixed family of points is affine in the weights. -/
@[fun_prop]
lemma isAffineMap_iConvexComb {f : I → M} :
    IsAffineMap R (fun w : StdSimplex R I ↦ iConvexComb w f) :=
  isAffineMap_sConvexComb.comp (StdSimplex.isAffineMap_map R f)

lemma iConvexComb_duple (i j : I) (a b : R) (ha hb hab) (x : I → M) :
    iConvexComb (.duple i j ha hb hab) x = convexCombPair a b ha hb hab (x i) (x j) := by
  simp [iConvexComb, convexCombPair]

lemma iConvexComb_duple' (i j : I) (a b : R) (x : I → M) :
    iConvexComb (.duple' i j a b) x = convexCombPair' a b (x i) (x j) := by
  simp only [iConvexComb, StdSimplex.map_duple', convexCombPair'_eq_sConvexComb_duple']

end iConvexComb

-- PR #43261

section IsCancelConvexSpace

variable {R X Y : Type*} [PartialOrder R] [Semiring R] [IsStrictOrderedRing R] [ConvexSpace R X]
  [ConvexSpace R Y]

variable (R X) in
/-- A convex space is *cancellative* if a point of positive weight can be cancelled from a convex
combination, namely if two convex combinations which agree except that one puts positive weight on
`x` where the other puts it on `y` are equal, then `x = y`.

Torsion-free modules over linearly ordered scalars are cancellative,
and so are affine spaces over such modules.
See `Convexity.IsCancelConvexSpace.of_module`, `Convexity.IsCancelConvexSpace.of_addTorsor`. -/
class IsCancelConvexSpace : Prop where
  /-- A point of positive weight can be cancelled from a convex combination. -/
  eq_of_sConvexComb {a : R} (ha : 0 < a) {w : X →₀ R} {w₁ w₂ : StdSimplex R X} {x y : X}
    (hw₁ : w₁.weights = .single x a + w) (hw₂ : w₂.weights = .single y a + w)
    (hw : w₁.sConvexComb = w₂.sConvexComb) : x = y

export IsCancelConvexSpace (eq_of_sConvexComb)

section
variable [IsCancelConvexSpace R X] {a b : R} {x y z : X}

open Finsupp

/-- A point of positive weight can be cancelled from a convex combination after mapping it to a
cancellative convex space along an affine map. -/
protected lemma IsAffineMap.eq_of_sConvexComb {f : Y → X} (hf : IsAffineMap R f) {a : R}
    (ha : 0 < a) {w : Y →₀ R} {w₁ w₂ : StdSimplex R Y} {x y : Y}
    (hw₁ : w₁.weights = .single x a + w) (hw₂ : w₂.weights = .single y a + w)
    (h : w₁.sConvexComb = w₂.sConvexComb) : f x = f y :=
  eq_of_sConvexComb (w := w.mapDomain f) (w₁ := w₁.map f) (w₂ := w₂.map f) ha
    (by simp [hw₁, mapDomain_add]) (by simp [hw₂, mapDomain_add])
    (by rw [← hf.map_sConvexComb, ← hf.map_sConvexComb, h])

lemma IsCancelConvexSpace.of_injective {f : Y → X} (hf : IsAffineMap R f) (hfinj : f.Injective) :
    IsCancelConvexSpace R Y where
  eq_of_sConvexComb ha _ _ _ _ _ hw₁ hw₂ h := hfinj <| hf.eq_of_sConvexComb ha hw₁ hw₂ h

/-- A point of positive weight can be cancelled from an indexed convex combination. -/
lemma eq_of_iConvexComb {I : Type*} (w : StdSimplex R I) {i : I} (hi : 0 < w.weights i)
    {f g : I → X} (hfg : ∀ j ≠ i, f j = g j) (h : w.iConvexComb f = w.iConvexComb g) :
    f i = g i := by
  classical
  replace hfg : (w.weights.erase i).mapDomain f = (w.weights.erase i).mapDomain g := by
    congr! 1 with j hj
    simp_all
  refine eq_of_sConvexComb (w := (w.weights.erase i).mapDomain f) (w₁ := w.map f) (w₂ := w.map g)
    hi ?_ ?_ h
  · simp only [StdSimplex.weights_map]
    exact mapDomain_eq_single_add_mapDomain_erase f i
  · simp only [StdSimplex.weights_map]
    rw [mapDomain_eq_single_add_mapDomain_erase g i, hfg]

lemma convexCombPair_left_injective ⦃a b : R⦄ (ha : 0 < a) (hb : 0 ≤ b) (hab : a + b = 1) (y : X) :
    Function.Injective fun x ↦ convexCombPair a b ha.le hb hab x y := fun x₁ x₂ h ↦
  eq_of_sConvexComb (w := .single y b) (w₁ := .duple x₁ y ha.le hb hab)
    (w₂ := .duple x₂ y ha.le hb hab) ha (by simp) (by simp) h

lemma convexCombPair_right_injective (ha : 0 ≤ a) (hb : 0 < b) (hab : a + b = 1) (x : X) :
    Function.Injective fun y ↦ convexCombPair a b ha hb.le hab x y := fun y z hyz ↦
  convexCombPair_left_injective hb ha ((add_comm _ _).trans hab) x <| by
    dsimp only
    rw [convexCombPair_symm, convexCombPair_symm (x := z)]
    exact hyz

@[simp]
lemma convexCombPair_left_inj (ha : 0 < a) (hb : 0 ≤ b) (hab : a + b = 1) :
    convexCombPair a b ha.le hb hab x z = convexCombPair a b ha.le hb hab y z ↔ x = y :=
  (convexCombPair_left_injective ha hb hab z).eq_iff

@[simp]
lemma convexCombPair_right_inj (ha : 0 ≤ a) (hb : 0 < b) (hab : a + b = 1) :
    convexCombPair a b ha hb.le hab x y = convexCombPair a b ha hb.le hab x z ↔ y = z :=
  (convexCombPair_right_injective ha hb hab x).eq_iff

@[simp]
lemma convexCombPair_eq_left (ha : 0 ≤ a) (hb : 0 < b) (hab : a + b = 1) :
    convexCombPair a b ha hb.le hab x y = x ↔ y = x := by
  simpa using convexCombPair_right_inj ha hb hab (x := x) (z := x)

@[simp]
lemma convexCombPair_eq_right (ha : 0 < a) (hb : 0 ≤ b) (hab : a + b = 1) :
    convexCombPair a b ha.le hb hab x y = y ↔ x = y := by
  simpa using convexCombPair_left_inj ha hb hab (y := y) (z := y)

end

end IsCancelConvexSpace

-- end PR #43261

end Convexity
