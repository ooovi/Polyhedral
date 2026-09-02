/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Order
public import Mathlib.Geometry.Convex.Set

import Mathlib.Data.Fintype.Order

/-!
# Convex and concave functions

This file defines convex and concave functions from a convex space to an ordered convex space.

## Main declarations

* `Convexity.IsConvexFunOn`: `f` is convex on `s` if its epigraph over `s` is a convex set.
* `Convexity.IsConcaveFunOn`: `f` is concave on `s` if its hypograph over `s` is a convex set.
* `Convexity.IsConvexFunOn.map_iConvexComb_le`: **Jensen's inequality**, in its finitary form.
* `Convexity.IsConvexFunOn.of_map_convexCombPair_le`: Over a field, binary Jensen implies
  convexity, hence finitary Jensen.

## Implementation notes

To allow full generality on the coefficients, we define convexity of `f` on `s` through convexity
of its epigraph rather than through binary combinations as is customary. Over a field the two
agree, see `Convexity.IsConvexFunOn.of_map_convexCombPair_le`.

Since their body are an implementation detail, the predicates `IsConvexFunOn` and `IsConcaveFunOn`
are unexposed.
-/

open Finsupp Set

public section

namespace Convexity
variable {I R K X Y : Type*}

section Semiring
variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R] [ConvexSpace R X] [ConvexSpace R Y]
  [PartialOrder Y] {w : StdSimplex R X} {s t : Set X} {f : X → Y} {x y : X}

variable (R s f) in
/-- A function `f : X → Y` from a convex space to an ordered convex space is convex on a set `s`
if its epigraph `{(x, y) : X × Y | x ∈ s ∧ f x ≤ y}` is a convex set.

When the scalars form a field, this is equivalent to the definition in terms of binary combinations.
See `IsConvexFunOn.of_map_convexCombPair_le`.

Under mild assumptions, convexity of the function `f` implies convexity of the set `s`.
See `IsConvexFunOn.isConvexSet`. -/
@[to_dual IsConcaveFunOn
/-- A function `f : X → Y` from a convex space to an ordered convex space is concave on a set `s`
if its hypograph `{(x, y) : X × Y | x ∈ s ∧ y ≤ f x}` is a convex set.

When the scalars form a field, this is equivalent to the definition in terms of binary combinations.
See `IsConcaveFunOn.of_le_map_convexCombPair`.

Under mild assumptions, concavity of the function `f` implies convexity of the set `s`.
See `IsConcaveFunOn.isConvexSet`. -/]
def IsConvexFunOn : Prop := IsConvexSet R {(x, y) : X × Y | x ∈ s ∧ f x ≤ y}

@[to_dual]
lemma IsConvexFunOn.isConvexSet_epigraph (hf : IsConvexFunOn R s f) :
    IsConvexSet R {(x, y) : X × Y | x ∈ s ∧ f x ≤ y} := hf

@[to_dual]
lemma IsConvexFunOn.of_isConvexSet_epigraph
    (hf : IsConvexSet R {(x, y) : X × Y | x ∈ s ∧ f x ≤ y}) : IsConvexFunOn R s f := hf

@[to_dual]
lemma IsConvexFunOn.isConvexSet (hf : IsConvexFunOn R s f) : IsConvexSet R s := by
  classical
  refine .of_sConvexComb_mem fun w hw ↦ ?_
  have : ↑(w.map fun x ↦ (x, f x)).weights.support ⊆ {(x, y) : X × Y | x ∈ s ∧ f x ≤ y} := by
    grw [StdSimplex.weights_map, mapDomain_support]; simpa
  simpa [Function.comp_def] using (hf.isConvexSet_epigraph.sConvexComb_mem this).1

@[to_dual le_map_sConvexComb]
lemma IsConvexFunOn.map_sConvexComb_le (hf : IsConvexFunOn R s f) {w : StdSimplex R X}
    (hw : ↑w.weights.support ⊆ s) :
    f w.sConvexComb ≤ w.iConvexComb f := by
  classical
  have : ↑(w.map fun x ↦ (x, f x)).weights.support ⊆ {(x, y) : X × Y | x ∈ s ∧ f x ≤ y} := by
    grw [StdSimplex.weights_map, mapDomain_support]; simpa
  simpa [Function.comp_def] using (hf.isConvexSet_epigraph.sConvexComb_mem this).2

@[to_dual le_map_iConvexComb]
lemma IsConvexFunOn.map_iConvexComb_le (hf : IsConvexFunOn R s f) {w : StdSimplex R I} {x : I → X}
    (hx : ∀ i, w.weights i ≠ 0 → x i ∈ s) :
    f (w.iConvexComb x) ≤ w.iConvexComb (fun i ↦ f (x i)) := by
  classical
  grw [iConvexComb, hf.map_sConvexComb_le, iConvexComb_map]
  grw [StdSimplex.weights_map, mapDomain_support]
  simpa [Set.subset_def]

@[to_dual (dont_translate := R) le_map_convexCombPair]
lemma IsConvexFunOn.map_convexCombPair_le (hf : IsConvexFunOn R s f) (hx : x ∈ s) (hy : y ∈ s)
    {a b : R} {ha hb hab} :
    f (convexCombPair a b ha hb hab x y) ≤ convexCombPair a b ha hb hab (f x) (f y) := by
  classical
  grw [convexCombPair, hf.map_sConvexComb_le, iConvexComb_duple]
  grw [StdSimplex.weights_duple, support_add, support_single_subset, support_single_subset]
  simp [Set.subset_def, *]

@[to_dual (attr := simp)]
protected lemma IsConvexFunOn.empty : IsConvexFunOn R (∅ : Set X) f := by simp [IsConvexFunOn]

@[to_dual]
protected lemma IsConvexFunOn.inter (hs : IsConvexFunOn R s f) (ht : IsConvexFunOn R t f) :
    IsConvexFunOn R (s ∩ t) f := by
  refine .of_isConvexSet_epigraph ?_
  have : {(x, y) : X × Y | x ∈ s ∩ t ∧ f x ≤ y}
      = {(x, y) : X × Y | x ∈ s ∧ f x ≤ y} ∩ {(x, y) : X × Y | x ∈ t ∧ f x ≤ y} := by
    ext ⟨x, y⟩; simp; tauto
  rw [this]
  exact hs.isConvexSet_epigraph.inter ht.isConvexSet_epigraph

/-- Note the nonemptiness assumption: `⋂₀ ∅ = univ`, on which `f` need not be convex. -/
@[to_dual]
protected lemma IsConvexFunOn.sInter {S : Set (Set X)} (hS₀ : S.Nonempty)
    (hS : ∀ s ∈ S, IsConvexFunOn R s f) : IsConvexFunOn R (⋂₀ S) f := by
  refine .of_isConvexSet_epigraph ?_
  have : {(x, y) : X × Y | x ∈ ⋂₀ S ∧ f x ≤ y}
      = ⋂ s ∈ S, {(x, y) : X × Y | x ∈ s ∧ f x ≤ y} := by
    obtain ⟨s₀, hs₀⟩ := hS₀
    ext ⟨x, y⟩
    simp only [mem_ofPred_eq, mem_sInter, mem_iInter]
    exact ⟨fun h s hs ↦ ⟨h.1 s hs, h.2⟩, fun h ↦ ⟨fun s hs ↦ (h s hs).1, (h s₀ hs₀).2⟩⟩
  rw [this]
  exact .iInter₂ fun s hs ↦ (hS s hs).isConvexSet_epigraph

/-- Note the nonemptiness assumption: `⋂ i : Empty, s i = univ`, on which `f` need not be
convex. -/
@[to_dual]
protected lemma IsConvexFunOn.iInter {ι : Sort*} [Nonempty ι] {s : ι → Set X}
    (hs : ∀ i, IsConvexFunOn R (s i) f) : IsConvexFunOn R (⋂ i, s i) f := by
  refine .of_isConvexSet_epigraph ?_
  have : {(x, y) : X × Y | x ∈ ⋂ i, s i ∧ f x ≤ y}
      = ⋂ i, {(x, y) : X × Y | x ∈ s i ∧ f x ≤ y} := by
    ext ⟨x, y⟩
    simp only [mem_ofPred_eq, mem_iInter]
    exact ⟨fun h i ↦ ⟨h.1 i, h.2⟩,
      fun h ↦ ⟨fun i ↦ (h i).1, (h (Classical.arbitrary ι)).2⟩⟩
  rw [this]
  exact .iInter fun i ↦ (hs i).isConvexSet_epigraph

@[to_dual]
lemma IsConvexFunOn.iInter₂ {ι : Sort*} {κ : ι → Sort*} [Nonempty ι] [∀ i, Nonempty (κ i)]
    {s : ∀ i, κ i → Set X} (h : ∀ i j, IsConvexFunOn R (s i j) f) :
    IsConvexFunOn R (⋂ (i) (j), s i j) f :=
  .iInter fun i ↦ .iInter <| h i

@[to_dual]
protected lemma IsConvexFunOn.sUnion {S : Set (Set X)} (hS : DirectedOn (· ⊆ ·) S)
    (hS' : ∀ s ∈ S, IsConvexFunOn R s f) : IsConvexFunOn R (⋃₀ S) f := by
  refine .of_isConvexSet_epigraph ?_
  have : {(x, y) : X × Y | x ∈ ⋃₀ S ∧ f x ≤ y}
      = ⋃₀ ((fun s ↦ {(x, y) : X × Y | x ∈ s ∧ f x ≤ y}) '' S) := by
    rw [sUnion_image]
    ext ⟨x, y⟩
    simp only [mem_ofPred_eq, mem_sUnion, mem_iUnion]
    tauto
  rw [this]
  refine .sUnion ?_ ?_
  · rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
    obtain ⟨u, hu, hsu, htu⟩ := hS s hs t ht
    exact ⟨_, mem_image_of_mem _ hu, fun p hp ↦ ⟨hsu hp.1, hp.2⟩, fun p hp ↦ ⟨htu hp.1, hp.2⟩⟩
  · rintro _ ⟨s, hs, rfl⟩
    exact (hS' s hs).isConvexSet_epigraph

@[to_dual]
protected lemma IsConvexFunOn.iUnion {ι : Sort*} {s : ι → Set X} (hs : Directed (· ⊆ ·) s)
    (hs' : ∀ i, IsConvexFunOn R (s i) f) : IsConvexFunOn R (⋃ i, s i) f :=
  .sUnion hs.directedOn_range <| by simpa

end Semiring

section IsOrderedConvexSpace
variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R] [ConvexSpace R X] [ConvexSpace R Y]
  [LinearOrder Y] [IsOrderedConvexSpace R Y] {s : Set X} {f : X → Y} {x : X}

/-- Jensen's inequality characterises convexity of a function. -/
lemma IsConvexFunOn.of_map_sConvexComb_le (hs : IsConvexSet R s)
    (hf : ∀ w : StdSimplex R X, ↑w.weights.support ⊆ s → f w.sConvexComb ≤ w.iConvexComb f) :
    IsConvexFunOn R s f := by
  classical
  refine .of_sConvexComb_mem fun w hw ↦ ?_
  have hws : ↑(w.map Prod.fst).weights.support ⊆ s := by
    grw [StdSimplex.weights_map, mapDomain_support]
    simp only [Finset.coe_image, image_subset_iff]
    exact fun x hx ↦ (hw hx).1
  refine ⟨hs.sConvexComb_mem hws, ?_⟩
  calc f (w.map Prod.fst).sConvexComb
      ≤ (w.map Prod.fst).iConvexComb f := hf _ hws
    _ = w.iConvexComb fun p ↦ f p.1 := iConvexComb_map ..
    -- The two functions agree on the support of `w`, where `f p.1 ≤ p.2` by assumption.
    _ = w.iConvexComb fun p ↦ min (f p.1) p.2 :=
        iConvexComb_congr fun p hp ↦ (min_eq_left (hw <| by simpa using hp).2).symm
    _ ≤ w.iConvexComb Prod.snd := iConvexComb_le_iConvexComb fun p ↦ min_le_right ..

/-- **Jensen's inequality** characterises convexity of a function: `f` is convex on `s` iff `s` is
convex and `f` of a convex combination of points of `s` is at most the corresponding convex
combination of the values of `f`. -/
lemma isConvexFunOn_iff : IsConvexFunOn R s f ↔ IsConvexSet R s ∧
    ∀ w : StdSimplex R X, ↑w.weights.support ⊆ s → f w.sConvexComb ≤ w.iConvexComb f :=
  ⟨fun hf ↦ ⟨hf.isConvexSet, fun _ ↦ hf.map_sConvexComb_le⟩, fun h ↦ .of_map_sConvexComb_le h.1 h.2⟩

/-- An affine map is convex on any convex set. -/
protected lemma IsAffineMap.isConvexFunOn (hs : IsConvexSet R s) (hf : IsAffineMap R f) :
    IsConvexFunOn R s f :=
  isConvexFunOn_iff.2 ⟨hs, fun w _ ↦ (hf.map_sConvexComb w).le⟩

@[simp] protected lemma IsConvexFunOn.singleton : IsConvexFunOn R {x} f :=
  isConvexFunOn_iff.2 ⟨.singleton, fun w hw ↦ by
    obtain rfl : w = .single x := by
      rw [← StdSimplex.support_weights_eq_singleton]
      exact (Finset.subset_singleton_iff.1 (Finset.coe_subset_singleton.1 hw)).resolve_left
        w.support_weights_nonempty.ne_empty
    simp⟩

lemma IsConvexFunOn.of_subsingleton (hs : s.Subsingleton) : IsConvexFunOn R s f := by
  obtain rfl | ⟨x, rfl⟩ := hs.eq_empty_or_singleton <;> simp

end IsOrderedConvexSpace

section Field
variable [Field K] [LinearOrder K] [IsStrictOrderedRing K] [ConvexSpace K X] [ConvexSpace K Y]
  [LinearOrder Y] [IsOrderedConvexSpace K Y] {s : Set X} {f : X → Y}

/-- Convexity of a function can be checked via binary combinations if the scalars form a field.

Combined with `IsConvexFunOn.map_iConvexComb_le`, this says that binary Jensen implies finitary
Jensen. -/
lemma IsConvexFunOn.of_map_convexCombPair_le (hs : IsConvexSet K s)
    (hf : ∀ a b : K, ∀ ha hb hab, ∀ x ∈ s, ∀ y ∈ s,
      f (convexCombPair a b ha hb hab x y) ≤ convexCombPair a b ha hb hab (f x) (f y)) :
    IsConvexFunOn K s f := by
  refine .of_isConvexSet_epigraph <| .of_convexCombPair_mem fun a b ha hb hab p hp q hq ↦ ?_
  simp only [Set.mem_ofPred_eq, Prod.fst_convexCombPair, Prod.snd_convexCombPair] at hp hq ⊢
  refine ⟨hs.convexCombPair_mem hp.1 hq.1 ha hb hab, ?_⟩
  calc f (convexCombPair a b ha hb hab p.1 q.1)
      ≤ convexCombPair a b ha hb hab (f p.1) (f q.1) := hf a b ha hb hab _ hp.1 _ hq.1
    _ ≤ convexCombPair a b ha hb hab p.2 q.2 := convexCombPair_le_convexCombPair _ _ _ hp.2 hq.2

/-- **Jensen's inequality**: a function satisfying the binary Jensen inequality on a convex set `s`
satisfies the finitary one. -/
lemma map_iConvexComb_le_of_map_convexCombPair_le (hs : IsConvexSet K s)
    (hf : ∀ a b : K, ∀ ha hb hab, ∀ x ∈ s, ∀ y ∈ s,
      f (convexCombPair a b ha hb hab x y) ≤ convexCombPair a b ha hb hab (f x) (f y))
    {w : StdSimplex K I} {x : I → X} (hx : ∀ i, w.weights i ≠ 0 → x i ∈ s) :
    f (w.iConvexComb x) ≤ w.iConvexComb fun i ↦ f (x i) :=
  (IsConvexFunOn.of_map_convexCombPair_le hs hf).map_iConvexComb_le hx

end Field
end Convexity
