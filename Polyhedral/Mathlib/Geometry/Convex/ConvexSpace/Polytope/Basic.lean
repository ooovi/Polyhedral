/-
Copyright (c) 2019 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter, Olivia Röhrig
-/

import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
import Mathlib.Geometry.Convex.ConvexSpace.AffineSpace

import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Hull

/-! ... -/

namespace Convexity

variable {R X Y V : Type*}

open ConvexSpace

section Semiring

variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [ConvexSpace R X]

variable (R) in
/-- A set is a polytope if it is the convex hull of finitely many points. -/
def IsPolytope (s : Set X) : Prop := ∃ t : Finset X, s = convexHull R t

end Semiring

namespace IsPolytope

section Semiring

variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [ConvexSpace R X]

variable {P P₁ P₂ : Set X}

lemma isConvexSet (hP : IsPolytope R P) : IsConvexSet R P := by
  obtain ⟨_, rfl⟩ := hP
  exact IsConvexSet.convexHull

variable (R X) in
@[simp] protected lemma empty : IsPolytope R (∅ : Set X) := by
  use ∅; simp

variable (R) in
@[simp] protected lemma singleton (x : X) : IsPolytope R {x} := by
  use {x}; simp

variable (R) in
lemma subsingleton (hP : P.Subsingleton) : IsPolytope R P := by
  obtain rfl | ⟨x, rfl⟩ := hP.eq_empty_or_singleton <;> simp

variable (R) in
lemma convexHull_finite {v : Set X} (hv : v.Finite) :
    IsPolytope R (convexHull R v) := by use hv.toFinset; simp

lemma convexHull_union (h₁ : IsPolytope R P₁) (h₂ : IsPolytope R P₂) :
    IsPolytope R (convexHull R (P₁ ∪ P₂)) := by classical
  obtain ⟨v₁, rfl⟩ := h₁
  obtain ⟨v₂, rfl⟩ := h₂
  use v₁ ∪ v₂
  simp [convexHull_union_convexHull_right, convexHull_convexHull_union]

lemma convexHull_iUnion_finite {p : Set (Set X)} (hp : p.Finite)
    (h : ∀ P ∈ p, IsPolytope R P) : IsPolytope R (convexHull R (⋃ P ∈ p, P)) := by
  induction p, hp using Set.Finite.induction_on with
  | empty => simp
  | insert _ _ h' =>
    simp only [Set.mem_insert_iff, Set.iUnion_iUnion_eq_or_left, forall_eq_or_imp] at ⊢ h
    rw [← convexHull_union_convexHull_right]
    exact convexHull_union h.1 (h' h.2)

variable [ConvexSpace R Y] {f : X → Y}

protected lemma image (hf : IsAffineMap R f) (hP : IsPolytope R P) :
    IsPolytope R (f '' P) := by classical
  obtain ⟨v, rfl⟩ := hP
  use v.image f
  simpa using hf.image_convexHull v

end Semiring

section Field

variable [Field R] [PartialOrder R] [IsStrictOrderedRing R]
variable [ConvexSpace R X]
variable [AddCommGroup V] [Module R V]
variable [AddTorsor V X]

attribute [local instance] AddTorsor.toConvexSpace

variable {P P₁ P₂ : Set X}

protected theorem inter (hP₁ : IsPolytope R P₁) (hP₂ : IsPolytope R P₂) :
    IsPolytope R (P₁ ∩ P₂) := by
  -- TODO:
  -- * homogenize to a cone
  -- * use that the homogenization is FG
  -- * use orderIso structure
  sorry

protected theorem sInter {s : Set (Set X)} (hs : s.Finite) (hs' : s.Nonempty)
    (h : ∀ P ∈ s, IsPolytope R P) : IsPolytope R (⋂₀ s) := by
  induction s, hs using Set.Finite.induction_on with
  | empty => simp at hs'
  | insert _ _ h' =>
    rename Set (Set X) => t
    simp only [Set.mem_insert_iff, forall_eq_or_imp, Set.sInter_insert] at ⊢ h
    by_cases htt : t.Nonempty
    · exact IsPolytope.inter h.1 (h' htt h.2)
    · rw [Set.not_nonempty_iff_eq_empty] at htt
      simp [htt, h.1]

protected theorem iInter {s : Set (Set X)} (hs : s.Finite) (hs' : s.Nonempty)
    (h : ∀ P ∈ s, IsPolytope R P) : IsPolytope R (⋂ P ∈ s, P) := by
  rw [← Set.sInter_eq_biInter]
  exact IsPolytope.sInter hs hs' h

end Field

end IsPolytope

end Convexity
