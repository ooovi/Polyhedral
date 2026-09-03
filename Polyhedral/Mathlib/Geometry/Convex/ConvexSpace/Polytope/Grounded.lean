/-
Copyright (c) 2026 Anouk Brose, Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anouk Brose, Justus Springer
-/
module

public import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.Lattice

/-!
# Grounded Polytopes

We define `IsGroundedPolytope` with respect to a set `S` as the convex hull of a
finite set contained in `S`.
Common examples are lattice polytopes, where `S` is a lattice such as `ℤᵈ`, rational polytopes,
where `S = ℚᵈ`, {0,1}-polytopes where `S= {0,1}ᵈ`, but
there could also be more abstract examples such as vertices whose coordinates
are all prime numbers.
We don't think the name `IsGroundedPolytope` will be the best choice, and are thinking
of renaming it to `IsPolytopeOn`,
or have a defintion called `HasExtremePointsIn`.

We prove basic lemmas about `IsGroundedPolytope`. When we consider lattice polytopes
specifically, there will be many more interesting lemmas later on.
See `Submodule.IsLattice'` in `Algebra/Module/Lattice/Basic.lean` for the current notion of lattice.


-/

@[expose] public section

namespace Convexity

variable {R X : Type*}

open ConvexSpace

variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [ConvexSpace R X]
variable (S : Set X)

variable (R) in
/-- A set `P` is a *grounded polytope* in `S` if there exists a finite set `t` contained in `S`
such that `P` is the convex hull of `t`. If `S` is a lattice, this is usually called a
*lattice polytope*. -/
def IsGroundedPolytope (P : Set X) : Prop :=
  ∃ t : Finset X, (t : Set X) ⊆ S ∧ P = convexHull R t

namespace IsGroundedPolytope

/-- A grounded polytope is a polytope. -/
lemma isPolytope (P : Set X)
    (h : IsGroundedPolytope R S P) : IsPolytope R P := by
  obtain ⟨t, _, hP⟩ := h
  exact ⟨t, hP⟩

protected lemma empty : IsGroundedPolytope R S ∅ := ⟨∅, by simp, by simp⟩

protected lemma singleton (x : X) (h : x ∈ S) : IsGroundedPolytope R S {x} :=
  ⟨{x}, by simpa, by simp⟩

variable (R) in
lemma convexHull_finite {s : Set X} (hs : s.Finite) (hsS : s ⊆ S) :
    IsGroundedPolytope R S (convexHull R s) :=
  ⟨hs.toFinset, by simpa, by simp⟩

/-- If `P` and `Q` are S-polytopes, then the convex hull of `P ∪ Q` is an S-polytope. -/
lemma convexHull_union {P Q : Set X} (hP : IsGroundedPolytope R S P)
    (hQ : IsGroundedPolytope R S Q) :
    IsGroundedPolytope R S (convexHull R (P ∪ Q)) := by classical
  obtain ⟨t₁, ht₁, rfl⟩ := hP
  obtain ⟨t₂, ht₂, rfl⟩ := hQ
  exact ⟨t₁ ∪ t₂, by simp [ht₁, ht₂],
    by simp [convexHull_union_convexHull, convexHull_convexHull_union]⟩

/-- If `P` is an S-polytope and `S ⊆ T`, then `P` is a T-polytope. -/
lemma mono_subset {P : Set X} {S T : Set X} (hP : IsGroundedPolytope R S P) (hST : S ⊆ T) :
    IsGroundedPolytope R T P := by
  obtain ⟨t, h₁, h₂⟩ := hP
  exact ⟨t, h₁.trans hST, h₂⟩

/-- If an S-polytope is non-empty, then it contains a point in `S`. -/
lemma inter_ground_set_nonempty_of_nonempty {P : Set X} (hP : IsGroundedPolytope R S P)
    (h : P.Nonempty) : (P ∩ S).Nonempty := by
  obtain ⟨t, htS, hPt⟩ := hP
  apply Set.Nonempty.mono (by simpa using ⟨hPt ▸ subset_convexHull_self, htS⟩)
  by_contra! H
  simp only [H, convexHull_empty] at hPt
  exact Set.not_nonempty_empty (hPt ▸ h)

/-- An S-polytope `P` contains a point in `S` if and only if `P` is non-empty. -/
lemma inter_ground_set_nonempty_iff {P : Set X} (hP : IsGroundedPolytope R S P) :
    (P ∩ S).Nonempty ↔ P.Nonempty :=
  ⟨Set.Nonempty.left, hP.inter_ground_set_nonempty_of_nonempty S⟩

end IsGroundedPolytope

end Convexity
