/-
Copyright (c) 2026 Mortiz Firschinggit , Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mortiz Firsching
-/
module

public import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.Basic
public import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Face.Basic

/-! In this file we prove the Krein-Milman theorem for polytopes: every polytope is the convex
hull of its vertices, that is, of the finite set of points whose singletons are faces.

The proof is independent of the Krein-Milman theorem for FG cones
(`PointedCone.FG.krein_milman`); the cone version is instead derived from the present theorem
by slicing a salient cone at weight one. The key step here shows that a generator outside the
convex hull of the remaining generators spans a singleton face; this is obtained from the
cone-side lemma `PointedCone.span_singleton_isFaceOf_sup_singleton_of_not_mem` via
homogenization. -/

@[expose] public section

variable {R X : Type*}

open Convexity ConvexSet

namespace Convexity

section Field

variable [DivisionRing R] [LinearOrder R] [IsStrictOrderedRing R]
variable [ConvexSpace R X] [IsCancelConvexSpace R X]

variable {P : Set X}

open Finset in
/-- Krein-Milman theorem for polytopes: every polytope is the convex hull of its vertices,
that is, of the finite set of points whose singletons are faces. -/
theorem IsPolytope.krein_milman (hP : IsPolytope R P) :
    ∃ s : Finset X, convexHull R s = P ∧ ∀ x ∈ s, IsFaceOf R {x} P := by
  classical
  suffices h : ∀ t : Finset X, ∀ P : Set X, convexHull R t = P →
      ∃ s : Finset X, convexHull R s = P ∧ ∀ x ∈ s, IsFaceOf R {x} P by
    obtain ⟨t, ht⟩ := hP
    exact h t P ht.symm
  intro t
  induction t using Finset.strongInduction with
  | _ t ih =>
    intro P hP
    by_cases hex : ∃ x ∈ t, x ∈ convexHull R (t.erase x)
    · -- a redundant generator can be dropped and the induction hypothesis applies
      obtain ⟨x, hxt, hx⟩ := hex
      refine ih (t.erase x) (erase_ssubset hxt) P ?_
      rw [← hP]
      refine subset_antisymm (convexHull_mono (coe_subset.mpr (erase_subset x t))) ?_
      refine IsConvexSet.convexHull.convexHull_subset_iff.mpr ?_
      intro y hy
      rcases eq_or_ne y x with rfl | hne
      · exact hx
      · exact subset_convexHull_self (mem_coe.mpr (mem_erase.mpr ⟨hne, hy⟩))
    · -- otherwise every generator is a vertex
      push Not at hex
      refine ⟨t, hP, fun x hxt => ?_⟩
      have h := IsFaceOf.singleton_convexHull_insert (hex x hxt)
      rwa [← coe_insert, insert_erase hxt, hP] at h

end Field

end Convexity
