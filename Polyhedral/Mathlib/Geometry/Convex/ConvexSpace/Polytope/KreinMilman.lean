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

variable {R V A : Type*}

open Convexity ConvexSet

namespace Convexity

section Field

variable [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable [AddCommGroup V] [Module R V]
variable [AddTorsor V A]

variable [ConvexSpace R A] [IsAffineConvexSpace R V A]

variable {P : ConvexSet R A}

include V in
/-- Krein-Milman theorem for polytopes: every polytope is the convex hull of its vertices,
that is, of the finite set of points whose singletons are faces. -/
theorem IsPolytope.krein_milman (hP : IsPolytope R (P : Set A)) :
    ∃ s : Finset A, ConvexSet.convexHull R (s : Set A) = P ∧ ∀ x ∈ s, IsFaceOf {x} P := by
  classical
  suffices h : ∀ t : Finset A, ∀ P : ConvexSet R A, ConvexSet.convexHull R (t : Set A) = P →
      ∃ s : Finset A, ConvexSet.convexHull R (s : Set A) = P ∧ ∀ x ∈ s, IsFaceOf {x} P by
    obtain ⟨t, ht⟩ := hP
    exact h t P (SetLike.ext' ht.symm)
  intro t
  induction t using Finset.strongInduction with
  | _ t ih =>
    intro P hP
    by_cases hex : ∃ x ∈ t, x ∈ Convexity.convexHull R ((t.erase x : Finset A) : Set A)
    · -- a redundant generator can be dropped and the induction hypothesis applies
      obtain ⟨x, hxt, hx⟩ := hex
      refine ih (t.erase x) (Finset.erase_ssubset hxt) P ?_
      rw [← hP]
      apply SetLike.ext'
      refine subset_antisymm
        (convexHull_mono (Finset.coe_subset.mpr (Finset.erase_subset x t))) ?_
      refine (IsConvexSet.convexHull_subset_iff IsConvexSet.convexHull).mpr ?_
      intro y hy
      rcases eq_or_ne y x with rfl | hne
      · exact hx
      · exact subset_convexHull_self (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hne, hy⟩))
    · -- otherwise every generator is a vertex
      push Not at hex
      refine ⟨t, hP, fun x hxt => ?_⟩
      have h := IsFaceOf.singleton_convexHull_insert (R := R) (hex x hxt)
      rwa [← Finset.coe_insert, Finset.insert_erase hxt, hP] at h

end Field

end Convexity
