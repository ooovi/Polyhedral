/-
Copyright (c) 2026 Olivia Röhrig, Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter, Olivia Röhrig
-/

import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Finite.Face.Basic
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Module
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.Basic
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Face.Homogenization

/-! In this file we prove the Krein-Milman theorem for polytopes: every polytope is the convex
hull of its vertices, that is, of the finite set of points whose singletons are faces.

The proof is independent of the Krein-Milman theorem for FG cones
(`PointedCone.FG.krein_milman`); the cone version is instead derived from the present theorem
by slicing a salient cone at weight one. The key step here shows that a generator outside the
convex hull of the remaining generators spans a singleton face; this is obtained from the
cone-side lemma `PointedCone.span_singleton_isFaceOf_sup_singleton_of_not_mem` via
homogenization. -/

variable {R V A : Type*}

open Convexity Affine Affine.IsHomogenization PointedCone

section Field

variable [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable [AddCommGroup V] [Module R V]
variable [AddTorsor V A]

variable {P : Set A}

variable {W} [AddCommGroup W] [Module R W] (ℋ : Affine.IsHomogenization R A W) in
/-- The dehomogenization of the ray spanned by an embedded point is the singleton of that
point. -/
@[simp] lemma dehomogenize_hull_singleton_ofPoint (p : A) :
    Convexity.dehomogenize ℋ (R ∙₊ ℋ.ofPoint p) = {p} := by
  ext q
  constructor
  · intro hq
    have hq' : ℋ.ofPoint q ∈ R ∙₊ ℋ.ofPoint p := hq
    simp only [Submodule.mem_span_singleton, Subtype.exists, Nonneg.mk_smul, exists_prop] at hq'
    obtain ⟨c, -, hc⟩ := hq'
    have hw := congrArg ℋ.weight hc
    simp only [map_smul, ℋ.weight_ofPoint, smul_eq_mul, mul_one] at hw
    rw [hw, one_smul] at hc
    exact ℋ.ofPoint_injective hc ▸ rfl
  · rintro rfl
    simp [Convexity.dehomogenize]

variable [ConvexSpace R A] [IsAffineConvexSpace R V A]

/-- If a point `x` does not lie in the convex hull of a set `s`, then the singleton of `x` is
a face of the convex hull of `insert x s`. -/
lemma IsFaceOf.singleton_convexHull_insert {s : Set A} {x : A} {v : V} (hx : x ∉ convexHull R s) :
    IsFaceOf R ({x} : Set A) (convexHull R (insert x s)) := by
  let : ConvexSpace R (Homogenization R A) := .ofModule
  let ℋ := IsHomogenization.canonical R A
  have hhom : homogenize (IsHomogenization.canonical R A) (convexHull R (insert x s)) =
      PointedCone.hull R (ℋ.ofPoint '' s) ⊔ (R ∙₊ ℋ.ofPoint x) := by
    rw [← hull_image_ofPoint_eq_homogenize_convexHull, Set.image_insert_eq, hull_insert, sup_comm]
  have hnot : ℋ.ofPoint x ∉ PointedCone.hull R (ℋ.ofPoint '' s) := by
    rw [hull_image_ofPoint_eq_homogenize_convexHull (ℋ := ℋ)]
    exact fun h => hx ((ofPoint_mem_homogenize_iff_mem _ x IsConvexSet.convexHull).mp h)
  have hsal : (PointedCone.hull R (ℋ.ofPoint '' s) ⊔ (R ∙₊ ℋ.ofPoint x)).Salient :=
    hhom ▸ homogenize_salient _ _
  have hface := span_singleton_isFaceOf_sup_singleton_of_not_mem hnot hsal
  rw [← hhom] at hface
  have h := dehomogenize_isFaceOf ℋ hface
  rwa [dehomogenize_homogenize, dehomogenize_hull_singleton_ofPoint ℋ x] at h
  exact IsConvexSet.convexHull

/-- Krein-Milman theorem for polytopes: every polytope is the convex hull of its vertices,
that is, of the finite set of points whose singletons are faces. -/
theorem IsPolytope.krein_milman (hP : IsPolytope R P) :
    ∃ s : Finset A, Convexity.convexHull R (s : Set A) = P ∧ ∀ x ∈ s, IsFaceOf R {x} P := by
  classical
  suffices h : ∀ t : Finset A, ∀ P : Set A, Convexity.convexHull R (t : Set A) = P →
      ∃ s : Finset A, Convexity.convexHull R (s : Set A) = P ∧ ∀ x ∈ s, IsFaceOf R {x} P by
    obtain ⟨t, ht⟩ := hP
    exact h t P ht.symm
  intro t
  induction t using Finset.strongInduction with
  | _ t ih =>
    intro P hP
    by_cases hex : ∃ x ∈ t, x ∈ Convexity.convexHull R ((t.erase x : Finset A) : Set A)
    · -- a redundant generator can be dropped and the induction hypothesis applies
      obtain ⟨x, hxt, hx⟩ := hex
      refine ih (t.erase x) (Finset.erase_ssubset hxt) P ?_
      rw [← hP]
      -- ext
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
