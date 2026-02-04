/-
Copyright (c) 2025 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Order.Partition.Basic
import Mathlib.Order.Grade

import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.MinkowskiWeyl
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Face.Lattice
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Face.Exposed
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Face.Faces2
import Polyhedral.Hyperplane
import Polyhedral.Halfspace

open Module

-- ## PREDICATE

namespace PointedCone

variable {R : Type*} [Field R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}
variable {C F F₁ F₂ : PointedCone R M}

lemma exists_fg_span_subset_face {s : Finset M} (hF : F.IsFaceOf (span R s)) :
    ∃ t ⊆ s, span R t.toSet = F := by
  use (s.finite_toSet.inter_of_left F).toFinset
  simp [IsFaceOf.span_inter_face_span_inf_face hF]

/-- Faces of FG cones are FG. -/
lemma IsFaceOf.fg_of_fg (hC : C.FG) (hF : F.IsFaceOf C) : F.FG := by
  obtain ⟨_, rfl⟩ := hC
  let ⟨t, _, tt⟩ := exists_fg_span_subset_face hF
  use t, tt



-- TODO: can we reduce assumptions?
variable (p) [Fact (Function.Surjective p.flip)] in
lemma IsFaceOf.FG.subdual_subdual (hC : C.FG) (hF : F.IsFaceOf C) :
    subdual p.flip (dual p C) (subdual p C F) = F := by
  repeat rw [subdual_def]
  rw [FG.dual_flip_dual p hC]
  rw [← dual_span_lineal_dual]
  rw [Submodule.coe_inf, Submodule.coe_restrictScalars]
  nth_rw 3 [← PointedCone.ofSubmodule_coe]
  rw [FGDual.dual_inf_dual_sup_dual ?_ ?_]
  · rw [Submodule.coe_restrictScalars, dual_eq_submodule_dual]
    rw [FG.dual_flip_dual p hC]
    nth_rw 2 [← Submodule.dual_span]
    rw [Submodule.dual_flip_dual p]
    have H : (C ⊔ F.linSpan).lineal = F.linSpan := by
      sorry
    rw [H]
    exact hF.inf_linSpan
  · simpa using FG.dual_fgdual _ hC
  · rw [LinearMap.flip_flip, coe_fgdual_iff, ← Submodule.dual_span]
    exact Submodule.FG.dual_fgdual _ (submodule_span_fg <| hF.fg_of_fg hC)

-- TODO: can we reduce assumptions?
-- variable (p) [Fact p.SeparatingLeft] in
-- lemma IsFaceOf.FG.subdual_subdual' (hC : C.FG) (hF : F.IsFaceOf C) :
--     subdual p.flip (dual p C) (subdual p C F) = F := by
--   wlog _ : Module.Finite R M with exposed -- reduction to finite dimensional case
--   · sorry
--   repeat rw [subdual_def]
--   rw [FG.dual_flip_dual p hC]
--   rw [← dual_span_lineal_dual]
--   rw [Submodule.coe_inf, Submodule.coe_restrictScalars]
--   nth_rw 3 [← PointedCone.ofSubmodule_coe]
--   rw [FGDual.dual_inf_dual_sup_dual ?_ ?_]
--   · rw [Submodule.coe_restrictScalars, dual_eq_submodule_dual]
--     rw [FG.dual_flip_dual p hC]
--     nth_rw 2 [← Submodule.dual_span]
--     rw [Submodule.dual_flip_dual p]
--     have H : (C ⊔ F.linSpan).lineal = F.linSpan := by
--       sorry
--     rw [H]
--     exact IsFaceOf.inf_submodule hF
--   · simpa using FG.dual_fgdual _ hC
--   · rw [LinearMap.flip_flip, coe_fgdual_iff, ← Submodule.dual_span]
--     exact Submodule.FG.dual_fgdual _ (submodule_span_fg <| hF.fg_of_fg hC)


/-- Every face of an FG cone is exposed. -/
lemma IsFaceOf.FG.exposed (hC : C.FG) (hF : F.IsFaceOf C) :
    F.IsExposedFaceOf C := by
  wlog _ : Module.Finite R M with exposed -- reduction to finite dimensional case
  · let S : Submodule R M := .span R C
    have H := exposed (FG.restrict_fg S hC) (restrict S hF)
      (Finite.iff_fg.mpr <| submodule_span_fg hC)
    have hC : C ≤ Submodule.span R (C : Set M) := Submodule.le_span
    simpa [S, hC, le_trans hF.le hC] using H.embed
  rw [← FG.dual_flip_dual (Dual.eval R M) hC]
  rw [← subdual_subdual (Dual.eval R M) hC hF]
  exact .subdual_dual _ <| .subdual_dual _ hF

end PointedCone








-- ## BUNDLES STRUCTURE

namespace PointedCone

variable {R : Type*} [Field R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}
variable {C : PointedCone R M}
variable {F F₁ F₂ : Face C}

variable (hC : C.FG)



-- lemma Face.dual_dual (F : Face C) : dual p.flip (dual p F) = F := sorry


-- ## RANK

noncomputable def Face.rank (F : Face C) := Module.rank R F.span

-- def Face.IsRay (F : Face C) := F.rank = 1

-- lemma isAtom_of_isRay {F : Face C} (h : F.IsRay) : IsAtom F := sorry

-- def atoms : Set (Face C) := {F : Face C | IsAtom F}
-- def rays : Set (Face C) := {F : Face C | F.IsRay}

-- def coatoms : Set (Face C) := {F : Face C | IsCoatom F}
-- alias facets := coatoms

/-- An FG cone has finitely many faces. -/
theorem FG.finite_face (hC : C.FG) : Finite (Face C) := by
  obtain ⟨s, rfl⟩ := hC
  apply Finite.of_injective (β := Finset.powerset s)
    fun F => ⟨(exists_fg_span_subset_face F.isFaceOf).choose, by
      simpa using (exists_fg_span_subset_face F.isFaceOf).choose_spec.1 ⟩
  intro F F' hF
  have h := congrArg (fun s : s.powerset => PointedCone.span R (s : Set M)) hF
  simp only [(exists_fg_span_subset_face F.isFaceOf).choose_spec] at h
  exact Face.toPointedCone_eq_iff.mp sorry -- h

lemma FG.face_atomic (hC : C.FG) : IsAtomic (Face C) :=
  sorry -- # broken since PR
  -- letI := FG.finite_face hC; Finite.to_isAtomic

lemma FG.face_coatomic (hC : C.FG) : IsCoatomic (Face C) :=
  sorry -- # broken since PR
  -- letI := FG.finite_face hC; Finite.to_isCoatomic


-- atoms are 1D

lemma foobarfoo'' (hF : IsAtom F) :
    ∃ x : M, F = (C.lineal : PointedCone R M) ⊔ span R {x} :=

  sorry

lemma foobarfoo' (hF : IsAtom F) :
    PointedCone.rank (F : PointedCone R M) = Module.rank R C.lineal + 1 :=
  sorry

lemma foobarfoo (hC : C.Salient) (hF : IsAtom F) :
    PointedCone.rank (F : PointedCone R M) = 1 := sorry

/-
The way to proving graded:
 * assume C is pointed and FG
 * choose a finite generating set
 * there is a minimal subset that still generates
 * choose any element of the minimal subset
 * this element spans a face of C
-/

theorem span_singleton_isFaceOf_of_fg_salient (hfg : C.FG) (hpt : C.Salient) (h₀ : C ≠ ⊥) :
    ∃ r ∈ C, (span R {r}).IsFaceOf C := by
  sorry

-- theorem isAtom_dim_add_one (F : Face C) (hF : IsAtom F) : F.rank = rank R (lineal C) + 1 := sorry

-- ## KREIN MILMAN

instance atomistic_of_fg (hC : C.FG) : IsAtomistic (Face C) := sorry

instance coatomistic_of_fg (hC : C.FG) : IsCoatomistic (Face C) := sorry

instance face_complemented (hC : C.FG) : ComplementedLattice (Face C) := sorry

instance face_graded (hC : C.FG) : GradeOrder ℕ (Face C) := sorry

------

-- ## ROADMAP TO GRADED

lemma foo {C : PointedCone R M} (hC : C.Salient) {x : M} :
    (C ⊔ span R {x}).Salient ↔ -x ∉ C := by
  unfold Salient ConvexCone.Salient
  simp [Submodule.mem_sup, Submodule.mem_span_singleton]
  constructor <;> intro h
  · sorry
  · sorry

/-- If a point `x` does not lie in a cone `C` and `span R (C ∪ {x})` is salient, then `x` spans
  a face of `C ∪ {x}`. -/
lemma span_singleton_isFaceOf_sup_singleton_of_not_mem {C : PointedCone R M} {x : M}
    (hx : x ∉ C) (hC : (C ⊔ span R {x}).Salient) : (span R {x}).IsFaceOf (C ⊔ span R {x}) := by
  rw [IsFaceOf.iff_mem_of_add_mem]
  constructor
  · exact le_sup_right
  intro y z hy hz hyz
  simp [Submodule.mem_sup, Submodule.mem_span_singleton] at *
  obtain ⟨y', hy', a, _, hy⟩ := hy
  obtain ⟨z', hz', b, _, hz⟩ := hz
  obtain ⟨c, _, hyz⟩ := hyz
  rw [← hy, ← hz, add_assoc, ← sub_eq_iff_eq_add] at hyz
  nth_rw 2 [add_comm] at hyz
  rw [← add_assoc, ← add_smul, sub_add_eq_sub_sub, sub_eq_iff_eq_add, ← sub_smul] at hyz
  set t := c - (a + b)
  have h := C.add_mem hy' hz'
  rw [← hyz] at h
  rcases le_or_gt t 0 with ht | ht
  · set C' := C ⊔ span R {x}
    have hxC' : x ∈ C' := by
      simpa [C', Submodule.mem_sup, Submodule.mem_span_singleton] using ⟨0, by simp, 1, by simp⟩
    have hxC' : -t • x ∈ C' := C'.smul_mem (neg_nonneg.mpr ht) hxC'
    rw [neg_smul] at hxC'
    have hCC' : C ≤ C' := by simp [C']
    have hC : ∀ x ∈ C', -x ∈ C' → x = 0 := by
      intro x hx hx'
      by_contra h
      exact hC _ hx h hx'
    have h0 := hC _ (hCC' h) hxC'
    rw [h0, Eq.comm, add_eq_zero_iff_eq_neg] at hyz
    rw [hyz] at hy'
    have h0' := hC _ (hCC' hz') (hCC' hy')
    simp [h0'] at hyz
    simp [hyz] at hy
    use a
  · rw [smul_mem_iff ht] at h
    contradiction

lemma exists_ray {s : Finset M} (hs : s ≠ ∅) (hsal : (span R (s : Set M)).Salient) :
    ∃ x ∈ s, (span R {x}).IsFaceOf (span R s) := by classical
  induction s using Finset.induction with
  | empty => contradiction
  | insert w s hwr hind =>
    by_cases h : w ∈ span R s
    · by_cases hs' : s = ∅
      · simp [hs']
      rw [Finset.coe_insert] at ⊢ hsal
      unfold span at *
      rw [Submodule.span_insert_eq_span h] at ⊢ hsal
      obtain ⟨x, hxs, hx⟩ := hind hs' hsal
      use x
      simp [hxs, hx]
    · use w
      rw [← Finset.union_singleton, Finset.coe_union, span_union] at ⊢ hsal
      simp at ⊢ hsal
      exact span_singleton_isFaceOf_sup_singleton_of_not_mem h hsal

/-- A non-bottom FG cone has a ray face. -/
lemma FG.exists_ray' (hfg : C.FG) (hC : C ≠ ⊥) (hsal : C.Salient) :
    ∃ x : M, (span R {x}).IsFaceOf C := by
  obtain ⟨s, rfl⟩ := hfg
  have h : s ≠ ∅ := by
    by_contra h
    simp [h] at hC
  obtain ⟨_, hx⟩ := exists_ray h hsal
  exact ⟨_, hx.2⟩

--------------

-- lemma span_singleton_isFaceOf_union_singleton_of_not_mem {C : PointedCone R M}
--     (hC : C.DualClosed p) (hC' : C.Salient) {x : M} (hx : x ∉ C) :
--     (span R {x}).IsFaceOf (C ⊔ span R {x}) := by
--   replace hC : C.DualClosed (Dual.eval R M) := hC.to_eval
--   obtain ⟨f, hf, h⟩ := farkas hC hx
--   obtain ⟨g, hg⟩ := exists_dual_pos₀ (Dual.eval R M) hC'
--   simp at hf hg h
--   apply IsExposedFaceOf.isFaceOf
--   use f - (f x / g x) • g
--   constructor <;> intro y hy
--     <;> simp only [Submodule.mem_sup, Submodule.mem_span_singleton] at hy
--     <;> obtain ⟨y, hy, a, ha, rfl⟩ := hy
--     <;> obtain ⟨b, rfl⟩ := ha
--     -- <;> simp
--   · sorry
--   · simp [Submodule.mem_span_singleton]
--     constructor <;> intro h
--     · sorry
--     · obtain ⟨b, hb, h⟩ := h
--       sorry

-- -- 2. version of Farkas lemma for finite sets
-- variable (p) [Fact p.SeparatingLeft] in
-- lemma FG.farkas {s : Finset M} {x : M} (h : x ∉ span R s) :
--     ∃ φ : N, 0 > p x φ ∧ ∀ y ∈ s, 0 ≤ p y φ := by
--   let ⟨φ, hφ, h⟩ := PointedCone.farkas (FG.isDualClosed p ⟨s, rfl⟩) h
--   exact ⟨φ, hφ, fun y hy => h y (subset_span hy)⟩

-- -- 2. version of Farkas lemma for finite sets
-- variable (p) [Fact p.SeparatingLeft] in
-- lemma FG.farkas' {s : Finset M} {x : M} (hx : x ∉ span R s) (hx' : -x ∉ span R s) :
--     ∃ φ : N, p x φ = 0 ∧ ∀ y ∈ s, 0 ≤ p y φ ∧ (p y φ = 0 → y ∈ (span R s).lineal) := by
--   obtain ⟨f, hf, h⟩ := FG.farkas p hx
--   obtain ⟨g, hg⟩ := exists_dual_pos p (span R s) /- This lemma is not yet proven. -/
--   use f - (p x f / p x g) • g
--   simp
--   have hgx : 0 < p x g := sorry
--   constructor
--   · simp [ne_of_gt hgx]
--   · intro y hy
--     -- somehow use that f x < 0, g x > 0 and f y >= 0 for all y != x.
--     constructor
--     · sorry
--     · intro h
--       sorry

-- -- 2. version of Farkas lemma for finite sets
-- variable (p) [Fact p.SeparatingLeft] in
-- lemma FG.farkas'' {s : Finset M} {x : M} (hs : (span R (s : Set M)).Salient) (h : x ∉ span R s) :
--     ∃ φ : N, p x φ = 0 ∧ ∀ y ∈ s, 0 ≤ p y φ ∧ (p y φ = 0 → y = 0) := by
--   obtain ⟨f, hf, h⟩ := FG.farkas p h
--   obtain ⟨g, hg⟩ := exists_dual_pos p hs /- this lemma is not trivial. It proves that a pointed
--     (i.e. salient) cone is contained in some halfspace. g is the normal vector of that halfspace.
--     This lemma is not yet proven, but all the machinery is there. -/
--   use f - (p x f / p x g) • g
--   simp
--   have hgx : 0 < p x g := sorry
--   constructor
--   · simp [ne_of_gt hgx]
--   · intro y hy

--     -- use that f x < 0 but g x and all other f y are >= 0
--     sorry

-- -- If a generator is not in the span of the other generators, then it spans a face.
-- lemma FG.mem_span_setminus_iff_span_isFaceOf_span {s : Finset M}
--     (hs : (span R (s : Set M)).Salient) {x : M} (hx : x ∈ s) (h : x ∉ span R (s \ {x})) :
--       (span R {x}).IsFaceOf (span R s) := by classical
--   have h' : (span R _).DualClosed (Dual.eval R M) := FG.isDualClosed _ ⟨s \ {x}, rfl⟩
--   simp at h'
--   have hfar := PointedCone.farkas h' h


--   have hspan' : (span R (s \ {x} : Finset M)).Salient := Salient.of_le_salient hspan
--     (Submodule.span_monotone (by simp))
--   obtain ⟨g, hg, hg'⟩ := FG.farkas'' (Dual.eval R M) hspan' (by simpa using h)
--   apply IsExposedFaceOf.isFaceOf -- it suffices to show that we obtain an exposed face
--   use g
--   constructor <;> intro y hy
--   · by_cases h : y = x
--     · simpa only [h] using ge_of_eq hg
--     · specialize hg' y
--       simp at hg'
--       sorry
--   · rw [Submodule.mem_span_singleton]
--     constructor <;> intro h
--     · sorry
--     · sorry
--       -- rw [Submodule.mem_span_singleton] at h
--       -- obtain ⟨c, rfl⟩ := h
--       -- simp; ring_nf
--       -- rw [mul_assoc]
--       -- rw [mul_inv_cancel₀ (ne_of_gt hgx)]
--       -- simp

-- -- A non-bottom cone has a ray as face.
-- lemma FG.exists_ray (hC : C.FG) (hC' : C.Salient) (hC'' : C ≠ ⊥) :
--     ∃ x : M, (span R {x}).IsFaceOf C := by classical
--   let s' := sInf {t : Set M | span R t = C}
--   obtain ⟨s, rfl⟩ := hC
--   let t := sInf {r : Set M | r ⊆ s ∧ span R r = span R s}
--   have ht : t.Nonempty := sorry
--   obtain ⟨x, hx⟩ := ht
--   use x
--   let t' := t \ {x}
--   have ht : t ⊆ s := sorry
--   have ht' : x ∉ t' := sorry
--   refine FG.mem_span_setminus_iff_span_isFaceOf_span hC' (ht hx) ?_
--   sorry

end PointedCone
