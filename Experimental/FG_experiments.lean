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
-- import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Face.Faces2
-- import Polyhedral.Hyperplane
-- import Polyhedral.Halfspace

open Module

-- ## PREDICATE

namespace PointedCone

variable {R : Type*} [Field R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}
variable {C F F₁ F₂ : PointedCone R M}

lemma exists_fg_span_subset_face {s : Finset M} (hF : F.IsFaceOf (span R s)) :
    ∃ t ⊆ s, span R t = F := by
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
    have H := exposed (FG.restrict_fg S hC) (IsFaceOf.restrict S hF)
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

------

-- ## ROADMAP TO GRADED

-- The theory below does not need duality! Move it accordingly

lemma foo {C : PointedCone R M} (hC : C.Salient) {x : M} :
    (C ⊔ span R {x}).Salient ↔ -x ∉ C := by
  unfold Salient ConvexCone.Salient
  simp [Submodule.mem_sup, Submodule.mem_span_singleton]
  constructor <;> intro h
  · sorry
  · sorry

open Submodule in
/-- If a point `x` does not lie in a cone `C` but together with `C` spans a salient cone, then
  `x` spans a face of `span R (C ∪ {x})`. -/
lemma span_singleton_isFaceOf_sup_singleton_of_not_mem {C : PointedCone R M} {x : M}
    (hx : x ∉ C) (hC : (C ⊔ span R {x}).Salient) : (span R {x}).IsFaceOf (C ⊔ span R {x}) := by
  rw [IsFaceOf.iff_mem_of_add_mem]
  constructor
  · exact le_sup_right
  intro y z hy hz hyz
  simp [mem_sup, mem_span_singleton] at *
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
      simpa [C', mem_sup, mem_span_singleton] using ⟨0, by simp, 1, by simp⟩
    have hxC' : -t • x ∈ C' := C'.smul_mem (neg_nonneg.mpr ht) hxC'
    rw [neg_smul] at hxC'
    have hCC' : C ≤ C' := by simp [C']
    have hC : ∀ x ∈ C', -x ∈ C' → x = 0 := by -- this should actually be the definition of salient
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

open Finset Submodule in
lemma exists_ray' {s : Finset M} (hs : ∃ x ∈ s, x ≠ 0) (hsal : (span R (s : Set M)).Salient) :
    ∃ x ∈ s, x ≠ 0 ∧ (span R {x}).IsFaceOf (span R s) := by classical
  induction s using Finset.induction with
  | empty => absurd hs; simp
  | insert w s hwr hind =>
    by_cases h : w ∈ span R s
    · by_cases hs' : ∃ x ∈ s, x ≠ 0
      · simp only [coe_insert, span, span_insert_eq_span h] at ⊢ hsal
        obtain ⟨x, hxs, hx⟩ := hind hs' hsal
        exact ⟨x, by simp [hxs, hx]⟩
      push_neg at hs'
      have hs' : ∀ x ∈ (s : Set M), x = 0 := fun x hx => hs' x hx
      simp [Submodule.span_eq_bot.mpr hs'] at h
      obtain ⟨x, hx, h⟩ := hs
      simp at hx
      rcases hx with hx | hx
      · rw [hx] at h; contradiction
      · specialize hs' x hx; contradiction
    · use w
      simp_rw [← union_singleton, coe_union, span_union, coe_singleton, union_singleton,
        mem_insert, true_or, true_and] at ⊢ hsal
      exact ⟨by by_contra H; absurd h; simp [H],
        span_singleton_isFaceOf_sup_singleton_of_not_mem h hsal⟩

section -- FG + not bot + Salient

/-- A non-bottom salient FG cone has a ray face. -/
lemma FG.exists_ray (hfg : C.FG) (hC : C ≠ ⊥) (hsal : C.Salient) :
    ∃ x : M, x ≠ 0 ∧ (span R {x}).IsFaceOf C := by
  obtain ⟨s, rfl⟩ := hfg
  have h : ∃ x ∈ s, x ≠ 0 := by
    by_contra h
    simp [h] at hC
  obtain ⟨_, hx⟩ := exists_ray' h hsal
  exact ⟨_, hx.2⟩

lemma zero_le_rank (C : PointedCone R M) : 0 ≤ C.rank := sorry

lemma bot_of_rank_zero (h : C.rank = 0) : C = ⊥ := sorry

lemma bot_iff_rank_zero : C.rank = 0 ↔ C = ⊥ := sorry

lemma Face.bot_iff_rank_zero {F : Face C} : F.rank = 0 ↔ F = ⊥ := sorry

lemma ray_of_rank_one (h : C.rank = 1) : ∃ x : M, C = span R {x} := sorry

lemma Face.rank_one_of_atom (hfg : C.FG) (hC : C ≠ ⊥) (hsal : C.Salient)
    (F : Face C) (hF : IsAtom F) : F.rank = 1 := by
  rcases lt_trichotomy F.rank 1 with h | h | h
  · have h : F.rank = 0 := sorry
    absurd Face.bot_iff_rank_zero.mp h
    exact hF.ne_bot
  · exact h
  · have h1 : (F : PointedCone R M).FG := sorry
    have h2 : (F : PointedCone R M).Salient := sorry

    have h := FG.exists_ray h1 sorry h2
    sorry

-- def Face.atoms (C : PointedCone R M) : Set (Face C) := {F : Face C | IsAtom F}

-- lemma Face.krein_milman : sSup (atoms C) = ⊤ := sorry

-- lemma FG.krein_milman : ∃ s : Set (Face C), (∀ F ∈ s, IsAtom F) ∧ sSup s = ⊤ := sorry

variable (p) [Fact p.SeparatingLeft] in
lemma FG.farkas {s : Finset M} {x : M} (h : x ∉ span R s) :
    ∃ φ : N, 0 > p x φ ∧ ∀ y ∈ s, 0 ≤ p y φ := by
  let ⟨φ, hφ, h⟩ := PointedCone.farkas (FG.isDualClosed p ⟨s, rfl⟩) h
  exact ⟨φ, hφ, fun y hy => h y (subset_span hy)⟩

def opt (C : PointedCone R M) (f g : M →ₗ[R] R) (hg : ∀ x ∈ C, 0 ≤ g x ∧ (g x = 0 → x = 0)) :
    PointedCone R M where
  carrier := {x ∈ C | ∀ y ∈ C, f x * g y ≤ f y * g x}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, map_add] at *
    constructor
    · exact C.add_mem ha.1 hb.1
    intro y hy
    have ha := ha.2 y hy
    have hb := hb.2 y hy
    sorry
  zero_mem' := sorry
  smul_mem' := sorry

lemma IsFaceOf.of_opt (C : PointedCone R M) (f g : M →ₗ[R] R)
    (hg : ∀ x ∈ C, 0 ≤ g x ∧ (g x = 0 → x = 0)) : (C.opt f g hg).IsFaceOf C := sorry

lemma FG.opt_neq_bot (C : PointedCone R M) (hC : C.FG) (f g : M →ₗ[R] R)
    (hg : ∀ x ∈ C, 0 ≤ g x ∧ (g x = 0 → x = 0)) : C.opt f g hg ≠ ⊥ := sorry

-- TODO: golf this
lemma IsFaceOf.span_ray {s : Set M} {x : M} (hx : x ≠ 0)
    (hspan : (span R {x}).IsFaceOf (span R s)) : ∃ y ∈ s, ∃ c : R, 0 < c ∧ y = c • x := by
  have h := hspan.span_inter_face_span_inf_face
  have hs : ∃ w ∈ s ∩ (span R {x}), w ≠ 0 := by
    by_contra H
    absurd hx
    push_neg at H
    simp only [← Set.mem_singleton_iff] at H
    simpa [h] using Submodule.span_mono (R := {c : R // 0 ≤ c}) H
  obtain ⟨y, hy, hy0⟩ := hs
  use y
  simp [Submodule.mem_span_singleton] at hy
  constructor
  · exact hy.1
  obtain ⟨a, ha⟩ := hy.2
  use a
  have ha' : a > 0 := by
    by_contra h
    simp at h
    simp [le_antisymm h ha.1, Eq.comm] at ha
    contradiction
  constructor
  · exact ha'
  exact ha.2.symm

theorem IsFaceOf.salient {C F : PointedCone R M} (hC : C.Salient) (hF : F.IsFaceOf C) :
    F.Salient := by
  intro x xF x_ne_0 x_negF
  have xC : x ∈ C := hF.le (mem_toConvexCone.mp xF)
  have x_negC : -x ∈ C := hF.le (mem_toConvexCone.mp x_negF)
  exact hC x xC x_ne_0 x_negC

-- TODO: this proof uses FG only at one point: to show that opt is non-empty. This should
--  generalize to dual-closed.
lemma FG.krein_milman (hfg : C.FG) (hsal : C.Salient) :
    ∃ s : Finset M, span R s = C ∧ ∀ x ∈ s, (span R {x}).IsFaceOf C := by classical

  let ⟨s, hs⟩ := hfg

  by_cases hs' : s = ∅
  · exact ⟨∅, by simp [← hs, hs']⟩

  by_contra h
  push_neg at h

  let t := s.filter fun x => (span R {x}).IsFaceOf C
  specialize h t

  have hts : t ⊆ s := by simp [t]

  have hst : ¬(s : Set M) ⊆ span R (t : Set M) := by
    by_contra h'
    have h' := Submodule.span_mono (R := {c : R // 0 ≤ c}) h'
    have h'' := Submodule.span_mono (R := {c : R // 0 ≤ c}) hts
    simp at h'
    rw [← le_antisymm h' h'', hs] at h
    simp [t, and_assoc] at h

  obtain ⟨x, hxs, hxt⟩ := Set.not_subset.mp hst
  have hx : x ∈ C := by
    rw [← hs]
    exact subset_span hxs

  obtain ⟨f, hf, hf'⟩ := FG.farkas (Dual.eval R M) hxt

  rw [← hs] at hsal
  obtain ⟨g, hg⟩ := exists_dual_pos₀ (Dual.eval R M) hsal
  rw [hs] at hsal

  simp at hf hf' hg

  rw [hs] at hg

  let F := C.opt f g hg
  have hF : F.IsFaceOf C := IsFaceOf.of_opt C f g hg
  have hF' := opt_neq_bot C hfg f g hg
  have hFsal := Salient.of_le_salient hsal hF.le

  obtain ⟨r, hr0, hrF⟩ := exists_ray (hF.fg_of_fg hfg) hF' hFsal

  have hr := IsFaceOf.trans hrF hF

  rw [← hs] at hr
  obtain ⟨w, hws, c, hc', h⟩ := hr.span_ray hr0

  simp at hws

  have hc0 := (ne_of_lt hc').symm
  have hrw : r = c⁻¹ • w := by
    subst h hs
    simp [smul_smul, hc0]

  rw [hrw] at hr

  have hc := inv_ne_zero hc0

  rw [span_singleton_smul_eq (inv_pos.mpr hc')] at hr
  rw [hs] at hr

  have hwt : w ∈ t := by
    simp [t]
    exact ⟨hws, hr⟩

  have hwF : r ∈ F := by
    have : r ∈ span R {r} := by simp
    exact hrF.le this
  have hwF : w ∈ F := by
    rw [h]
    exact F.smul_mem (le_of_lt hc') hwF

  simp [F, opt] at hwF

  specialize hf' w hwt
  specialize hf

  have hgx := hg x hx
  have hgw := hg w hwF.1

  have hgw : 0 < g w := by
    have hw0 : w ≠ 0 := by
      rw [h]
      exact smul_ne_zero hc0 hr0
    by_contra h
    simp at h
    have hgw' := le_antisymm hgw.1 h
    have := hgw.2 hgw'.symm
    absurd hxt
    contradiction

  have hwF := hwF.2 x hx

  have : 0 ≤ f w * g x := mul_nonneg hf' hgx.1
  have : f x * g w < 0 := mul_neg_of_neg_of_pos hf hgw

  linarith

-- lemma DualClosed.krein_milman :
--     ∃ s : Set M, dual p.flip (dual p s) = C ∧ ∀ x ∈ s, (span R {x}).IsFaceOf C := by
--   by_contra h
--   push_neg at h
--   specialize h {x : M | (span R {x}).IsFaceOf C}
--   simp at h
--   set D := dual p.flip ↑(dual p (sSup {F | F.rank = 1} : Face C))
--   have : D ≤ C := sorry
--   have hCD : ¬C ≤ D := sorry
--   obtain ⟨x, hx⟩ := Set.nonempty_of_not_subset hCD
--   obtain ⟨f, hf, hf'⟩ := farkas (dual_flip_DualClosed p _) hx.2

-- lemma DualClosed.krein_milman' (hdc : C.DualClosed p) (hsal : C.Salient) :
--     ∃ s : Set (Face C), (∀ F ∈ s, F.rank = 1) ∧ dual p.flip (dual p (sSup s : Face C)) = C := by
--   by_contra h
--   push_neg at h
--   specialize h {F : Face C | F.rank = 1}
--   simp at h
--   set D := dual p.flip ↑(dual p (sSup {F | F.rank = 1} : Face C))
--   have : D ≤ C := sorry
--   have hCD : ¬C ≤ D := sorry
--   obtain ⟨x, hx⟩ := Set.nonempty_of_not_subset hCD
--   obtain ⟨f, hf, hf'⟩ := farkas (dual_flip_DualClosed p _) hx.2

--   sorry


end

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

-------

-- theorem isAtom_dim_add_one (F : Face C) (hF : IsAtom F) : F.rank = rank R (lineal C) + 1 := sorry

-- ## KREIN MILMAN

instance atomistic_of_fg (hC : C.FG) : IsAtomistic (Face C) := sorry

instance coatomistic_of_fg (hC : C.FG) : IsCoatomistic (Face C) := sorry

instance face_complemented (hC : C.FG) : ComplementedLattice (Face C) := sorry

instance face_graded (hC : C.FG) : GradeOrder ℕ (Face C) := sorry

end PointedCone
