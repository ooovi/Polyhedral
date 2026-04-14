import Mathlib.Order.Grade
import Mathlib.LinearAlgebra.Quotient.Basic

import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Face.Exposed
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Finite.Face.Rank
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Finite.MinkowskiWeyl
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Ray

namespace PointedCone

section DivisionRingLemmas

variable {R : Type*} [DivisionRing R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {C F : PointedCone R M}

lemma exists_fg_hull_subset_face {s : Finset M} (hF : F.IsFaceOf (hull R s)) :
    ∃ t ⊆ s, hull R t = F := by
  use (s.finite_toSet.inter_of_left F).toFinset
  simp [IsFaceOf.hull_inter_face_hull_inf_face hF]

/-- Faces of FG cones are FG. -/
lemma IsFaceOf.fg (hC : C.FG) (hF : F.IsFaceOf C) : F.FG := by
  obtain ⟨_, rfl⟩ := hC
  let ⟨t, _, tt⟩ := exists_fg_hull_subset_face hF
  use t, tt

lemma lineal_fg (hC : C.FG) : C.lineal.FG := FG.coe_fg_iff.mp ((IsFaceOf.lineal C).fg hC)

end DivisionRingLemmas

section Field

variable {R : Type*} [Field R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}

/- Farkas lemma for finitely generated cones: for any point `x` not in the hull of a finite set `s`,
  there exists a hyperplane `φ` separating `x` from `hull R s`. -/
variable (p) [Fact p.SeparatingLeft] in
lemma FG.farkas {s : Finset M} {x : M} (h : x ∉ hull R s) :
    ∃ φ : N, 0 > p x φ ∧ ∀ y ∈ s, 0 ≤ p y φ := by
  let ⟨φ, hφ, h⟩ := PointedCone.farkas (FG.isDualClosed p ⟨s, rfl⟩) h
  exact ⟨φ, hφ, fun y hy => h y (subset_hull hy)⟩

variable {C F F₁ F₂ : PointedCone R M}

section exposed

-- TODO: can we reduce assumptions?
variable (p) [Fact (Function.Surjective p.flip)] in
lemma IsFaceOf.FG.subdual_subdual (hC : C.FG) (hF : F.IsFaceOf C) :
    subdual p.flip (dual p C) (subdual p C F) = F := by
  repeat rw [subdual_def]
  rw [FG.dual_flip_dual p hC]
  rw [← dual_span_lineal_dual]
  rw [Submodule.coe_inf, Submodule.coe_restrictScalars]
  nth_rw 3 [← PointedCone.coe_ofSubmodule]
  rw [DualFG.dual_inf_dual_sup_dual ?_ ?_]
  · rw [Submodule.coe_restrictScalars, dual_eq_submodule_dual]
    rw [FG.dual_flip_dual p hC]
    nth_rw 2 [← Submodule.dual_span]
    rw [Submodule.dual_flip_dual p]
    have H : (C ⊔ F.linSpan).lineal = F.linSpan := by
      sorry
    rw [H]
    exact hF.inf_span
  · simpa using FG.dual_dualfg _ hC
  · rw [LinearMap.flip_flip, coe_dualfg_iff, ← Submodule.dual_span]
    exact Submodule.FG.dual_dualfg _ (FG.span_fg <| IsFaceOf.fg hC hF)

open Module in
/-- Every face of an FG cone is exposed. -/
lemma IsFaceOf.FG.exposed (hC : C.FG) (hF : F.IsFaceOf C) :
    F.IsExposedFaceOf C := by
  wlog _ : Module.Finite R M with exposed -- reduction to finite dimensional case
  · let S : Submodule R M := .span R C
    have H := exposed (FG.restrict_fg S hC) (IsFaceOf.restrict S hF)
      (Finite.iff_fg.mpr <| FG.span_fg hC)
    have hC : C ≤ Submodule.span R (C : Set M) := Submodule.le_span
    simpa [S, hC, le_trans hF.le hC] using H.embed
  rw [← FG.dual_flip_dual (Dual.eval R M) hC]
  rw [← subdual_subdual (Dual.eval R M) hC hF]
  exact .subdual_dual _ <| .subdual_dual _ hF

end exposed
end Field

section DivisionRing

variable {R : Type*} [DivisionRing R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {C : PointedCone R M}


set_option backward.isDefEq.respectTransparency false in
open Submodule in
/-- If a point `x` does not lie in a cone `C` but together with `C` spans a salient cone, then
  `x` spans a face of `hull R (C ∪ {x})`. -/
lemma span_singleton_isFaceOf_sup_singleton_of_not_mem {C : PointedCone R M} {x : M}
    (hx : x ∉ C) (hC : (C ⊔ hull R {x}).Salient) : (hull R {x}).IsFaceOf (C ⊔ hull R {x}) := by
  rw [isFaceOf_iff_mem_of_add_mem]
  constructor
  · exact le_sup_right
  intro y z hy hz hyz
  simp only [mem_sup, mem_span_singleton, Subtype.exists, Nonneg.mk_smul, exists_prop,
    exists_exists_and_eq_and] at *
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
  · set C' := C ⊔ hull R {x}
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
lemma exists_ray' {s : Finset M} (hs : ∃ x ∈ s, x ≠ 0) (hsal : (hull R (s : Set M)).Salient) :
    ∃ x ∈ s, x ≠ 0 ∧ (hull R {x}).IsFaceOf (hull R s) := by classical
  induction s using Finset.induction with
  | empty => absurd hs; simp
  | insert w s hwr hind =>
    by_cases h : w ∈ hull R s
    · by_cases hs' : ∃ x ∈ s, x ≠ 0
      · simp only [coe_insert, hull, span_insert_eq_span h] at ⊢ hsal
        obtain ⟨x, hxs, hx⟩ := hind hs' hsal
        exact ⟨x, by simp [hxs, hx]⟩
      push Not at hs'
      have hs' : ∀ x ∈ (s : Set M), x = 0 := fun x hx => hs' x hx
      simp only [Submodule.span_eq_bot.mpr hs', mem_bot] at h
      obtain ⟨x, hx, h⟩ := hs
      rcases mem_insert.mp hx with hx | hx
      · rw [hx] at h; contradiction
      · specialize hs' x hx; contradiction
    · use w
      simp_rw [← union_singleton, coe_union, span_union, coe_singleton, union_singleton,
        mem_insert, true_or, true_and] at ⊢ hsal
      exact ⟨by by_contra H; absurd h; simp [H],
        span_singleton_isFaceOf_sup_singleton_of_not_mem h hsal⟩

namespace FG

/-- A non-bottom salient FG cone has a ray face. -/
lemma exists_ray (hfg : C.FG) (hC : C ≠ ⊥) (hsal : C.Salient) :
    ∃ x : M, x ≠ 0 ∧ (hull R {x}).IsFaceOf C := by
  obtain ⟨s, rfl⟩ := hfg
  have h : ∃ x ∈ s, x ≠ 0 := by
    by_contra h
    simp [h] at hC
  obtain ⟨_, hx⟩ := exists_ray' h hsal
  exact ⟨_, hx.2⟩

end FG

end DivisionRing

section Field

variable {R : Type*} [Field R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {C : PointedCone R M}

lemma Face.rank_one_of_atom (hfg : C.FG) (hsal : C.Salient)
    (F : Face C) (hF : IsAtom F) : F.rank = 1 := by
  by_cases! h : F.rank < 1
  · absurd (Face.bot_iff_rank_zero hsal).mp <| Cardinal.lt_one_iff_zero.mp h
    exact hF.ne_bot
  have h1 : (F : PointedCone R M).FG := IsFaceOf.fg hfg F.isFaceOf
  have h2 : (F : PointedCone R M).Salient := IsFaceOf.salient hsal F.isFaceOf
  obtain ⟨x, hx0, hxF⟩ := by
    refine FG.exists_ray h1 (fun h3 ↦ ?_) h2
    replace h : (F : PointedCone R M).rank ≥ 1 := h
    simp [(F : PointedCone R M).bot_iff_rank_zero.mpr h3] at h
  let test : Face C := ⟨PointedCone.hull R {x}, hxF.trans F.isFaceOf⟩
  have t_rank : test.rank = 1 := rank_one_of_ray hx0
  have : test ≤ F := hxF.le
  rcases (IsAtom.le_iff hF).1 this with h | h
  · rw [(bot_iff_rank_zero hsal).2 h] at t_rank
    simp at t_rank
  rw [← h, t_rank]

end Field
end PointedCone
