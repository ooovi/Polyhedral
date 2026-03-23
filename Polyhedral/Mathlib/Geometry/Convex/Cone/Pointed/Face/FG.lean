import Mathlib.Order.Grade
import Mathlib.LinearAlgebra.Quotient.Basic

import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Face.Exposed
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Face.Rank
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Ray

namespace PointedCone

section DivisionRingLemmas

variable {R : Type*} [DivisionRing R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {C F : PointedCone R M}

lemma exists_fg_span_subset_face {s : Finset M} (hF : F.IsFaceOf (span R s)) :
    ∃ t ⊆ s, span R t = F := by
  use (s.finite_toSet.inter_of_left F).toFinset
  simp [IsFaceOf.span_inter_face_span_inf_face hF]

/-- Faces of FG cones are FG. -/
lemma IsFaceOf.fg (hC : C.FG) (hF : F.IsFaceOf C) : F.FG := by
  obtain ⟨_, rfl⟩ := hC
  let ⟨t, _, tt⟩ := exists_fg_span_subset_face hF
  use t, tt

end DivisionRingLemmas

section Field

variable {R : Type*} [Field R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}

/- Farkas lemma for finitely generated cones: for any point `x` not in the span of a finite set `s`,
  there exists a hyperplane `φ` separating `x` from `span R s`. -/
variable (p) [Fact p.SeparatingLeft] in
lemma FG.farkas {s : Finset M} {x : M} (h : x ∉ span R s) :
    ∃ φ : N, 0 > p x φ ∧ ∀ y ∈ s, 0 ≤ p y φ := by
  let ⟨φ, hφ, h⟩ := PointedCone.farkas (FG.isDualClosed p ⟨s, rfl⟩) h
  exact ⟨φ, hφ, fun y hy => h y (subset_span hy)⟩

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
    exact Submodule.FG.dual_fgdual _ (FG.linSpan_fg <| IsFaceOf.fg hC hF)

open Module in
/-- Every face of an FG cone is exposed. -/
lemma IsFaceOf.FG.exposed (hC : C.FG) (hF : F.IsFaceOf C) :
    F.IsExposedFaceOf C := by
  wlog _ : Module.Finite R M with exposed -- reduction to finite dimensional case
  · let S : Submodule R M := .span R C
    have H := exposed (FG.restrict_fg S hC) (IsFaceOf.restrict S hF)
      (Finite.iff_fg.mpr <| FG.linSpan_fg hC)
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


open Submodule in
/-- If a point `x` does not lie in a cone `C` but together with `C` spans a salient cone, then
  `x` spans a face of `span R (C ∪ {x})`. -/
lemma span_singleton_isFaceOf_sup_singleton_of_not_mem {C : PointedCone R M} {x : M}
    (hx : x ∉ C) (hC : (C ⊔ span R {x}).Salient) : (span R {x}).IsFaceOf (C ⊔ span R {x}) := by
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
    ∃ x : M, x ≠ 0 ∧ (span R {x}).IsFaceOf C := by
  obtain ⟨s, rfl⟩ := hfg
  have h : ∃ x ∈ s, x ≠ 0 := by
    by_contra h
    simp [h] at hC
  obtain ⟨_, hx⟩ := exists_ray' h hsal
  exact ⟨_, hx.2⟩

open Submodule in
lemma finrank_strictMono (hCfg : C.FG) :
    StrictMono (fun F : Face C => F.finrank) := by
  intro G F hFG
  haveI := (Submodule.fg_iff_finiteDimensional _).mp (FG.linSpan_fg <| F.isFaceOf.fg hCfg)
  apply finrank_lt_finrank_of_lt (lt_of_le_of_ne ?_ ?_)
  · exact span_mono (R := R) hFG.le
  · intro h
    have : G.toSubmodule < F.toSubmodule := gt_iff_lt.mp hFG
    rw [← IsFaceOf.inf_linSpan F.isFaceOf, ← IsFaceOf.inf_linSpan G.isFaceOf] at this
    simp [linSpan, h] at this

lemma finrank_add_one (hCfg : C.FG)
    {F G : Face C} (hFG : F ⋖ G) :
    G.finrank = F.finrank + 1 := by
  obtain ⟨hfg, hc⟩ := hFG
  -- suffices to show quotient has rank 1
  have hgfg := quot_fg (G.isFaceOf.fg hCfg) F.linSpan
  convert
    finrank_eq_finrank_add_finrank_quot_linSpan (FG.linSpan_fg (G.isFaceOf.fg hCfg)) hfg.le
    -- G/F has a ray
  have FfG : (F : PointedCone R M).IsFaceOf G := (G.isFaceOf.isFaceOf_iff.mpr ⟨hfg.le, F.isFaceOf⟩)
  have : ¬(G : PointedCone R M) ≤ F.linSpan := by
    simpa [Face.le_linSpan_iff_le] using not_le_of_gt hfg
  obtain ⟨v, hv0, hvray⟩ :=
    FG.exists_ray hgfg ((PointedCone.quot_eq_bot_iff _ _).not.mpr this) FfG.quot_salient
  set ray : Face (quot G.toSubmodule F.linSpan) := ⟨span R {v}, hvray⟩
  -- pull ray back to get face of G with F < H
  let H := ray.fiberFace (F := ⟨_, FfG⟩)
  have : F < H := by
    apply lt_of_le_of_ne (ray.le_fiber (F := ⟨_, FfG⟩))
    intro ha
    have ugh : span R {v} = ⊥ := (Face.fiberFace_eq_iff _).mp ha
    have : v ∈ span R {v} := Submodule.mem_span_singleton_self v
    rw [ugh] at this
    exact hv0 <| (AddOpposite.op_eq_zero_iff v).mp (congrArg AddOpposite.op this)
  -- must be G = H because of covering
  simp only [← eq_of_le_of_not_lt H.isFaceOf.le <| hc this]
  rw [← PointedCone.finrank_one_of_ray (R := R) hv0]
  congr; ext x; constructor
  · intro hx
    obtain ⟨x', hx', rfl⟩ := hvray.le hx
    exact ⟨x', ⟨hx', hx⟩, rfl⟩
  · rintro ⟨_, ⟨_, hhx'⟩, rfl⟩
    exact mem_toConvexCone.mp hhx'

lemma finrank_covBy (hCfg : C.FG)
    {F G : Face C} (hFG : F ⋖ G) :
    F.finrank ⋖ G.finrank := by
  obtain ⟨hfg, hc⟩ := hFG
  refine ⟨finrank_strictMono hCfg hfg, ?_⟩
  suffices G.finrank = F.finrank + 1 by omega
  exact (FG.finrank_add_one hCfg ⟨hfg, hc⟩)

lemma covBy_iff_finrank_covBy_of_le (hCfg : C.FG)
    {F G : Face C} (hfg : F ≤ G) : F ⋖ G ↔
    F.finrank ⋖ G.finrank := by
  refine ⟨finrank_covBy hCfg, ?_⟩
  intro h
  constructor
  · exact lt_of_le_of_ne hfg <| fun a => ne_of_lt h.1 (congrArg finrank (by simpa))
  · exact fun H hH hah => h.2 (finrank_strictMono hCfg hH) (finrank_strictMono hCfg hah)

/-- The face lattice of a finitely generated cone is graded by face dimension. -/
noncomputable instance gradeOrder_finrank {C : PointedCone R M}
    (hCfg : C.FG) : GradeOrder ℕ (Face C) where
  grade F := F.finrank
  grade_strictMono := finrank_strictMono hCfg
  covBy_grade := fun {_ _} hFG => finrank_covBy hCfg hFG

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
  let test : Face C := ⟨PointedCone.span R {x}, hxF.trans F.isFaceOf⟩
  have t_rank : test.rank = 1 := rank_one_of_ray hx0
  have : test ≤ F := hxF.le
  rcases (IsAtom.le_iff hF).1 this with h | h
  · rw [(bot_iff_rank_zero hsal).2 h] at t_rank
    simp at t_rank
  rw [← h, t_rank]

end Field
end PointedCone
