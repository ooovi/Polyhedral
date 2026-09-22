/-
Copyright (c) 2025 Olivia Röhrig, Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Olivia Röhrig, Martin Winter
-/
module

public import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Face.Dual
public import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Finite.Face.Rank
public import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Finite.MinkowskiWeyl
public import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Ray

/-! This file proves results about faces of finitely generated cones. -/

public section

namespace PointedCone

open Submodule (span)
open Function

variable {R M N : Type*}

section Ring

variable [Ring R] [LinearOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M]

variable {C F : PointedCone R M}

lemma exists_fg_hull_subset_face {s : Finset M} (hF : F.IsFaceOf (hull R s)) :
    ∃ t ⊆ s, hull R t = F := by
  use (s.finite_toSet.inter_of_left F).toFinset
  simp [IsFaceOf.hull_inter_face_hull_inf_face hF]

/-- Faces of FG cones are FG. -/
lemma IsFaceOf.fg (hC : C.FG) (hF : F.IsFaceOf C) : F.FG := by
  obtain ⟨_, rfl⟩ := hC
  obtain ⟨t, _, tt⟩ := exists_fg_hull_subset_face hF
  use t, tt

/-- A finitely generated cone has only finitely many faces. -/
lemma FG.finite_face (hC : C.FG) : Finite (Face C) := by
  obtain ⟨s, rfl⟩ := hC
  let T := {t : {t : Finset M // t ∈ s.powerset} // (hull R (t.1 : Set M)).IsFaceOf (hull R s)}
  let f : T → Face (hull R s) := fun t ↦ ⟨hull R (t.1.1 : Set M), t.2⟩
  apply Finite.of_surjective f
  intro F
  obtain ⟨t, hts, ht⟩ := exists_fg_hull_subset_face F.isFaceOf
  refine ⟨⟨⟨t, Finset.mem_powerset.mpr hts⟩, ?_⟩, ?_⟩
  · simpa [ht] using F.isFaceOf
  · exact Face.toPointedCone_eq_iff.mp ht

end Ring

section Field

variable [Field R] [LinearOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]

variable {p : M →ₗ[R] N →ₗ[R] R}
variable {C F F₁ F₂ : PointedCone R M}

variable (p) [Fact p.SeparatingLeft] in
/-- Farkas lemma for finitely generated cones: for any point `x` not in the hull of a finite set
`s`, there exists a linear functional `φ` separating `x` from `hull R s`. -/
lemma FG.farkas {s : Finset M} {x : M} (h : x ∉ hull R s) :
    ∃ φ : N, p x φ < 0 ∧ ∀ y ∈ s, 0 ≤ p y φ := by
  let ⟨φ, hφ, h⟩ := PointedCone.farkas (FG.dualClosed p ⟨s, rfl⟩) h
  exact ⟨φ, hφ, fun y hy => h y (subset_hull hy)⟩

variable (p) in
/-- The dual of a face of an FG cone is an exposed face. -/
lemma Face.dual_isExposed (hC : C.FG) (F : Face C) : IsExposed (F.dual p) :=
  F.dual_isExposed_of_nonempty_relint p <| relint_nonempty_of_finRank (F.isFaceOf.fg hC).finRank

-- TODO: to what other types of cones does this theorem generalize?
variable (p) [Fact p.SeparatingLeft] in
/-- Face duality is involutive. -/
lemma Face.dual_dual_flip (hC : C.FG) (F : Face C) : (F.dual p).dual_flip p = F := by
  have hspan : (Submodule.span R (F : Set M)).FG := by
    exact FG.span_fg (F.isFaceOf.fg hC)
  rw [← Face.toPointedCone_eq_iff]
  rw [Face.coe_dual_flip]
  rw [show F.dual p = ((F.dual p : PointedCone R N) : Set N) from rfl]
  rw [Face.coe_dual]
  rw [← dual_lineal_eq_submodule_dual]
  rw [← PointedCone.dual_submodule_span]
  rw [Submodule.coe_inf]
  rw [DualFG.dual_inf_dual_sup_dual (FG.dual_dualfg p hC) ?_]
  · rw [FG.dual_flip_dual p hC]
    rw [← dual_coe_coe_eq_dual_coe]
    rw [FG.dual_flip_dual p (FG.coe_fg hspan)]
    rw [show F = ((F : PointedCone R M) : Set M) from rfl]
    rw [IsFaceOf.sup_span_lineal_eq_span F.isFaceOf]
    exact F.isFaceOf.inf_span
  · rw [dual_eq_submodule_dual, coe_dualfg_iff]
    exact Submodule.FG.dual_dualfg p hspan

variable (p) [Fact p.SeparatingLeft] in
/-- Face duality is injective. -/
lemma Face.dual_inj (hC : C.FG) : Function.Injective (Face.dual p : Face C → _) := by
  intro F₁ F₂ h
  rw [← F₁.dual_dual_flip p hC, ← F₂.dual_dual_flip p hC, h]

variable (p) [Fact p.SeparatingLeft] in
/-- Face duality is antitone. -/
lemma Face.dual_antitone_iff (hC : C.FG) (F₁ F₂ : Face C) :
    F₁.dual p ≤ F₂.dual p ↔ F₂ ≤ F₁ where
  mpr h := dual_antitone p h
  mp h := by
    rw [← F₂.dual_dual_flip p hC, ← F₁.dual_dual_flip p hC]
    exact dual_flip_antitone p h

-- This proof is, to large parts, AI generated.
open Module in
/-- Every face of an FG cone is exposed. -/
lemma IsFaceOf.FG.isExposedFaceOf (hC : C.FG) (hF : F.IsFaceOf C) :
    F.IsExposedFaceOf C := by
  wlog _ : Module.Finite R M with exposed -- reduction to finite dimensional case
  · let S : Submodule R M := .span R C
    have H := exposed (FG.restrict_fg S hC) (IsFaceOf.restrict S hF)
      (Finite.iff_fg.mpr <| FG.span_fg hC)
    have hC : C ≤ Submodule.span R (C : Set M) := Submodule.le_span
    simpa [S, hC, le_trans hF.le hC] using H.embed
  let F' : Face C := ⟨F, hF⟩
  have H := Face.dual_isExposed .id (FG.dual_fg (Dual.eval R M) hC) (F'.dual (Dual.eval R M))
  change ((F'.dual (Dual.eval R M)).dual (Dual.eval R M).flip : PointedCone R M).IsExposedFaceOf
    (dual (Dual.eval R M).flip (dual (Dual.eval R M) C)) at H
  rw [Face.coe_dual] at H
  rw [FG.dual_flip_dual (Dual.eval R M) hC] at H
  have hFF : C ⊓
      (.dual (Dual.eval R M).flip (F'.dual (Dual.eval R M)) : Submodule R M) = F := by
    rw [← Face.coe_dual_flip]
    exact congrArg (fun G : Face C ↦ (G : PointedCone R M))
      (F'.dual_dual_flip (Dual.eval R M) hC)
  rw [hFF] at H
  exact H

/-- The lineality space of a finitely generated cone is an exposed face. -/
lemma IsExposedFaceOf.lineal (hC : C.FG) : IsExposedFaceOf C.lineal C := by
  apply IsFaceOf.FG.isExposedFaceOf hC (IsFaceOf.lineal C)

end Field

section DivisionRing

variable [DivisionRing R] [LinearOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M]

variable {C : PointedCone R M}

-- TODO: this is the better version of `PointedCone.smul_mem_iff` and should replace it.
lemma smul_mem_iff' {𝕜 M : Type*} [DivisionRing 𝕜] [LinearOrder 𝕜] [IsOrderedRing 𝕜]
    [AddCommMonoid M] [Module 𝕜 M] (C : PointedCone 𝕜 M)
    {c : 𝕜} (hc : 0 < c) {x : M} : c • x ∈ C ↔ x ∈ C :=
  ⟨fun h => inv_smul_smul₀ hc.ne' x ▸ C.smul_mem (inv_pos.2 hc).le h, C.smul_mem hc.le⟩

open Submodule in
/-- If a point `x` does not lie in a cone `C` but together with `C` spans a salient cone, then
  `x` spans a face of `hull R (C ∪ {x})`. -/
lemma span_singleton_isFaceOf_sup_singleton_of_not_mem {C : PointedCone R M} {x : M}
    (hx : x ∉ C) (hC : (C ⊔ (R ∙₊ x)).Salient) : (R ∙₊ x).IsFaceOf (C ⊔ (R ∙₊ x)) := by
  apply IsFaceOf.of_mem_of_add_mem_left
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
  · set C' := C ⊔ (R ∙₊ x)
    have hxC' : x ∈ C' := by
      simpa [C', mem_sup, mem_span_singleton] using ⟨0, by simp, 1, by simp⟩
    have hxC' : -t • x ∈ C' := C'.smul_mem (neg_nonneg.mpr ht) hxC'
    rw [neg_smul] at hxC'
    have hCC' : C ≤ C' := by simp [C']
    rw [salient_iff_forall_mem_eq_zero_of_neg_mem] at hC
    have h0 := hC _ (hCC' h) hxC'
    rw [h0, Eq.comm, add_eq_zero_iff_eq_neg] at hyz
    rw [hyz] at hy'
    have h0' := hC _ (hCC' hz') (hCC' hy')
    simp [h0'] at hyz
    simp [hyz] at hy
    use a
  · rw [smul_mem_iff' C ht] at h
    contradiction

open Finset Submodule in
lemma exists_ray' {s : Finset M} (hs : ∃ x ∈ s, x ≠ 0) (hsal : (hull R (s : Set M)).Salient) :
    ∃ x ∈ s, x ≠ 0 ∧ (R ∙₊ x).IsFaceOf (hull R s) := by classical
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
    ∃ x : M, x ≠ 0 ∧ (R ∙₊ x).IsFaceOf C := by
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
  · absurd (Face.bot_iff_rank_zero hsal).mp <| Cardinal.lt_one_iff.mp h
    exact hF.ne_bot
  have h1 : (F : PointedCone R M).FG := IsFaceOf.fg hfg F.isFaceOf
  have h2 : (F : PointedCone R M).Salient := IsFaceOf.salient hsal F.isFaceOf
  obtain ⟨x, hx0, hxF⟩ := by
    refine FG.exists_ray h1 (fun h3 ↦ ?_) h2
    replace h : (F : PointedCone R M).rank ≥ 1 := h
    simp [(F : PointedCone R M).bot_iff_rank_zero.mpr h3] at h
  let test : Face C := ⟨R ∙₊ x, hxF.trans F.isFaceOf⟩
  have t_rank : test.rank = 1 := rank_one_of_ray hx0
  have : test ≤ F := hxF.le
  rcases (IsAtom.le_iff hF).1 this with h | h
  · rw [(bot_iff_rank_zero hsal).2 h] at t_rank
    simp at t_rank
  rw [← h, t_rank]

end Field

end PointedCone
