/-
Copyright (c) 2025 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/
module

public import Polyhedral.Mathlib.Algebra.Module.Submodule.Dual.DualClosed
public import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Dual
public import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Rank

/-! This file defines dual closed cones, that is, cones that are identical to their
double dual.

Main definition:
* `DualClosed p C` states that `dual p.flip (dual p C) = C`.
 -/

public section

namespace PointedCone

open Function Module LinearMap Pointwise
open Submodule (span)

variable {R M N : Type*}

section CommRing

variable [CommRing R] [PartialOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]

variable {C D : PointedCone R M}
variable {p : M →ₗ[R] N →ₗ[R] R}

variable (p) in
/-- A cone is dual closed if it is identical to its double dual. -/
abbrev DualClosed (C : PointedCone R M) := dual p.flip (dual p C) = C

variable (p) in
@[simp] lemma DualClosed.def (hC : DualClosed p C) :
     dual p.flip (dual p C) = C := hC

variable (p) in
@[simp] lemma DualClosed.def_flip {C : PointedCone R N} (hC : DualClosed p.flip C) :
     dual p (dual p.flip C) = C := hC

lemma DualClosed.def_iff : DualClosed p C ↔ dual p.flip (dual p C) = C := by rfl

lemma DualClosed.def_flip_iff {C : PointedCone R N} :
    DualClosed p.flip C ↔ dual p (dual p.flip C) = C := by rfl

@[simp] lemma DualClosed.coe_iff {S : Submodule R M} :
    DualClosed p S ↔ S.DualClosed p := by
  change dual p.flip (dual p S) = S ↔ _
  rw [dual_eq_submodule_dual p S, dual_coe_coe_eq_dual_coe, dual_eq_submodule_dual p.flip]
  exact ofSubmodule_inj

lemma dualClosed_coe {S : Submodule R M} (hS : S.DualClosed p) :
    DualClosed p S := DualClosed.coe_iff.mpr hS

lemma dualClosed_coe' {S : Submodule R M} (hS : DualClosed p S) :
    S.DualClosed p := DualClosed.coe_iff.mp hS

variable (p) in
lemma dual_dualClosed (C : PointedCone R M) : (dual p C).DualClosed p.flip := by
  simp [DualClosed, dual_dual_flip_dual]

variable (p) in
lemma dual_flip_DualClosed (C : PointedCone R N) : (dual p.flip C).DualClosed p
    := dual_dualClosed p.flip C

lemma DualClosed.dual_inj (hC : C.DualClosed p) (hD : D.DualClosed p)
    (hCD : dual p C = dual p D) : C = D := by
  rw [← hC, ← hD, hCD]

@[simp] lemma DualClosed.dual_inj_iff (hC : C.DualClosed p)
    (hD : D.DualClosed p) : dual p C = dual p D ↔ C = D := ⟨dual_inj hC hD, by intro h; congr ⟩

lemma DualClosed.exists_of_dual_flip (hC : C.DualClosed p) :
    ∃ D : PointedCone R N, D.DualClosed p.flip ∧ dual p.flip D = C
  := ⟨dual p C, by simp [DualClosed, hC.def]⟩

lemma DualClosed.exists_of_dual {C : PointedCone R N} (hC : C.DualClosed p.flip) :
    ∃ D : PointedCone R M, D.DualClosed p ∧ dual p D = C
  := hC.exists_of_dual_flip

lemma DualClosed.inf (hS : C.DualClosed p) (hT : D.DualClosed p) :
    (C ⊓ D).DualClosed p := by
  rw [← hS, ← hT, ← dual_sup_dual_inf_dual, DualClosed, dual_flip_dual_dual_flip]

theorem DualClosed.eq_sInf (hC : C.DualClosed p) :
    C = sInf { D : PointedCone R M | D.DualClosed p ∧ C ≤ D } := by
  rw [Eq.comm, le_antisymm_iff]
  constructor
  · exact sInf_le ⟨hC, by simp⟩
  simp only [SetLike.le_def, Submodule.mem_sInf, Set.mem_ofPred_eq, and_imp]
  intro x hx D hD hsD
  rw [← hD]; rw [← hC] at hx
  exact (dual_dual_mono p hsD) hx

lemma DualClosed.dual_le_of_dual_le {D : PointedCone R N} (hC : C.DualClosed p)
    (hCD : dual p C ≤ D) : dual p.flip D ≤ C := by
  rw [← hC]; exact dual_antitone hCD

-- NOTE: This is the characterizing property of an antitone GaloisConnection.
lemma dual_le_iff_dual_le_of_dualClosed {D : PointedCone R N} (hC : C.DualClosed p)
    (hD : D.DualClosed p.flip) : dual p C ≤ D ↔ dual p.flip D ≤ C :=
  ⟨hC.dual_le_of_dual_le, hD.dual_le_of_dual_le⟩

variable (p) in
lemma dual_dual_eval_le_dual_dual_bilin (s : Set M) :
    dual .id (dual (Dual.eval R M) s) ≤ dual p.flip (dual p s) :=
  fun _ hx y hy => @hx (p.flip y) hy

lemma DualClosed.to_eval {S : PointedCone R M} (hS : S.DualClosed p) :
    S.DualClosed (Dual.eval R M) := by
  have h := dual_dual_eval_le_dual_dual_bilin p S
  rw [hS] at h
  exact le_antisymm h subset_dual_dual

lemma DualClosed.neg {C : PointedCone R M} (hC : C.DualClosed p) : (-C).DualClosed p := by
  unfold DualClosed
  repeat rw [Submodule.coe_set_neg, dual_neg]
  rw [hC]

lemma dual_inf_dual_sup_dual_of_dualClosed (C D : PointedCone R M)
    (hC : C.DualClosed p) (hD : D.DualClosed p) (hCD : (dual p C ⊔ dual p D).DualClosed p.flip) :
      dual p (C ⊓ D) = dual p C ⊔ dual p D := by
  change dual p (C ∩ D) = _ -- don't we have a theorem for this?
  nth_rw 1 [← hC, ← hD, ← Submodule.coe_inf, ← dual_sup_dual_inf_dual]
  exact hCD

lemma dual_inf_eq_sup_dual_iff_dualClosed (hC : C.DualClosed p) (hD : D.DualClosed p) :
    (dual p C ⊔ dual p D).DualClosed p.flip ↔ dual p (C ⊓ D) = dual p C ⊔ dual p D :=
  ⟨dual_inf_dual_sup_dual_of_dualClosed C D hC hD, fun h => h ▸ dual_dualClosed p (C ⊓ D)⟩

end CommRing

section LinearOrder

variable [CommRing R] [LinearOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]

variable {C D : PointedCone R M}
variable {p : M →ₗ[R] N →ₗ[R] R}

lemma DualClosed.lineal (hC : C.DualClosed p) : C.lineal.DualClosed p := by
  rw [← coe_iff, ofSubmodule_lineal]
  exact DualClosed.inf hC hC.neg

/- WARNING: `C` being dual closed does *not* imply that `span R C` is dual closed! Not even
over ℝ or with a separating pairing!

But see `DualClosed.span_dualClosed` which assumes `FinSalRank`.
-/

-- # FARKAS

/- Separation lemma for dual closed cones. -/
lemma exists_pos_forall_nonneg_of_not_mem (hC : C.DualClosed p)
    {x : M} (hx : x ∉ C) : ∃ φ : N, p x φ < 0 ∧ ∀ y ∈ C, 0 ≤ p y φ := by
  rw [← hC] at hx
  simp only [mem_dual, SetLike.mem_coe, flip_apply, not_forall, not_le] at hx
  obtain ⟨φ, _, _⟩ := hx
  use φ

alias farkas := exists_pos_forall_nonneg_of_not_mem

/-- The dual of a cone being ⊥ is equivalent to all non-zero linear forms
  attaining negative values on the cone. -/
lemma dual_eq_bot_iff_forall_eq_zero_or_exists_neg :
    dual p C = ⊥ ↔ ∀ φ : N, φ = 0 ∨ ∃ x ∈ C, p x φ < 0 := by
  simp only [SetLike.ext_iff, mem_dual, SetLike.mem_coe, Submodule.mem_bot]
  constructor <;> intro h φ
  · by_cases hφ : φ = 0
    · left; exact hφ
    · replace h := (h φ).mp.mt hφ
      push Not at h
      right; exact h
  · constructor
    · intro h'
      rcases h φ
      · assumption
      · absurd h'
        push Not
        assumption
    · simp +contextual

-- /-- The dual of a cone being ⊥ is equivalent to all non-zero linear forms
--   attaining negative values on the cone. -/
-- lemma dual_eq_bot_iff_forall_eq_zero_or_exists_neg' {C : PointedCone R M} :
--     dual p C ≠ ⊥ ↔ ∃ φ : N, φ ≠ 0 ∧ ∀ x ∈ C, 0 ≤ p x φ := by
--   simp only [SetLike.ext_iff, mem_dual, SetLike.mem_coe, Submodule.mem_bot]
--   constructor <;> intro h φ
--   · by_cases hφ : φ = 0
--     · left; exact hφ
--     · replace h := (h φ).mp.mt hφ
--       push_neg at h
--       right; exact h
--   · constructor
--     · intro h'
--       rcases h φ
--       · assumption
--       · absurd h'
--         push_neg
--         assumption
--     · simp +contextual

/-- The double dual of a cone being ⊤ is equivalent to every non-zero linear
  form attaining a negative value on the cone. In infinite dimensional vector spaces
  there exists such cones other than ⊤ itself (e.g. the lexicographic cone). -/
lemma dual_dual_eq_top_iff_exists_ne_zero_forall_nonneg :
    dual p.flip (dual p C) ≠ ⊤ ↔ ∃ φ : N, p.flip φ ≠ 0 ∧ ∀ x ∈ C, 0 ≤ p x φ := by
  constructor <;> intro h
  · obtain ⟨x, hx⟩ := SetLike.exists_not_mem_of_ne_top _ h
    obtain ⟨φ, hxφ, hφ⟩ := farkas (dual_dualClosed _ _) hx
    use φ
    constructor
    · by_contra hφ
      rw [flip_apply] at hxφ
      simp [hφ] at hxφ
    exact fun y hy => hφ y (subset_dual_dual hy)
  · obtain ⟨φ, h0φ, hφ⟩ := h
    by_contra h
    rw [dual_top_iff_le_ker] at h
    have := h hφ
    contradiction

lemma exists_ne_zero_forall_nonneg_of_dualClosed_ne_top
    (hC : C.DualClosed p) (h : C ≠ ⊤) : ∃ φ : N, p.flip φ ≠ 0 ∧ ∀ x ∈ C, 0 ≤ p x φ := by
  simp [← dual_dual_eq_top_iff_exists_ne_zero_forall_nonneg, hC, h]


end LinearOrder

section Field

variable [Field R] [LinearOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]

variable {C D : PointedCone R M}
variable {p : M →ₗ[R] N →ₗ[R] R}

-- Q: Do we need Field?
-- /-- For a dual closed cone, the dual of the lineality space is the submodule span of the dual. -/
-- lemma DualClosed.dual_lineal_span_dual {C : PointedCone R M} (hC : C.DualClosed p) :
--     Submodule.dual p C.lineal = Submodule.span R (dual p C) := by
--   rw [Eq.comm, le_antisymm_iff]
--   constructor
--   · exact span_dual_le_dual_lineal
--   simp only [lineal, Submodule.dual_sSup_sInf_dual]
--   have hh := (dual_dualClosed p C).submodule_span_dualClosed
--   rw [hh.eq_sInf]
--   --rw [submodule_span_dual]
--   refine sInf_le_sInf ?_
--   intro T
--   simp only [Set.mem_image, Set.mem_ofPred_eq, exists_exists_and_eq_and]
--   intro ⟨hdc, h⟩
--   use Submodule.dual p.flip T
--   constructor
--   · rw [← hC, ← dual_eq_submodule_dual]
--     exact dual_antitone h  -- (le_trans dual_le_submodule_dual h)
--   · exact hdc
--
-- variable [Fact (Surjective p)] in
-- /-- For a dual closed cone, the dual of the lineality space is the submodule span of the dual. -/
-- lemma DualClosed.dual_lineal_span_dual'' {C : PointedCone R M} (hC : C.DualClosed p) :
--     Submodule.dual p C.lineal = Submodule.span R (dual p C) := by
--   simp only [lineal, Submodule.dual_sSup_sInf_dual]
--   unfold Submodule.span
--   congr; ext T
--   simp only [Set.mem_image, Set.mem_ofPred_eq, exists_exists_and_eq_and]
--   constructor
--   · intro h -- this direction needs neither Field nor dual closed
--     obtain ⟨S, hSC, hS⟩ := h
--     rw [← hS]
--     nth_rw 3 [← ofSubmodule_coe]
--     rw [SetLike.coe_subset_coe, ← dual_eq_submodule_dual]
--     exact dual_le_dual hSC
--   · intro h -- this direction needs Field and dual closed; maybe not Field
--     use Submodule.dual p.flip T
--     constructor
--     · rw [← hC, ← dual_eq_submodule_dual]
--       exact dual_antitone h
--     · exact T.dualClosed p.flip
--
-- variable [Fact (Surjective p)] in
-- /-- For a dual closed cone, the dual of the submodule span is the lineality space of the dual. -/
-- lemma DualClosed.dual_span_lineal_dual {C : PointedCone R M} (hC : C.DualClosed p) :
--     .dual p (Submodule.span R (C : Set M)) = (dual p C).lineal := by
--   have h := hC.dual_lineal_span_dual.symm
--   obtain ⟨D, hD, rfl⟩ := hC.exists_of_dual_flip
--   --rw [DualClosed, flip_flip] at hD
--   rw [hD.def_flip] at *
--   simp at *
--   sorry

lemma DualClosed.dual_dual_lineal (hC : C.DualClosed p) :
    (dual p.flip (dual p C)).lineal = .dual p.flip (Submodule.dual p C.lineal) := by
  sorry

variable (p) [Fact (Surjective p.flip)] in
/-- Every submodule of a vector space is dual closed. -/
lemma dualClosed (S : Submodule R M) : DualClosed p S :=
    dualClosed_coe <| S.dualClosed p

/-- If a cone has dual closed lineality and has finite salient rank, then its span is
also dual closed. -/
lemma DualClosed.span_dualClosed_of_dualClosed_lineal (hC : C.lineal.DualClosed p)
    (h : C.FinSalRank) : (span R C).DualClosed p := by
  obtain ⟨D, hD, hCD⟩ := h.exists_finRank_sup_lineal
  rw [hCD, ← coe_sup_submodule_span, Submodule.span_union, coe_ofSubmodule,
    Submodule.span_eq C.lineal]
  simpa [sup_comm] using Submodule.DualClosed.sup_fg hC hD

/-- If a cone is dual closed and has finite salient rank, then its span is also dual closed. -/
lemma DualClosed.span_dualClosed (hC : C.DualClosed p)
    (h : C.FinSalRank) : (span R C).DualClosed p :=
  span_dualClosed_of_dualClosed_lineal hC.lineal h

/-- For a dual closed cone of finite salient rank, the span of the double dual cone is the
double dual of the span.

The finite rank assumption cannot be dropped: as the warning above explains, the span of a dual
closed cone need not be dual closed. For example, for `M = N = ℓ²(ℝ)` with the inner product
pairing, the closed cone generated by `{e 1} ∪ {e 1 + √n • e n | n ∈ ℕ}` is dual closed while
its span is a proper dense subspace. -/
lemma DualClosed.dual_dual_span (hC : C.DualClosed p) (hfin : C.FinSalRank) :
    span R (dual p.flip (dual p C)) = .dual p.flip (Submodule.dual p (span R (C : Set M))) := by
  rw [hC, hC.span_dualClosed hfin]

end Field

end PointedCone
