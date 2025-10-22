/-
Copyright (c) 2025 Justus Springer, Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer, Martin Winter
-/

import Polyhedral.Mathlib.Algebra.Module.Submodule.FG
import Polyhedral.Mathlib.Algebra.Module.Submodule.CoFG

open Function Module LinearMap

variable {𝕜 M N : Type*}

namespace Submodule

section LinearOrder

variable [Field 𝕜] [AddCommGroup M] [AddCommGroup N]
  [Module 𝕜 M] [Module 𝕜 N] {p : M →ₗ[𝕜] N →ₗ[𝕜] 𝕜}

/-- The union of an FG cone and a CoFG cone is CoFG. -/
lemma sup_cofg_submodule (S : Submodule 𝕜 N) {T : Submodule 𝕜 N} (hT : T.CoFG p) : (S ⊔ T).CoFG p
    := by classical
  sorry

/-- The union of an FG cone and a CoFG cone is CoFG. -/
lemma sup_fg_cofg {S T : Submodule 𝕜 N} (hS : S.FG) (hT : T.CoFG p) : (S ⊔ T).CoFG p
    := by classical
  obtain ⟨s, rfl⟩ := hS
  induction s using Finset.induction with
  | empty => simp [hT]
  | insert w s hws hs =>
    obtain ⟨t, ht⟩ := hs
    use (auxGenSet p t.toSet w).toFinset
    simp [span_insert, sup_assoc, ← ht]
    exact dual_auxGenSet t.finite_toSet

lemma sup_cofg_fg {C D : Submodule 𝕜 N} (hC : C.CoFG p) (hD : D.FG) : (C ⊔ D).CoFG p
    := by rw [sup_comm]; exact sup_fg_cofg hD hC

variable (p) [Fact p.IsFaithfulPair] in
/-- An FG cone can be written as the intersection of a CoFG cone and an FG submodule. -/
lemma FG.exists_cofg_inf_submodule {C : Submodule 𝕜 N} (hC : C.FG)
    {S : Submodule 𝕜 N} (hS : S.FG) (hCS : C ≤ S) :
      ∃ D : Submodule 𝕜 N, D.CoFG p ∧ D ⊓ S = C := by
  wlog hC' : C = ⊥ with h
  · specialize h p fg_bot hS bot_le rfl
    obtain ⟨D, hcofg, hD⟩ := h
    exact ⟨_, sup_fg_cofg hC hcofg, by simp [← sup_inf_assoc_of_le_submodule D hCS, hD]⟩
  · obtain ⟨D, hcofg, hD⟩ := hS.exists_cofg_inf_bot p
    exact ⟨_, coe_cofg_iff.mpr hcofg, by simp [← restrictScalars_inf, inf_comm, hD, hC']⟩

variable (p) [Fact p.IsFaithfulPair] in
/-- An FG cone can be written as the intersection of its linear span with a CoFG cone. -/
lemma FG.exists_cofg_inf_span {C : Submodule 𝕜 N} (hC : C.FG) :
      ∃ D : Submodule 𝕜 N, D.CoFG p ∧ D ⊓ Submodule.span 𝕜 (M := N) C = C :=
  exists_cofg_inf_submodule p hC (span_fg hC) Submodule.subset_span

variable (p) [Fact p.IsFaithfulPair] in
/-- An FG cone can be written as the intersection of a CoFG cone and an FG submodule. -/
lemma FG.exists_cofg_inf_fg_submodule {C : Submodule 𝕜 N} (hC : C.FG) :
      ∃ D : Submodule 𝕜 N, D.CoFG p ∧ ∃ S : Subspace 𝕜 N, S.FG ∧ D ⊓ S = C := by
  obtain ⟨D, hcofg, hD⟩ := exists_cofg_inf_span p hC
  exact ⟨D, hcofg, Submodule.span 𝕜 C, submodule_span_fg hC, hD⟩

variable (p) [Fact p.IsFaithfulPair] in
/-- An FG cone is the dual of a CoFG cone. -/
lemma FG.exists_cofg_flip_dual {C : Submodule 𝕜 N} (hC : C.FG) :
    ∃ D : Submodule 𝕜 M, D.CoFG p.flip ∧ dual p D = C := by
  obtain ⟨D, hD, S, hS, rfl⟩ := exists_cofg_inf_fg_submodule p hC
  obtain ⟨C', hfg, rfl⟩ := hD.exists_fg_dual
  use C' ⊔ dual p.flip S
  constructor
  · exact sup_fg_cofg hfg <| cofg_of_fg p.flip (ofSubmodule_fg_of_fg hS)
  · simp [dual_sup_dual_inf_dual, Submodule.FG.dual_dual_flip hS]
    -- TODO: prove `Submodule.FG.dual_dual_flip` (the equivalent for cones was already proven here).

variable (p) [Fact p.flip.IsFaithfulPair] in
/-- An FG cone is the dual of a CoFG cone. -/
lemma FG.exists_cofg_dual_flip {C : Submodule 𝕜 M} (hC : C.FG) :
    ∃ D : Submodule 𝕜 N, D.CoFG p ∧ dual p.flip D = C := by
  rw [← flip_flip p]; exact exists_cofg_flip_dual p.flip hC

variable (p) [Fact p.IsFaithfulPair] in
/-- The double dual of an FG cone is the cone itself. -/
@[simp]
lemma FG.dual_dual_flip {C : Submodule 𝕜 N} (hC : C.FG) : dual p (dual p.flip C) = C := by
  obtain ⟨D, hcofg, rfl⟩ := exists_cofg_flip_dual p hC
  exact dual_dual_flip_dual (p := p) D

variable (p) [Fact p.flip.IsFaithfulPair] in
/-- The double dual of an FG cone is the cone itself. -/
@[simp]
lemma FG.dual_flip_dual {C : Submodule 𝕜 M} (hC : C.FG) : dual p.flip (dual p C) = C := by
  rw [← flip_flip p]; exact dual_dual_flip p.flip hC

variable (p) [Fact p.flip.IsFaithfulPair] in
lemma FG.isDualClosed {C : Submodule 𝕜 M} (hC : C.FG) : C.IsDualClosed p
    := FG.dual_flip_dual p hC

variable (p) [Fact p.IsFaithfulPair] in
/-- The double dual of a finite set is its span. -/
@[simp]
lemma FG.dual_dual_flip_eq_span (s : Finset N) : dual p (dual p.flip s) = span 𝕜 s := by
  nth_rw 2 [← dual_span]
  exact dual_dual_flip p (fg_span s.finite_toSet)

variable (p) [Fact p.flip.IsFaithfulPair] in
/-- The double dual of a finite set is its span. -/
@[simp]
lemma FG.dual_flip_dual_eq_span (s : Finset M) : dual p.flip (dual p s) = span 𝕜 s := by
  rw [← flip_flip p]; exact dual_dual_flip_eq_span p.flip s

variable (p) [Fact p.IsFaithfulPair] in
lemma FG.dual_flip_inj {C D : Submodule 𝕜 N} (hC : C.FG) (hD : D.FG)
    (h : dual p.flip C = dual p.flip D) : C = D := by
  have h := congrArg (dual p) <| congrArg SetLike.coe h
  rw [dual_dual_flip _ hC, dual_dual_flip _ hD] at h
  exact h

variable (p) [Fact p.flip.IsFaithfulPair] in
lemma FG.dual_inj {C D : Submodule 𝕜 M} (hC : C.FG) (hD : D.FG)
    (h : dual p C = dual p D) : C = D := by
  rw [← flip_flip p] at h; exact dual_flip_inj p.flip hC hD h

variable [Fact p.IsFaithfulPair] in
@[simp] lemma FG.dual_flip_inj_iff {C D : Submodule 𝕜 N} {hC : C.FG} {hD : D.FG} :
    dual p.flip C = dual p.flip D ↔ C = D := ⟨dual_flip_inj p hC hD, by simp +contextual⟩

variable [Fact p.flip.IsFaithfulPair] in
@[simp] lemma FG.dual_inj_iff {C D : Submodule 𝕜 M} {hC : C.FG} {hD : D.FG} :
    dual p C = dual p D ↔ C = D := ⟨dual_inj p hC hD, by simp +contextual⟩

variable [Fact p.IsFaithfulPair] in
/-- The dual of a CoFG cone is FG. -/
lemma CoFG.dual_fg {C : Submodule 𝕜 M} (hC : C.CoFG p.flip) : (dual p C).FG := by
  obtain ⟨D, hfg, rfl⟩ := exists_fg_dual hC
  rw [FG.dual_dual_flip p hfg]
  exact hfg

variable [Fact p.flip.IsFaithfulPair] in
/-- The dual of a CoFG cone is FG. -/
lemma CoFG.dual_flip_fg {C : Submodule 𝕜 N} (hC : C.CoFG p) : (dual p.flip C).FG := by
  rw [← flip_flip p] at hC; exact dual_fg hC

variable [Fact (Surjective p.flip)] in
lemma CoFG.exists_fg_sup_lineal {C : Submodule 𝕜 N} (hC : C.CoFG p) :
    ∃ D : Submodule 𝕜 N, D.FG ∧ D ⊔ C.lineal = C := by
  obtain ⟨C', hcofg, hC'⟩ := FG.exists_cofg_inf_span p.flip hC.dual_flip_fg
  obtain ⟨C'', hfg, rfl⟩ := hcofg.exists_fg_dual
  use C''
  constructor
  · exact hfg
  /- NOTE: this proof does not rely on `p.IsFaithfulPair` because in the next line it uses
    `IsDualClosed.dual_inj_iff` instead of `FG.dual_inj_iff`. It is not clear to me how this
    avoids the assumption. Maybe `IsDualClosed.dual_inj_iff` (or something it relies on) is
    not completely implemented yet. -/
  rw [← IsDualClosed.dual_inj_iff (p := p.flip)]
  · rw [dual_sup_dual_inf_dual, ofSubmodule_coe, coe_dual, IsDualClosed.dual_lineal_span_dual]
    · exact hC'
    · exact hC.isDualClosed_flip
  · exact CoFG.isDualClosed <| sup_fg_cofg hfg (CoFG.coe <| CoFG.lineal_cofg hC)
  · exact hC.isDualClosed_flip

-- Q: is `p.flip.IsFaithfulPair` necessary?
variable [Fact (Surjective p.flip)] in
lemma sup_cofg {C D : Submodule 𝕜 N} (hC : C.CoFG p) (hD : D.CoFG p) : (C ⊔ D).CoFG p := by
  obtain ⟨C', hCfg, hC'⟩ := hC.exists_fg_sup_lineal
  obtain ⟨D', hDfg, hD'⟩ := hD.exists_fg_sup_lineal
  rw [← hC', ← hD', sup_assoc]
  nth_rw 2 [sup_comm]
  rw [sup_assoc, ← sup_assoc]
  refine sup_fg_cofg (sup_fg hCfg hDfg) ?_
  rw [← coe_sup, coe_cofg_iff]
  exact Submodule.sup_cofg hD.lineal_cofg hC.lineal_cofg

-- variable [Fact p.flip.IsFaithfulPair] in
-- lemma inf_cofg_submodule {C : Submodule 𝕜 N} {S : Submodule 𝕜 N} (hC : C.CoFG p) (hS : S.FG) :
--     (C ⊓ S).FG := by
--   obtain ⟨D, hfg, hD⟩ := hC.exists_fg_sup_lineal
--   rw [← hD]
--   rw [← sup_inf_assoc_of_le_submodule]
--   refine sup_fg hfg ?_
--   rw [← coe_inf]
--   exact coe_fg (inf_fg_right _ hS)
--   --rw []
--   sorry

section Module.Finite

variable [Module.Finite 𝕜 N]

variable (p) [Fact p.IsFaithfulPair] in
/-- A finite dimensional FG cone is also CoFG. -/
lemma FG.cofg {C : Submodule 𝕜 N} (hC : C.FG) : C.CoFG p := by
  obtain ⟨D, hcofg, rfl⟩ := exists_cofg_inf_submodule p hC Finite.fg_top (by simp)
  simpa using hcofg

/-- A finite dimensional CoFG cone is also FG. -/
lemma CoFG.fg {C : Submodule 𝕜 N} (hC : C.CoFG p) : C.FG := by
  obtain ⟨D, hfg, rfl⟩ := hC.to_id.exists_fg_dual
  exact CoFG.dual_fg <| FG.cofg _ hfg

-- variable [Module.Finite 𝕜 N] in
-- variable [Fact p.IsFaithfulPair] in
-- /-- A finite dimensional cone is FG if and only if it is CoFG. -/
-- lemma fg_iff_cofg {C : Submodule 𝕜 N} : C.CoFG p ↔ C.FG := ⟨CoFG.fg, FG.cofg p⟩

variable (p) in
/-- In finite dimensional space, the dual of and FG cone is itself FG. -/
lemma FG.dual_fg {C : Submodule 𝕜 M} (hC : C.FG) : (dual p C).FG := by
  rw [dual_id_map]
  exact CoFG.dual_fg <| FG.cofg _ <| FG.map (LinearMap.restrictScalars _ p) hC

/-- In finite dimensional space, the dual of and CoFG cone is itself CoFG. -/
lemma CoFG.dual_cofg {C : Submodule 𝕜 N} (hC : C.CoFG p) : (dual p.flip C).CoFG p.flip
  := FG.dual_cofg p.flip (CoFG.fg hC)

-- TODO: implement pairing lemmas that allow inference of `Module.Finite 𝕜 M`.
--  We should preferably assume `Module.Finite 𝕜 N`
omit [Module.Finite 𝕜 N] in
variable (p) [Module.Finite 𝕜 M] [Fact p.IsFaithfulPair] in
lemma FG.exists_fg_dual {C : Submodule 𝕜 N} (hC : C.FG) :
    ∃ D : Submodule 𝕜 M, D.FG ∧ dual p D = C := by
  use dual p.flip C
  exact ⟨FG.dual_fg p.flip hC, FG.dual_dual_flip p hC⟩

-- -- see `inf_fg` for version not assuming Module.Finite
-- variable [Module.Finite 𝕜 M] in
-- private lemma inf_fg' {C D : Submodule 𝕜 M} (hC : C.FG) (hD : D.FG) : (C ⊓ D).FG := by
--   exact CoFG.fg <| inf_cofg (FG.cofg .id hC) (FG.cofg .id hD)

-- -- see `FG.restrict_fg` for version not assuming Module.Finite
-- variable [Module.Finite 𝕜 M] in
-- private lemma FG.restrict_fg' (S : Submodule 𝕜 M) {C : Submodule 𝕜 M} (hC : C.FG) :
--     (C.restrict S).FG := by
--   rw [← restrict_inf_submodule]
--   refine restrict_fg_of_fg_le (by simp) ?_
--   exact inf_fg' hC <| restrictedScalars_fg_of_fg _ (IsNoetherian.noetherian S)

-- -- NOTE: assumption `p.flip.IsFaithfulPair` cannot be dropped!
-- variable (p) [Fact p.flip.IsFaithfulPair] [Fact p.IsFaithfulPair] in
-- private lemma FG.dual_inf_dual_sup_dual' {C D : Submodule 𝕜 M} (hC : C.FG) (hD : D.FG) :
--     dual p (C ⊓ D : Submodule 𝕜 M) = (dual p C) ⊔ (dual p D) := by
--   nth_rw 1 [← FG.dual_flip_dual p hC]
--   nth_rw 1 [← FG.dual_flip_dual p hD]
--   rw [← dual_sup_dual_inf_dual]
--   rw [FG.dual_dual_flip]
--   exact sup_fg (FG.dual_fg p hC) (FG.dual_fg p hD)

-- NOTE: assumption `p.flip.IsFaithfulPair` cannot be dropped!
variable (p) [Fact p.flip.IsFaithfulPair] in
private lemma FG.dual_inf_dual_sup_dual' {C D : Submodule 𝕜 M} (hC : C.FG) (hD : D.FG) :
    dual p (C ⊓ D : Submodule 𝕜 M) = (dual p C) ⊔ (dual p D) := by
  obtain ⟨C', hC', rfl⟩ := FG.exists_cofg_dual_flip p hC
  obtain ⟨D', hD', rfl⟩ := FG.exists_cofg_dual_flip p hD
  rw [← dual_sup_dual_inf_dual, CoFG.dual_dual_flip <| sup_fg_cofg (CoFG.fg hC') hD',
    CoFG.dual_dual_flip hC', CoFG.dual_dual_flip hD']

end Module.Finite

/-- The intersection of two FG cones is an FG cone. -/
lemma inf_fg {C D : Submodule 𝕜 M} (hC : C.FG) (hD : D.FG) : (C ⊓ D).FG := by
  wlog _ : Module.Finite 𝕜 M with h
  · let CD : Submodule 𝕜 M := .span 𝕜 (C ⊔ D : Submodule 𝕜 M)
    have hCle : C ≤ CD := le_submodule_span_of_le le_sup_left
    have hDle : D ≤ CD := le_submodule_span_of_le le_sup_right
    specialize h (restrict_fg_of_fg_le hCle hC) (restrict_fg_of_fg_le hDle hD)
      (Finite.iff_fg.mpr <| span_fg <| sup_fg hC hD)
    rw [← restrict_inf] at h
    exact fg_of_restrict_le (le_submodule_span_of_le inf_le_sup) h
  · exact CoFG.fg <| inf_cofg (FG.cofg .id hC) (FG.cofg .id hD) -- inf_fg' hC hD

/- TODO: the equivalent of the below statement with CoFG instead of FG can likely be proven
  under rather weak assumptions (Noetherian or so). -/

/-- The intersection of an FG cone with an arbitrary submodule is FG. -/
lemma inf_fg_submodule {C : Submodule 𝕜 M} (hC : C.FG) (S : Submodule 𝕜 M) : (C ⊓ S).FG := by
  rw [left_eq_inf.mpr (le_submodule_span_self C), inf_assoc, ← coe_inf]
  exact inf_fg hC <| coe_fg <| inf_fg_left (span_fg hC) S

lemma inf_submodule_fg (S : Submodule 𝕜 M) {C : Submodule 𝕜 M} (hC : C.FG)
    : (S ⊓ C : Submodule 𝕜 M).FG := by rw [inf_comm]; exact inf_fg_submodule hC S

/-- The restriction of an FG cone to an arbitrary submodule is FG. -/
lemma FG.restrict_fg (S : Submodule 𝕜 M) {C : Submodule 𝕜 M} (hC : C.FG) :
    (C.restrict S).FG := by
  rw [restrict_fg_iff_inf_fg]; exact inf_submodule_fg S hC

/-- The intersection of an FG cone and a CoFG cone is FG. -/
lemma inf_fg_cofg {C D : Submodule 𝕜 N}
    (hC : C.FG) (hD : D.CoFG p) : (C ⊓ D).FG := by
  obtain ⟨C', hCcofg, rfl⟩ := FG.exists_cofg_flip_dual .id hC
  obtain ⟨D', hDfg, rfl⟩ := CoFG.exists_fg_dual hD.to_id
  rw [← dual_sup_dual_inf_dual]
  exact CoFG.dual_fg (sup_cofg_fg hCcofg hDfg)

/-- The intersection of a CoFG cone and an FG cone is FG. -/
lemma inf_cofg_fg {C D : Submodule 𝕜 N} (hC : C.CoFG p) (hD : D.FG) : (C ⊓ D).FG
    := by rw [inf_comm]; exact inf_fg_cofg hD hC

-- TODO: Should not need to rely on `p.flip.IsFaithfulPair`.
variable (p) [Fact p.IsFaithfulPair] [Fact p.flip.IsFaithfulPair] in
lemma dual_fg_inf_cofg_dual_sup_dual {C D : Submodule 𝕜 M} (hC : C.FG)
    (hD : D.CoFG p.flip) : dual p (C ⊓ D : Submodule 𝕜 M) = (dual p C) ⊔ (dual p D) := by
  obtain ⟨C', hC', rfl⟩ := FG.exists_cofg_dual_flip p hC
  obtain ⟨D', hD', rfl⟩ := CoFG.exists_fg_dual hD
  rw [← dual_sup_dual_inf_dual]
  rw [CoFG.dual_dual_flip <| sup_cofg_fg hC' hD']
  rw [CoFG.dual_dual_flip hC']
  rw [FG.dual_dual_flip p hD']

lemma dual_fg_inf_submodule_dual_sup_dual {C : Submodule 𝕜 M} {S : Submodule 𝕜 M}
    (hC : C.FG) (hS : S.FG) :
      dual p (C ⊓ S : Submodule 𝕜 M) = (dual p C) ⊔ (dual p S) := by
  sorry

lemma dual_cofg_inf_submodule_dual_sup_dual {C : Submodule 𝕜 M} {S : Submodule 𝕜 M}
    (hC : C.CoFG p.flip) (hS : S.FG) :
      dual p (C ⊓ S : Submodule 𝕜 M) = (dual p C) ⊔ (dual p S) := by
  sorry

-- TODO: this should *not* rely on `p.flip.IsFaithfulPair`
variable (p) [Fact p.IsFaithfulPair] [Fact p.flip.IsFaithfulPair] in
lemma dual_inf_cofg_dual_sup_dual {C D : Submodule 𝕜 M} (hC : C.FG) (hD : D.FG) :
    dual p (C ⊓ D : Submodule 𝕜 M) = (dual p C) ⊔ (dual p D) := by
  obtain ⟨D', hcofg, S, hfg, rfl⟩ := FG.exists_cofg_inf_fg_submodule p.flip hD
  rw [inf_comm, inf_assoc, inf_comm]
  rw [dual_fg_inf_cofg_dual_sup_dual _ (inf_fg (coe_fg hfg) hC) hcofg]
  rw [inf_comm]
  rw [dual_fg_inf_submodule_dual_sup_dual hC hfg]
  rw [sup_assoc]; nth_rw 2 [sup_comm]
  rw [← dual_cofg_inf_submodule_dual_sup_dual hcofg hfg]

-- lemma foo (C : Submodule 𝕜 M) (S : Submodule 𝕜 N) :
--   ∃ T : Submodule 𝕜 M, (dual p C).restrict S = dual (Dual.eval 𝕜 T) (C.restrict T) := by sorry

-- private lemma inf_submodule_cofg (S : Submodule 𝕜 N) {C : Submodule 𝕜 N} (hC : C.CoFG p) :
--     (C.restrict S).CoFG p := by
--   sorry


-- ----------------- ^^^^^^^ everything up there is proven vvvvv down there is work

-- lemma FG.restrict_fg (S : Submodule 𝕜 M) {C : Submodule 𝕜 M} (hC : C.FG) : (C.restrict S).FG := by
--   wlog hCS : C ≤ S with h
--   · let S' : Submodule 𝕜 M := .span 𝕜 C
--     have hCS : C ≤ S' := le_submodule_span_self C
--     specialize @h 𝕜 S' _ _ _ _ _ (.restrict S' S) (.restrict S' C)
--       (restrict_fg_of_fg_le hCS hC)
--     sorry -- restrict_mono
--   · exact restrict_fg_of_fg_le hCS hC

-- lemma FG.restrict_fg2 (S : Submodule 𝕜 M) {C : Submodule 𝕜 M} (hC : C.FG) : (C.restrict S).FG := by
--   wlog _ : Module.Finite 𝕜 M with h
--   · let S' := Submodule.span 𝕜 (M := M) C
--     specialize @h 𝕜 S' _ _ _ _ _ (.restrict S' S) (restrict S' C) _ _
--     · exact restrict_fg_of_fg_le (le_submodule_span_self C) hC
--     · exact Finite.iff_fg.mpr (span_fg hC)
--     · have hfgS : (restrict S' S).FG := sorry
--       have hfgC : (restrict S' C).FG := sorry
--       sorry
--   · exact restrict_fg' S hC

lemma CoFG.dual_sup_dual_inf_dual {C D : Submodule 𝕜 M}
    (hC : C.CoFG p.flip) (hD : D.CoFG p.flip) : dual p (C ⊓ D) = (dual p C) ⊔ (dual p D) := by
  obtain ⟨C', hCfg', rfl⟩ := CoFG.exists_fg_dual hC
  obtain ⟨D', hDfg', rfl⟩ := CoFG.exists_fg_dual hD
  simp only [Set.inf_eq_inter, ← coe_inf, ← dual_union, ← dual_sup]
  sorry

lemma inf_fg_submodule_cofg' {S : Submodule 𝕜 N} (hS : S.FG) {C : Submodule 𝕜 N} (hC : C.CoFG p) :
    (S ⊓ C : Submodule 𝕜 N).FG := by
  sorry -- I think we first need to do finite theory, and then apply here

variable [Fact p.IsFaithfulPair] in
lemma inf_fg_cofg' {C D : Submodule 𝕜 N} (hC : C.FG) (hD : D.CoFG p) : (C ⊓ D).FG := by
  obtain ⟨C', hCcofg, S, hSfg, rfl⟩ := FG.exists_cofg_inf_fg_submodule p hC
  -- obtain ⟨C', hCfg, rfl⟩ := FG.exists_cofg_flip_dual p hC
  -- obtain ⟨D', hDfg, rfl⟩ := CoFG.exists_fg_dual hD
  rw [inf_comm, ← inf_assoc]
  sorry -- can be reduced to the question "is inf of FG submodule and CoFG halfspace always FG?"

lemma CoFG.exists_fg_sup_submodule {C : Submodule 𝕜 N} (hC : C.CoFG p)
    {S : Submodule 𝕜 N} (hS : S.CoFG p) (hCS : S ≤ C) :
      ∃ D : Submodule 𝕜 N, D.FG ∧ D ⊔ S = C := by
  sorry

variable (p) [Fact p.flip.IsFaithfulPair] in
lemma dual_inf_dual_sup_dual {C D : Submodule 𝕜 M} (hC : C.FG) (hD : D.FG) :
    dual p (C ⊓ D) = (dual p C) ⊔ (dual p D) := by
  -- obtain ⟨C', hCcofg, rfl⟩ := FG.exists_cofg_dual_flip p hC
  -- obtain ⟨D', hDcofg, rfl⟩ := FG.exists_cofg_dual_flip p hD
  -- simp only [Set.inf_eq_inter]
  -- rw [← coe_inf] -- or Submodule.coe_inf
  -- rw [← dual_sup_dual_inf_dual]
  -- -- rw [CoFG.fg_dual_dual_flip p.flip hfg]
  -- -- needs C.CoFG ∧ D.CoFG → (C ⊔ D).CoFG
  sorry

lemma CoFG.is_dual_finite_inf_span''''' {C : Submodule 𝕜 N} (hC : C.FG)
    (S : Submodule 𝕜 N) (hFG : S.FG) (hS : C ≤ S) : ∃ s : Set M, s.Finite ∧ dual p s ⊓ S = C := by
  sorry

lemma CoFG.is_dual_finite_inf_span'''' {C : Submodule 𝕜 N} (hC : C.FG) :
    ∃ s : Set M, s.Finite ∧ dual p s ⊓ Submodule.span (M := N) 𝕜 C = C := by
  sorry

lemma FG.dual_span_finite_sup_lineal (hC : C.FG) :
    ∃ s : Set N, s.Finite ∧ dual p C = span 𝕜 s ⊔ (dual p C).lineal := by
  sorry

lemma FG.dual_span_finset_sup_lineal (hC : C.FG) :
    ∃ s : Finset N, dual p C = span 𝕜 s ⊔ (dual p C).lineal := by
  sorry

lemma CoFG.dual_sup_lineal (hC : C.FG) :
    ∃ D : Submodule 𝕜 N, D.FG ∧ dual p C = D ⊔ (dual p C).lineal := by
  sorry

lemma CoFG.is_sup_cofg_fg (hC : C.CoFG p.flip) :
    ∃ D : Submodule 𝕜 M, D.FG ∧ D ⊔ C.lineal = C := by
  sorry

lemma CoFG.lineal_cofg' (hC : C.CoFG p.flip) : C.lineal.CoFG p.flip := by
  sorry

lemma FG.is_dual_dual_of_finite (hC : C.FG) :
    ∃ s : Set M, s.Finite ∧ dual p.flip (dual p s) = C := by
  sorry

lemma FG.is_dual_dual_of_cofg (hC : C.FG) :
    ∃ D : Submodule 𝕜 N, D.CoFG p ∧ dual p.flip D = C := by
  sorry

/- The following lemmas are proven because they have equivalents for general cones that do
  not hold without the FG assumption -/

-- @[simp] lemma dual_flip_dual_inter {C C' : Submodule 𝕜 M} (hC : C.FG) (hC' : C'.FG) :
--     dual p.flip (dual p (C ∩ C')) = C ⊓ C' := by
--   rw [← dual_flip_dual (p := p) <| inf_fg hC hC']; simp

-- @[simp] lemma dual_dual_flip_inter {C C' : Submodule 𝕜 N} (hC : C.FG) (hC' : C'.FG) :
--     dual p (dual p.flip (C ∩ C')) = C ⊓ C' := by
--   rw [← dual_dual_flip (p := p) <| inf_fg hC hC']; simp

end LinearOrder

end Submodule
