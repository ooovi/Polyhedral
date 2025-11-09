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

import Polyhedral.Mathlib.Algebra.Module.Submodule.CoFG'
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Field
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Face.Basic
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Face.Lattice
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Field
import Polyhedral.Halfspace
import Polyhedral.Faces2

open Function Module OrderDual LinearMap
open Submodule hiding span dual IsDualClosed
open PointedCone



/- WISHLIST:
 * in finite dim, fg = polyhedral
 * faces are polyhedral
 * quotients are polyhedral
 * halfspaces are polyhedral
 * lattice of polyhedral cones
 * finitely many faces / finite face lattice
 * dual closed
-/



namespace PointedCone

variable {R : Type*} [Ring R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {C C₁ C₂ F : PointedCone R M}

/-- A cone is polyhedral if its salient quotient is finitely generated. -/
abbrev IsPolyhedral (C : PointedCone R M) := FG C.salientQuot

lemma isPolyhedral_def : C.IsPolyhedral ↔ FG C.salientQuot := by rfl

/-- Submodules are polyhedral cones. -/
@[simp] lemma isPolyhedral_of_submdule (S : Submodule R M) :
    (S : PointedCone R M).IsPolyhedral := by
  simp [IsPolyhedral, salientQuot_of_submodule, fg_bot]

/-- FG cones are polyhedral. -/
lemma FG.isPolyhedral (hC : C.FG) : C.IsPolyhedral := salientQuot_fg hC

/-- The span of a finite set is polyhedral. -/
lemma isPolyhedral_of_span_finite {s : Set M} (hs : s.Finite) : (span R s).IsPolyhedral :=
  FG.isPolyhedral (fg_def.mpr ⟨s, hs, rfl⟩)

/-- The span of a finite set is polyhedral. -/
lemma isPolyhedral_of_span_finset (s : Finset M) : (span (E := M) R s).IsPolyhedral :=
  isPolyhedral_of_span_finite s.finite_toSet

/-- If `C` is polyhedral and `S`is a submodule complementary to `C`'s linearlity spacen,
  then `C ⊓ S` is FG. A stronger version that only requires `S`to be disjoint to the lineality
  is `IsPolyhedral.fg_inf_of_disjoint_lineal`. -/
lemma IsPolyhedral.fg_inf_of_isCompl (hC : C.IsPolyhedral)
    {S : Submodule R M} (hS : IsCompl C.lineal S) : FG (C ⊓ S) :=
  hC.linearEquiv <| IsCompl.map_mkQ_equiv_inf hS C.lineal_le

/- If the quotient by any contained submodule is FG, then the cone is polyhedral. -/
lemma isPolyhedral_of_quot_fg {S : Submodule R M} (hS : S ≤ C) (hC : FG (C.quot S)) :
    C.IsPolyhedral := by
  simp only [IsPolyhedral, salientQuot, quot, map,
    ← factor_comp_mk <| submodule_le_lineal hS, restrictScalars_comp, map_comp]
  exact FG.map _ hC

/-- The salient quotient of a polyhedral `C` cone can als be written as the quotient of an
   FG cone by the lineality space of `C`. -/
lemma IsPolyhedral.exists_finset_span_quot_lineal (hC : C.IsPolyhedral) :
    ∃ s : Finset M, (span R s).quot C.lineal = C.salientQuot := by classical
  obtain ⟨s, hs⟩ := hC
  use Finset.image (surjInv <| mkQ_surjective _) s
  simp only [map_span, Finset.coe_image, Set.image_image, surjInv_eq, Set.image_id', hs]

-- lemma IsPolyhedral.exists_finset_inter_span_quot_lineal (hC : C.IsPolyhedral) :
--     ∃ s : Finset M, (s : Set M) ∩ C.lineal = ∅ ∧ (span R s).quot C.lineal = C.salientQuot := by
--   classical
--   obtain ⟨s, hs⟩ := exists_finset_span_quot_lineal hC
--   use {x ∈ s | x ∉ C.lineal}
--   constructor
--   · ext; simp
--   · rw [← hs]
--     simp
--     ext x
--     simp [mem_sup]
--     sorry

/-- A polyhedral cone can be written as the sum of its lineality space with an FG cone. -/
lemma IsPolyhedral.exists_finset_sup_lineal (hC : C.IsPolyhedral) :
    ∃ s : Finset M, span R s ⊔ C.lineal = C := by classical
  obtain ⟨s, hs⟩ := exists_finset_span_quot_lineal hC
  exact ⟨s, by simpa [quot_eq_iff_sup_eq] using hs⟩

/-- A polyhedral cone can be written as the sum of its lineality space with an FG cone. -/
lemma IsPolyhedral.exists_fg_sup_lineal (hC : C.IsPolyhedral) :
    ∃ D : PointedCone R M, D.FG ∧ D ⊔ C.lineal = C := by
  obtain ⟨s, hs⟩ := hC.exists_finset_sup_lineal
  exact ⟨span R s, fg_span s.finite_toSet, hs⟩


/-- A polyhedral cone with FG lineality space is FG. -/
lemma IsPolyhedral.fg_of_fg_lineal (hC : C.IsPolyhedral) (h : FG C.lineal) : C.FG := by
  obtain ⟨D, hD, hD'⟩ := hC.exists_fg_sup_lineal
  rw [← hD']
  exact sup_fg hD h

/-- A polyhedral cone is FG if and only if its lineality space is FG. -/
lemma IsPolyhedral.fg_iff_fg_lineal {hC : C.IsPolyhedral} : C.FG ↔ C.lineal.FG :=
  ⟨FG.lineal_fg, hC.fg_of_fg_lineal⟩

/-- If the lineality space is FG then a cone is polyhedral if and only if it is FG. -/
lemma isPolyhedral_iff_fg_of_fg_lineal {h : FG C.lineal} : C.IsPolyhedral ↔ C.FG :=
  ⟨(IsPolyhedral.fg_of_fg_lineal · h), FG.isPolyhedral⟩

/-- A salient polyhedral cone is FG. -/
lemma IsPolyhedral.fg_of_salient (hC : C.IsPolyhedral) (hsal : C.Salient) : C.FG :=
  hC.fg_of_fg_lineal (by simpa [salient_iff_lineal_bot.mp hsal] using fg_bot)

/-- A salient cone is polyhedral if and only if it is FG. -/
lemma isPolyhedral_iff_FG_of_salient (hC : C.Salient) : C.IsPolyhedral ↔ C.FG :=
  ⟨(IsPolyhedral.fg_of_salient · hC), FG.isPolyhedral⟩


section DivisionRing

variable {R : Type*} [DivisionRing R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {C C₁ C₂ F : PointedCone R M}

-- Q: Is DivisionRing necessary?
/-- The lineality space of a full-dimensional cone is CoFG'. -/
lemma IsPolyhedral.cofg_lineal_of_span_top (hC : C.IsPolyhedral)
    (h : Submodule.span R (C : Set M) = ⊤) : CoFG' C.lineal := by
  obtain ⟨_, hS⟩ := Submodule.exists_isCompl C.lineal
  have hh := congrArg (Submodule.span R ∘ SetLike.coe) <| inf_sup_lineal hS.codisjoint
  simp only [Function.comp_apply, h, ← coe_sup_submodule_span, Submodule.coe_restrictScalars,
    Submodule.span_union, span_coe_eq_restrictScalars, restrictScalars_self] at hh
  refine FG.codisjoint_cofg' (codisjoint_iff.mpr hh) (submodule_span_fg <| hC.fg_inf_of_isCompl hS)

-- lemma IsPolyhedral.exists_fg_salient_sup_lineal (hC : C.IsPolyhedral) :
--     ∃ D : PointedCone R M, D.FG ∧ D.Salient ∧ D ⊔ C.lineal = C := by
--   obtain ⟨s, hs', hs⟩ := hC.exists_finset_inter_span_quot_lineal
--   use span R s
--   constructor
--   · exact fg_span (Finset.finite_toSet _)
--   constructor
--   · rw [salient_iff_lineal_bot]
--     rw [← ofSubmodule_inj]
--     rw [← span_inter_lineal_eq_lineal]
--     simp at hs
--     rw [← hs] at hs'
--     have hh := lineal_sup_le (M := M) (span R s) C.lineal
--     simp only [lineal_submodule, -sup_le_iff] at hh
--     have hh := Set.inter_subset_inter_right s hh
--     rw [hs'] at hh
--     simp at hh
--     -- rw [Set.sup_eq_union] at hh
--     -- rw [lineal_sup]
--     -- simp at hs'
--     sorry -- use hs'
--   · simpa [span_union, span_coe_eq_restrictScalars] using hs

end DivisionRing


-- ## SUP

/-- The sum of an FG cone with a submodule is polyhedral. -/
lemma isPolyhedral_of_fg_sup_submodule (hC : C.FG) (S : Submodule R M) :
    (C ⊔ S).IsPolyhedral := by
  refine isPolyhedral_of_quot_fg le_sup_right ?_
  simpa [sup_quot_eq_quot] using quot_fg hC S

/-- The sum of two polyhedral cones is polyhedral -/
lemma IsPolyhedral.sup (h₁ : C₁.IsPolyhedral) (h₂ : C₂.IsPolyhedral) :
    (C₁ ⊔ C₂).IsPolyhedral := by
  obtain ⟨D₁, hD₁, hD₁'⟩ := h₁.exists_fg_sup_lineal
  obtain ⟨D₂, hD₂, hD₂'⟩ := h₂.exists_fg_sup_lineal
  rw [← hD₁', ← hD₂', sup_assoc]
  nth_rw 2 [sup_comm]
  rw [sup_assoc, ← sup_assoc, ← coe_sup]
  exact isPolyhedral_of_fg_sup_submodule (sup_fg hD₁ hD₂) _

/-- The sum of a polyhedral cone with a submodule is polyhedral. -/
lemma IsPolyhedral.sup_submodule (hC : C.IsPolyhedral) (S : Submodule R M) :
    (C ⊔ S).IsPolyhedral := hC.sup (isPolyhedral_of_submdule S)

/-- The sum of a polyhedral cone with an FG cone is polyhedral. -/
lemma IsPolyhedral.sup_fg (hC : C.IsPolyhedral) {D : PointedCone R M} (hD : D.FG) :
    (C ⊔ D).IsPolyhedral := hC.sup (FG.isPolyhedral hD)


-- ## MAP / COMAP

lemma IsPolyhedral.map (hC : C.IsPolyhedral) (f : M →ₗ[R] N) : (C.map f).IsPolyhedral := by
  obtain ⟨D, hfg, hD'⟩ := hC.exists_fg_sup_lineal
  rw [← hD']
  simp only [PointedCone.map, Submodule.map_sup] -- `map` should be an abbrev
  refine sup ?_ ?_
  · exact FG.isPolyhedral (FG.map _ hfg)
  · simp [← restrictScalars_map]

lemma IsPolyhedral.comap (hC : C.IsPolyhedral) (f : N →ₗ[R] M) : (C.comap f).IsPolyhedral := by
  unfold IsPolyhedral salientQuot quot at *
  -- apply FG.map
  rw [comap_lineal]
  sorry

lemma IsPolyhedral.quot (hC : C.IsPolyhedral) (S : Submodule R M) :
    (C.quot S).IsPolyhedral := hC.map _

@[simp] lemma isPolyhedral_neg_iff : (-C).IsPolyhedral ↔ C.IsPolyhedral where
  mp := by
    intro hC;
    simp [← map_id_eq_neg] at hC;
    simpa [map_map] using hC.map (-.id)
  mpr := fun hC => by simpa only [← map_id_eq_neg] using hC.map _

lemma IsPolyhedral.neg (hC : C.IsPolyhedral) : (-C).IsPolyhedral := by simpa using hC


-- ## DUAL

section Field

variable {R : Type*} [Field R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}
variable {C C₁ C₂ F : PointedCone R M}

/- Crucial sorry's that need to be fixed asap:
 * `aux`
 * CoFG' --> CoFG aka `CoFG'.cofg`
 * -C ⊔ C = Submodule.span C
-/

/-- Auxiliarty lemma used for reducing polyhedral intersections to FG intersections. -/
private lemma aux {P₁ P₂ : Submodule R M} (h₁ : P₁.FG) (h₂ : P₂.FG) (L₁ L₂ : Submodule R M) :
    ∃ P : Submodule R M, P.FG ∧ (P₁ ⊔ L₁) ⊓ (P₂ ⊔ L₂) = P ⊔ (L₁ ⊓ L₂) := by
  #check fg_of_fg_map_of_fg_inf_ker -- maybe useful
  sorry

/-- A polyhedral cone with CoFG linearlity space is itself CoFG. -/
lemma IsPolyhedral.cofg_of_lineal_cofg {C : PointedCone R N}
    (hC : C.IsPolyhedral) (hlin : C.lineal.CoFG p) : CoFG p C := by
  obtain ⟨_, hfg, hD⟩ := hC.exists_fg_sup_lineal
  rw [← hD]
  exact sup_fg_cofg hfg hlin

/-- A polyhedral cone is CoFG if and only if its lineality space is CoFG. -/
lemma IsPolyhedral.cofg_iff_lineal_cofg {C : PointedCone R N} {hC : C.IsPolyhedral} :
    C.CoFG p ↔ C.lineal.CoFG p := ⟨CoFG.lineal_cofg, hC.cofg_of_lineal_cofg⟩

variable (p) [Fact (Surjective p)] in
/-- If `C` is a polyhedral cone and `S` is a subspace codisjoint to the linear span of `C`,
  then `C ⊔ S` is CoFG. This is the counterpart to `IsPolyhedral.cofg_inf_of_disjoint_lineal`. -/
lemma IsPolyhedral.cofg_sup_of_codisjoint {C : PointedCone R N} (hC : C.IsPolyhedral)
    {S : Submodule R N} (hS : Codisjoint (Submodule.span R C) S) : CoFG p (C ⊔ S) := by
  refine (hC.sup <| isPolyhedral_of_submdule S).cofg_of_lineal_cofg (CoFG'.cofg p ?_)
  refine cofg_lineal_of_span_top (hC.sup_submodule _) ?_
  simpa [← coe_sup_submodule_span, Submodule.span_union] using codisjoint_iff.mp hS

variable (p) [Fact (Surjective p)] in
/-- A polyhedral cone `C` can be written as the intersection of a CoFG cone with the
  linear span of `C`. -/
lemma IsPolyhedral.exists_cofg_inf_span {C : PointedCone R N} (hC : C.IsPolyhedral) :
    ∃ D : PointedCone R N, D.CoFG p ∧ D ⊓ Submodule.span (M := N) R C = C := by
  have ⟨S, hS⟩ := Submodule.exists_isCompl (Submodule.span (M := N) R C)
  exact ⟨C ⊔ S, hC.cofg_sup_of_codisjoint p hS.codisjoint,
    sup_inf_submodule_span_of_disjoint hS.disjoint⟩

variable (p) in
/-- Duals generated from a finite set are polyhedral. -/
lemma isPolyhedral_dual_of_finset (s : Finset M) : (dual p s).IsPolyhedral := by
  obtain ⟨D, hfg, hD⟩ := exists_fg_sup_dual p s
  rw [← hD]
  exact isPolyhedral_of_fg_sup_submodule hfg _

variable (p) in
/-- Duals of FG cones are polyhedral. -/
lemma isPolyhedral_dual_of_fg (hC : C.FG) : (dual p C).IsPolyhedral := by
  obtain ⟨D, hfg, hD⟩ := FG.exists_fg_sup_dual p hC
  rw [← hD]
  exact isPolyhedral_of_fg_sup_submodule hfg _

/-- CoFG cones are polyhedral. -/
lemma isPolyhedral_cofg {C : PointedCone R N} (hC : C.CoFG p) : C.IsPolyhedral := by
  obtain ⟨D, hfg, rfl⟩ := hC.exists_fg_dual
  exact isPolyhedral_dual_of_fg p hfg

/-- The intersection of a polyhedral cone with an FG cone is FG. -/
lemma IsPolyhedral.fg_of_inf_fg_submodule (hC : C.IsPolyhedral)
    {S : Submodule R M} (hS : FG S) : FG (C ⊓ S) := by
  obtain ⟨D, hcofg, hD⟩ := hC.exists_cofg_inf_span .id
  rw [← hD, inf_assoc, ← coe_inf]
  exact inf_cofg_fg hcofg <| coe_fg <| Submodule.inf_fg_right _ hS

/-- The intersection of two polyhedral cones is polyhdral. -/
lemma IsPolyhedral.inf (h₁ : C₁.IsPolyhedral) (h₂ : C₂.IsPolyhedral) :
    (C₁ ⊓ C₂).IsPolyhedral := by
  -- The proof reduces the problem to the case of intersecting FG cones using the aux lemma.
  -- Then we can use `inf_fg` from the FG theory.
  obtain ⟨D₁, hfg₁, hD₁⟩ := h₁.exists_fg_sup_lineal
  obtain ⟨D₂, hfg₂, hD₂⟩ := h₂.exists_fg_sup_lineal
  have hD₁' := congrArg (Submodule.span R ∘ SetLike.coe) hD₁
  have hD₂' := congrArg (Submodule.span R ∘ SetLike.coe) hD₂
  simp only [Function.comp_apply] at hD₁' hD₂'
  rw [← PointedCone.coe_sup_submodule_span, Submodule.span_union] at hD₁' hD₂'
  simp only [Submodule.coe_restrictScalars, span_coe_eq_restrictScalars,
    restrictScalars_self] at hD₁' hD₂'
  --
  have h := Submodule.le_span (R := R) (M := M) (s := (C₁ ⊓ C₂ : PointedCone R M))
  replace h := le_trans h (span_inter_le _ _)
  rw [← hD₁', ← hD₂'] at h
  --
  obtain ⟨P, hPfg, hP⟩ :=
      aux (submodule_span_fg hfg₁) (submodule_span_fg hfg₂) C₁.lineal C₂.lineal
  rw [hP] at h
  nth_rw 2 [← ofSubmodule_coe] at h
  rw [Set.le_iff_subset] at h
  rw [SetLike.coe_subset_coe] at h
  --
  rw [← inf_eq_left.mpr h]
  have H := inf_le_inf (lineal_le C₁) (lineal_le C₂)
  rw [coe_sup, inf_sup_assoc_of_submodule_le _ H]
  --
  rw [← inf_idem P, inf_assoc, inf_comm, coe_inf, ← inf_assoc, inf_assoc]
  refine isPolyhedral_of_fg_sup_submodule (inf_fg ?_ ?_) _
  · exact h₂.fg_of_inf_fg_submodule hPfg
  · simpa [inf_comm] using h₁.fg_of_inf_fg_submodule hPfg

/-- If `C` is a polyhedral cone and `S` is a submodule disjoint to its lineality, then
  `C ⊓ S` is FG. This is a strengthened version of `IsPolyhedral.fg_inf_of_isCompl`. -/
lemma IsPolyhedral.fg_inf_of_disjoint_lineal (hC : C.IsPolyhedral)
    {S : Submodule R M} (hS : Disjoint C.lineal S) : FG (C ⊓ S) := by
  refine fg_of_fg_lineal (hC.inf <| isPolyhedral_of_submdule S) ?_
  simp only [lineal_inf, lineal_submodule, disjoint_iff.mp hS, fg_bot]
  -- TODO: fg_bot should be a simp lemma

variable (p) in
/-- The dual of a polyhedral cone is polyhedral. -/
lemma IsPolyhedral.dual (hC : C.IsPolyhedral) : (dual p C).IsPolyhedral := by
  obtain ⟨D, hDfg, hD⟩ := hC.exists_fg_sup_lineal
  rw [← hD, dual_sup_dual_inf_dual, Submodule.coe_restrictScalars, dual_eq_submodule_dual]
  exact IsPolyhedral.inf (isPolyhedral_dual_of_fg p hDfg) (isPolyhedral_of_submdule _)

variable (p) in
-- I believe proving this requires a lot of other work to be done before (above).
-- Essentially, in a lot of lemmas we need to replace `[Fact (Surjective p)]` by an
-- an assumption about lineal, most likely, that lineal is dual closed.
-- However, the assumption `[Fact (Surjective p)]` is preferable because it can be
-- inferred automatically in the finite dimensional case.
lemma IsPolyhedral.isDualClosed_iff_lineal (hC : C.IsPolyhedral) :
  C.IsDualClosed p ↔ C.lineal.IsDualClosed p := by sorry

variable (p) [Fact (Surjective p.flip)] in
lemma IsPolyhedral.isDualClosed (hC : C.IsPolyhedral) : C.IsDualClosed p := by
  obtain ⟨D, hcofg, hD⟩ := hC.exists_cofg_inf_span p.flip
  rw [← hD]
  exact IsDualClosed.inf (CoFG.isDualClosed hcofg)
    (isDualClosed_coe <| Submodule.isDualClosed p _)

variable (p) [Fact (Surjective p.flip)] in
lemma IsPolyhedral.dual_dual (hC : C.IsPolyhedral) :
  PointedCone.dual p.flip (PointedCone.dual p C) = C := hC.isDualClosed p

variable (p) [Fact (Surjective p.flip)] in
lemma IsPolyhedral.dual_inf_dual_sup_dual (hC₁ : C.IsPolyhedral) (hC₂ : C.IsPolyhedral) :
    PointedCone.dual p (C₁ ⊓ C₂) = PointedCone.dual p C₁ ⊔ PointedCone.dual p C₂ := sorry

/- Widhlist:
  * polyhedra are dual closed
  * dual (C ⊓ D) = dual C ⊔ dual D
-/






-- variable (p) [Fact p.IsFaithfulPair] in
-- private lemma IsPolyhedral.dual_fg_of_lineal_cofg' {C : PointedCone R M}
--     (hC : C.IsPolyhedral) (hlin : CoFG' C.lineal) : FG (dual p C) := by
--   obtain ⟨_, hfg, hD⟩ := hC.exists_fg_sup_lineal
--   rw [← hD]
--   exact CoFG.dual_fg (sup_fg_cofg hfg <| CoFG'.cofg p.flip hlin)

variable (p) [Fact (Surjective p)] in
@[deprecated cofg_of_lineal_cofg (since := "...")]
private lemma IsPolyhedral.cofg_of_lineal_cofg' {C : PointedCone R N}
    (hC : C.IsPolyhedral) (hlin : CoFG' C.lineal) : CoFG p C := by
  obtain ⟨_, hfg, hD⟩ := hC.exists_fg_sup_lineal
  rw [← hD]
  exact sup_fg_cofg hfg (CoFG'.cofg p hlin)

variable (p) [Fact (Surjective p.flip)] in -- [Fact p.IsFaithfulPair]
lemma IsPolyhedral.exists_isPolyhedral_dual (hC : C.IsPolyhedral) :
    ∃ D : PointedCone R N, D.IsPolyhedral ∧ PointedCone.dual p.flip D = C := by
  -- wlog fact : Fact (Surjective p) with H
  -- · rw [dual_id_map]
  --   let C' := C.map p
  --   have hC' : C'.IsPolyhedral := hC.map p
  --   have h' : C' = C.map p := rfl
  --   rw [← h']
  --   clear h' hC
  --   sorry
  obtain ⟨S, hS⟩ := Submodule.exists_isCompl C.lineal
  let C' := C ⊔ S
  have hC' : C'.IsPolyhedral := hC.sup_submodule S
  have h : C = C' ⊓ Submodule.span R (C : Set M) := sorry
  rw [h]
  have hh : Submodule.span R (C' : Set M) = ⊤ := sorry
  have h := hC'.cofg_of_lineal_cofg' p.flip (hC'.cofg_lineal_of_span_top hh)
  --have h' := CoFG.dual_fg h -- we dont' need FG, we need polyhedral
  have h' : (PointedCone.dual p C').IsPolyhedral := sorry -- FG.isPolyhedral (CoFG.dual_fg h)
  have h'' := CoFG.isDualClosed h
  rw [← h'']
  have h'' := Submodule.isDualClosed p (Submodule.span R C)
  rw [← h'']
  rw [← dual_eq_submodule_dual]
  have h (S : Submodule R N) : ((S : PointedCone R N) : Set N) = (S : Set N) := by simp
  -- rw [← h]
  --rw [← dual_eq_submodule_dual p]
  rw [← PointedCone.dual_union]
  simp
  let D := Submodule.dual p (C : Set M)
  use (PointedCone.dual p C') ⊔ D
  unfold D
  constructor
  · exact h'.sup_submodule _
  · rw [← h, ← dual_sup]



-- private lemma IsPolyhedral.dual_fg_of_lineal_cofg {C : PointedCone R N}
--     (hC : C.IsPolyhedral) (hlin : CoFG' C.lineal) :
--       ∃ D : PointedCone R M, D.IsPolyhedral ∧ PointedCone.dual p D = C := by
--   obtain ⟨S, hS⟩ := Submodule.exists_isCompl C.lineal

  --have h : FG (Submodule.dual p (C.lineal : Set N)) := sorry
  -- sorry

-- variable (p) in
-- lemma IsPolyhedral.dual' (hC : C.IsPolyhedral) : (PointedCone.dual p C).IsPolyhedral := by
--   rw [dual_id_map]
--   let C' := C.map p
--   have hC' : C'.IsPolyhedral := hC.map p
--   have h' : C' = C.map p := rfl
--   rw [← h']
--   -----
--   obtain ⟨D, hfg, hD⟩ := hC'.exists_fg_sup_lineal
--   rw [← hD]
--   rw [dual_sup_dual_inf_dual]
--   obtain ⟨E, hfg, hE⟩ := (isPolyhedral_dual_of_fg .id hfg).exists_fg_sup_lineal
--   rw [← hE]
--   simp only [Submodule.coe_restrictScalars, dual_eq_submodule_dual]
--   rw [← sup_inf_assoc_of_le_submodule]
--   · rw [← PointedCone.coe_inf]
--     exact isPolyhedral_of_fg_sup_submodule hfg _
--   · rw [dual_span_lineal_dual] at hE
--     -- rw [right_eq_sup] at hE
--     ----
--     rw [← hD]
--     --rw [dual_sup_dual_eq_inf_dual]
--     rw [IsDualClosed.dual_lineal_span_dual]
--     ·
--       sorry
--     · sorry
--     -- exact left_eq_sup.mp hE.symm

end Field

section Module.Finite

variable [Module.Finite R M]

lemma IsPolyhedral.FG (hC : C.IsPolyhedral) : C.FG := sorry

lemma isPolyhedral_iff_FG : C.IsPolyhedral ↔ C.FG := ⟨IsPolyhedral.FG, FG.isPolyhedral⟩

end Module.Finite



-- ## FACE

lemma IsPolyhedral.face (hC : C.IsPolyhedral) (hF : F.IsFaceOf C) : F.IsPolyhedral := sorry



end PointedCone











-- ## POLYHEDRAL CONE


variable {R : Type*} [Ring R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [AddCommGroup N] [Module R N]

variable (R M) in
/-- A cone is polyhedral if its salient quotient is finitely generated. -/
structure PolyhedralCone extends PointedCone R M where
  isPolyhedral : IsPolyhedral toSubmodule

namespace PolyhedralCone

-- ## BOILERPLATE

@[coe] abbrev toPointedCone (C : PolyhedralCone R M) : PointedCone R M := C.toSubmodule

instance : Coe (PolyhedralCone R M) (PointedCone R M) := ⟨toPointedCone⟩

lemma toPointedCone_injective :
    Injective (toPointedCone : PolyhedralCone R M → PointedCone R M) :=
  sorry -- fun ⟨_, _⟩ _ ↦ by congr!

instance : SetLike (PolyhedralCone R M) M where
  coe C := C.toPointedCone
  coe_injective' := SetLike.coe_injective.comp toPointedCone_injective

@[simp] lemma coe_toPointedCone (C : PolyhedralCone R M) :
    (C.toPointedCone : Set M) = C := rfl


-- ## FG

variable {C C₁ C₂ : PolyhedralCone R M}

/-- A finitely generated cone is polyhedral. -/
def of_FG {C : PointedCone R M} (hC : C.FG) : PolyhedralCone R M
    := ⟨C, FG.isPolyhedral hC⟩

variable (R) in
def finspan (s : Finset M) : PolyhedralCone R M := ⟨_, isPolyhedral_of_span_finset s⟩

set_option linter.unusedSectionVars false in -- why necessary ??
@[simp] lemma finspan_eq_span (s : Finset M) : finspan R s = span (E := M) R s := rfl

def finspan_lineal (s : Finset M) (S : Submodule R M) : PolyhedralCone R M :=
  ⟨span R s ⊔ S, IsPolyhedral.sup (isPolyhedral_of_span_finset s) (by simp)⟩

variable [Module.Finite R M]
/-- A polyhedral cone in a finite dimensional vector space is finitely generated. -/
def FG {C : PolyhedralCone R M} : C.FG := C.isPolyhedral.FG


-- ## COFG

-- /-- A co-finitely generated cone is polyhedral. -/
-- def of_CoFG {C : PointedCone R M} (hC : C.CoFG) : PolyhedralCone R M := sorry


-- ## TOP / BOT

def bot : PolyhedralCone R M := ⟨_, Submodule.isPolyhedral ⊥⟩
def top : PolyhedralCone R M := ⟨_, Submodule.isPolyhedral ⊤⟩

-- alias lineal := bot

instance : OrderBot (PolyhedralCone R M) where
  bot := bot
  bot_le := sorry

instance : OrderTop (PolyhedralCone R M) where
  top := top
  le_top := sorry

instance : Max (PolyhedralCone R M) where
  max C D := ⟨_, C.isPolyhedral.sup D.isPolyhedral⟩

section Field

variable {R : Type*} [Field R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

instance : Min (PolyhedralCone R M) where
  min C D := ⟨_, C.isPolyhedral.inf D.isPolyhedral⟩

end Field


-- ## FACE

instance : CoeOut (Face (C : PointedCone R M)) (PolyhedralCone R M) where
  coe F := ⟨F, C.isPolyhedral.face F.isFaceOf⟩

instance {C : PolyhedralCone R M} : Finite (Face (C : PointedCone R M)) := sorry

def atomFaces : Set (Face (C : PointedCone R M)) := sorry

alias rays := atomFaces

def coatomFaces : Set (Face (C : PointedCone R M)) := sorry

alias facets := coatomFaces

/- TODO:
 * face lattice is graded
 * all faces exposed
-/

-- lemma face_exposed (F : Face C) : F.IsExposed := sorry


-- ## DUAL

section CommRing

variable {R : Type*} [CommRing R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}
variable {C C₁ C₂ F : PolyhedralCone R M}

-- variable (p) in
-- def dual (C : PolyhedralCone R M) : PolyhedralCone R N := ⟨_, C.isPolyhedral.dual p⟩

variable (p) [Fact p.flip.IsFaithfulPair] in
lemma isDualClosed (C : PolyhedralCone R M) : IsDualClosed p C := sorry

variable (p) in
lemma isDualClosed_iff (C : PolyhedralCone R M) :
  IsDualClosed p C ↔ (lineal C).IsDualClosed p := sorry

-- Duality flips the face lattice

section Field

variable {R : Type*} [Field R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}

variable (p) in
def findual (s : Finset M) : PolyhedralCone R N := ⟨dual p s, isPolyhedral_dual_of_finset p s⟩

variable (p) in
@[simp]
lemma findual_eq_dual (s : Finset M) : findual p s = dual p s := rfl

variable (p) in
def dual (P : PolyhedralCone R M) : PolyhedralCone R N := ⟨_, P.isPolyhedral.dual p⟩

variable (p) in
@[simp]
lemma coe_dual (P : PolyhedralCone R M) : P.dual p = PointedCone.dual p P := rfl

end Field

end CommRing


-- ## SUBMODULE

instance : Coe (Submodule R M) (PolyhedralCone R M) where
  coe S := ⟨_, S.isPolyhedral⟩

-- instance : Coe (HalfspaceOrTop R M) (PolyhedralCone R M) := sorry

-- instance : Coe (Halfspace R M) (PolyhedralCone R M) := sorry

-- instance : Coe (HyperplaneOrTop R M) (PolyhedralCone R M) := sorry

-- instance : Coe (Hyperplane R M) (PolyhedralCone R M) := sorry


-- ## MAP

def map (f : M →ₗ[R] N) (C : PolyhedralCone R M) : PolyhedralCone R N :=
  ⟨_, C.isPolyhedral.map f⟩

def comap (f : M →ₗ[R] N) (C : PolyhedralCone R N) : PolyhedralCone R M :=
  ⟨_, C.isPolyhedral.comap f⟩


-- ## QUOT

def quot (S : Submodule R M) : PolyhedralCone R (M ⧸ S) := ⟨_, C.isPolyhedral.quot S⟩

def salientQuot : PolyhedralCone R (M ⧸ (C : PointedCone R M).lineal) := sorry
    -- ⟨_, C.isPolyhedral.salientQuot⟩


-- ## NEG

instance : InvolutiveNeg (PolyhedralCone R M) where
  neg C := ⟨_, C.isPolyhedral.neg⟩
  neg_neg := sorry

end PolyhedralCone
