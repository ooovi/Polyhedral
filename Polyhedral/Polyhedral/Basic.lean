/-
Copyright (c) 2025 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.MinkowskiWeyl

open Function Module OrderDual LinearMap
open Submodule hiding span dual DualClosed
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

lemma IsPolyhedral.def : C.IsPolyhedral ↔ FG C.salientQuot := by rfl

lemma IsPolyhedral.salientQuot_fg (hC : C.IsPolyhedral) : FG C.salientQuot := hC

/-- Submodules are polyhedral cones. -/
@[simp] lemma IsPolyhedral.of_submodule (S : Submodule R M) :
    (S : PointedCone R M).IsPolyhedral := by
  simp [IsPolyhedral, salientQuot_of_submodule, fg_bot]

/-- FG cones are polyhedral. -/
lemma FG.isPolyhedral (hC : C.FG) : C.IsPolyhedral := salientQuot_fg hC

lemma IsPolyhedral.salientQuot (hC : C.IsPolyhedral) : IsPolyhedral C.salientQuot :=
    FG.isPolyhedral hC.salientQuot_fg

/-- The span of a finite set is polyhedral. -/
lemma IsPolyhedral.of_span_finite {s : Set M} (hs : s.Finite) : (span R s).IsPolyhedral :=
  FG.isPolyhedral (fg_def.mpr ⟨s, hs, rfl⟩)

/-- The span of a finite set is polyhedral. -/
lemma isPolyhedral_of_span_finset (s : Finset M) : (span (E := M) R s).IsPolyhedral :=
  .of_span_finite s.finite_toSet

/- If the quotient by any contained submodule is FG, then the cone is polyhedral. -/
lemma IsPolyhedral.of_quot_fg {S : Submodule R M} (hS : S ≤ C) (hC : FG (C.quot S)) :
    C.IsPolyhedral := by
  simpa only [IsPolyhedral, map, ← factor_comp_mk <| le_lineal hS,
    restrictScalars_comp, map_comp] using FG.map _ hC

/-- The salient quotient of a polyhedral `C` cone can be written as the quotient of an
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

/-- If the lineality space is FG then a cone is polyhedral if and only if it is FG. -/
lemma IsPolyhedral.iff_fg_of_fg_lineal {h : FG C.lineal} : C.IsPolyhedral ↔ C.FG :=
  ⟨(IsPolyhedral.fg_of_fg_lineal · h), FG.isPolyhedral⟩

/-- A salient polyhedral cone is FG. -/
lemma IsPolyhedral.fg_of_salient (hC : C.IsPolyhedral) (hsal : C.Salient) : C.FG :=
  hC.fg_of_fg_lineal (by simpa [salient_iff_lineal_bot.mp hsal] using fg_bot)

/-- A salient cone is polyhedral if and only if it is FG. -/
lemma IsPolyhedral.iff_fg_of_salient (hC : C.Salient) : C.IsPolyhedral ↔ C.FG :=
  ⟨(IsPolyhedral.fg_of_salient · hC), FG.isPolyhedral⟩

section CommRing

variable {R : Type*} [CommRing R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {C C₁ C₂ F : PointedCone R M}

/-- If `C` is polyhedral and `S` is a submodule complementary to `C`'s linearlity spacen,
  then `C ⊓ S` is FG. A stronger version that only requires `S` to be disjoint to the lineality
  is `IsPolyhedral.fg_inf_of_disjoint_lineal`. -/
lemma IsPolyhedral.fg_inf_of_isCompl (hC : C.IsPolyhedral)
    {S : Submodule R M} (hS : IsCompl C.lineal S) : FG (C ⊓ S) :=
  hC.linearEquiv <| IsCompl.map_mkQ_equiv_inf hS C.lineal_le

end CommRing

-- ## SUP

/-- The sum of an FG cone with a submodule is polyhedral. -/
lemma IsPolyhedral.of_fg_sup_submodule (hC : C.FG) (S : Submodule R M) :
    (C ⊔ S).IsPolyhedral := by
  refine .of_quot_fg le_sup_right ?_
  simpa [sup_quot_eq_quot] using quot_fg hC S

/-- The sum of two polyhedral cones is polyhedral -/
lemma IsPolyhedral.sup (h₁ : C₁.IsPolyhedral) (h₂ : C₂.IsPolyhedral) :
    (C₁ ⊔ C₂).IsPolyhedral := by
  obtain ⟨D₁, hD₁, hD₁'⟩ := h₁.exists_fg_sup_lineal
  obtain ⟨D₂, hD₂, hD₂'⟩ := h₂.exists_fg_sup_lineal
  rw [← hD₁', ← hD₂', sup_assoc]
  nth_rw 2 [sup_comm]
  rw [sup_assoc, ← sup_assoc, ← coe_sup]
  exact .of_fg_sup_submodule (sup_fg hD₁ hD₂) _

/-- The sum of a polyhedral cone with a submodule is polyhedral. -/
lemma IsPolyhedral.sup_submodule (hC : C.IsPolyhedral) (S : Submodule R M) :
    (C ⊔ S).IsPolyhedral := hC.sup (.of_submodule S)

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
  · rw [← restrictScalars_map]
    simp

lemma IsPolyhedral.comap (hC : C.IsPolyhedral) (f : N →ₗ[R] M) : (C.comap f).IsPolyhedral := by
  unfold IsPolyhedral PointedCone.salientQuot quot at *
  -- apply FG.map
  rw [comap_lineal]
  sorry

lemma IsPolyhedral.quot (hC : C.IsPolyhedral) (S : Submodule R M) :
    (C.quot S).IsPolyhedral := hC.map _

@[simp] lemma IsPolyhedral.neg_iff : (-C).IsPolyhedral ↔ C.IsPolyhedral where
  mp := by
    intro hC;
    simp [← map_id_eq_neg] at hC;
    simpa [map_map] using hC.map (-.id)
  mpr := fun hC => by simpa only [← map_id_eq_neg] using hC.map _

lemma IsPolyhedral.neg (hC : C.IsPolyhedral) : (-C).IsPolyhedral := by simpa using hC



section Field

variable {R : Type*} [Field R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}
variable {C C₁ C₂ F : PointedCone R M}

/-- A polyhedral cone is FG if and only if its lineality space is FG. -/
lemma IsPolyhedral.fg_iff_fg_lineal {hC : C.IsPolyhedral} : C.FG ↔ C.lineal.FG :=
  ⟨FG.lineal_fg, hC.fg_of_fg_lineal⟩


-- ## DUAL

-- FIX: fix `fg_inf_of_isCompl` first
-- Q: Is DivisionRing necessary?
/-- The lineality space of a full-dimensional cone is CoFG. -/
lemma IsPolyhedral.cofg_lineal_of_span_top (hC : C.IsPolyhedral)
    (h : Submodule.span R (C : Set M) = ⊤) : CoFG C.lineal := by
  obtain ⟨_, hS⟩ := Submodule.exists_isCompl C.lineal
  have hh := congrArg (Submodule.span R ∘ SetLike.coe) <| inf_sup_lineal hS.codisjoint
  simp only [Function.comp_apply, h, ← coe_sup_submodule_span, Submodule.coe_restrictScalars,
    Submodule.span_union, span_coe_eq_restrictScalars, restrictScalars_self] at hh
  refine FG.codisjoint_cofg (codisjoint_iff.mpr hh) (submodule_span_fg <| hC.fg_inf_of_isCompl hS)

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

-- TODO: move
omit [LinearOrder R] [IsOrderedRing R] in
lemma ker_compl_fg {X P : Submodule R M} {C : Submodule R X} (f : X →ₗ[R] M) (rg_le : range f ≤ P)
    (fg : P.FG) (hC : IsCompl (ker f) C) : C.FG := by
  have : Module.Finite R (↥X ⧸ ker f) := by -- iso thm
    apply (Finite.equiv_iff (quotKerEquivRange f).symm).mp
    have := isNoetherian_of_fg_of_noetherian _ fg
    exact Module.Finite.of_injective (inclusion rg_le) (inclusion_injective _)
  have := quotientEquivOfIsCompl _ _ hC
  exact (Submodule.fg_top _).mp (Module.finite_def.mp (Finite.equiv this))

omit [LinearOrder R] [IsOrderedRing R] in
/- Auxiliarty lemma used for reducing polyhedral intersections to FG intersections. -/
private lemma aux' {P₁ P₂ L₁ L₂ M₁ M₂ : Submodule R M} (h₁ : P₁.FG) (h₂ : P₂.FG)
    (hM₁ : P₁ ≤ M₁) (hM₂ : P₂ ≤ M₂) (hc₁ : IsCompl L₁ M₁) (hc₂ : IsCompl L₂ M₂) :
    ∃ P : Submodule R M, P.FG ∧ (P₁ ⊔ L₁) ⊓ (P₂ ⊔ L₂) = P ⊔ (L₁ ⊓ L₂) := by
  set X := ((P₁ ⊓ M₁) ⊔ L₁) ⊓ ((P₂ ⊓ M₂) ⊔ L₂)
  let f : X →ₗ[R] M := (hc₁.projection - hc₂.projection).comp X.subtype
  have cmem_zero {P L : Submodule R M} {x} (hx : x ∈ P) (c : IsCompl L P) :
      c.projection x = 0 := by rwa [← mem_ker, c.projection_ker]
  have range_le : range f ≤ P₁ ⊔ P₂ := by
    intro x xm
    apply mem_sup.mpr
    simp only [mem_range, coe_comp, coe_subtype, Function.comp_apply, sub_apply, Subtype.exists,
      mem_inf, mem_sup, exists_prop, X, f] at xm
    obtain ⟨-, ⟨⟨⟨b, ⟨e, h, j, rfl⟩⟩, ⟨ed, ⟨hd, _, dd, ddd⟩⟩⟩, rfl⟩⟩ := xm
    use -b, P₁.neg_mem e.1, ed, hd.1
    rw [map_add hc₁.projection, cmem_zero e.2 hc₁, hc₁.projection_isProj.map_id _ j, ← ddd,
      map_add, cmem_zero hd.2 hc₂, hc₂.projection_isProj.map_id _ dd]
    grind only
  obtain ⟨S, hs⟩ := (ker f).exists_isCompl
  use .embed S ⊔ (P₁ ⊓ P₂)
  constructor
  · refine FG.sup (Submodule.embed_fg_iff_fg.mpr (ker_compl_fg f range_le (FG.sup h₁ h₂) hs)) ?_
    exact FG.of_le h₂ inf_le_right
  · rw [left_eq_inf.mpr hM₁, left_eq_inf.mpr hM₂, sup_assoc]
    have Xeq := congrArg (Submodule.map X.subtype) hs.symm.sup_eq_top.symm
    simp_rw [Submodule.map_top, range_subtype, Submodule.map_sup, f, X] at Xeq
    simp_rw [Xeq, X]
    congr
    simp_rw [ker_comp, map_comap_eq, range_subtype]
    ext x
    simp only [mem_inf, mem_sup, mem_ker, sub_apply]
    constructor
    · intro ⟨xX, xxh⟩
      refine ⟨x - hc₁.projection x, ⟨?_, ⟨hc₁.projection x, ?_⟩⟩⟩
      · obtain ⟨⟨_, ⟨hp₁, hm₁⟩, y, hl₁, hx₁⟩, _, ⟨hp₂, hm₂⟩, _, hl₂, hx₂⟩ := xX
        constructor
        · simp_rw [← hc₁.projection_eq_self_sub_projection, IsCompl.projection_apply_mem, ← hx₁]
          simpa [cmem_zero hl₁ hc₁.symm, hc₁.symm.projection_apply_left ⟨_, hm₁⟩]
        · simp_rw [sub_eq_zero.mp xxh, ← hc₂.projection_eq_self_sub_projection,
            IsCompl.projection_apply_mem, ← hx₂]
          simpa [cmem_zero hl₂ hc₂.symm, hc₂.symm.projection_apply_left ⟨_, hm₂⟩]
      · simp_rw [IsCompl.projection_apply_mem, true_and, sub_add_cancel, and_true,
          sub_eq_zero.mp xxh, IsCompl.projection_apply_mem]
    · rintro ⟨a, b, c, d, e⟩
      refine ⟨⟨⟨a, b.1, c, d.1, e⟩, ⟨a, b.2, c, d.2, e⟩⟩, ?_⟩
      simp [← e, hc₁.projection_isProj.map_id _ d.1, hc₂.projection_isProj.map_id _ d.2,
        cmem_zero b.1.2 hc₁, cmem_zero b.2.2 hc₂]

omit [LinearOrder R] [IsOrderedRing R] in
private lemma aux'' {P₁ P₂ : Submodule R M} (h₁ : P₁.FG) (h₂ : P₂.FG) (L₁ L₂ : Submodule R M)
    (hd₁ : Disjoint P₁ L₁) (hd₂ : Disjoint P₂ L₂) :
    ∃ P : Submodule R M, P.FG ∧ (P₁ ⊔ L₁) ⊓ (P₂ ⊔ L₂) = P ⊔ (L₁ ⊓ L₂) := by
  obtain ⟨M₁, hle₁, hM₁⟩ := hd₁.exists_isCompl
  obtain ⟨M₂, hle₂, hM₂⟩ := hd₂.exists_isCompl
  have h₁ : (P₁ ⊓ M₁).FG := FG.of_le h₁ inf_le_left
  have h₂ : (P₂ ⊓ M₂).FG := FG.of_le h₂ inf_le_left
  obtain ⟨P, Pfg, Pdist⟩ := aux' h₁ h₂ inf_le_right inf_le_right hM₁.symm hM₂.symm
  use P
  simp [← Pdist, Pfg]
  congr <;> simpa

omit [LinearOrder R] [IsOrderedRing R] in
private lemma aux {P₁ P₂ : Submodule R M} (h₁ : P₁.FG) (h₂ : P₂.FG) (L₁ L₂ : Submodule R M) :
    ∃ P : Submodule R M, P.FG ∧ (P₁ ⊔ L₁) ⊓ (P₂ ⊔ L₂) = P ⊔ (L₁ ⊓ L₂) := by
  obtain ⟨P₁', hle₁, hdis₁, hP₁⟩ := exists_le_disjoint_sup_self P₁ L₁
  obtain ⟨P₂', hle₂, hdis₂, hP₂⟩ := exists_le_disjoint_sup_self P₂ L₂
  simpa [hP₁, hP₂] using aux'' (FG.of_le h₁ hle₁) (FG.of_le h₂ hle₂) L₁ L₂ hdis₁ hdis₂

omit [LinearOrder R] [IsOrderedRing R] in
private lemma auxi {P₁ P₂ : Submodule R M} (h₁ : P₁.FG) (h₂ : P₂.FG) (L₁ L₂ : Submodule R M) :
    ∃ P : Submodule R M, P.FG ∧ (P₁ ⊔ L₁) ⊓ (P₂ ⊔ L₂) = P ⊔ (L₁ ⊓ L₂) := by
  -- obtain ⟨P₁, hle₁, hdis₁, hP₁⟩ := exists_le_disjoint_sup_self P₁ L₁
  -- obtain ⟨P₂, hle₂, hdis₂, hP₂⟩ := exists_le_disjoint_sup_self P₂ L₂
  -- have h₁ : P₁.FG := fg_of_le_fg h₁ hle₁
  -- have h₂ : P₂.FG := fg_of_le_fg h₂ hle₂
  -- rw [← hP₁, ← hP₂]
  set X := (P₁ ⊔ L₁) ⊓ (P₂ ⊔ L₂)
  set L := L₁ ⊓ L₂
  let P₁' := Submodule.restrict X P₁
  let P₂' := Submodule.restrict X P₂
  let L₁' := Submodule.restrict X L₁
  let L₂' := Submodule.restrict X L₂

  obtain ⟨M₁, hM₁⟩ := Submodule.exists_isCompl L₁
  obtain ⟨M₂, hM₂⟩ := Submodule.exists_isCompl L₂
  let P₁ := P₁ ⊓ M₁
  let P₂ := P₂ ⊓ M₂
  have h₁ : P₁.FG := FG.of_le h₁ inf_le_left
  have h₂ : P₂.FG := FG.of_le h₂ inf_le_left
  have hPL₁ : Disjoint P₁ L₁ := hM₁.symm.disjoint.inf_left' _
  have hPL₂ : Disjoint P₂ L₂ := hM₂.symm.disjoint.inf_left' _
  let f₁ := hM₁.projection --
  let f₂ := hM₂.projection
  let f := f₁ - f₂
  let g₁ := hM₁.symm.projection
  let g₂ := hM₂.symm.projection
  let g := g₂ - g₁
  have hfg : f = g := sorry
  have hker : ker f = (P₁ ⊓ P₂) ⊔ (L₁ ⊓ L₂) := sorry
  have him : FG (range g) := sorry
  have iso := LinearMap.quotKerEquivRange f

  obtain ⟨M, hM⟩ := Submodule.exists_isCompl (L₁ ⊔ L₂)
  let P := (P₁ ⊔ L₁) ⊓ (P₂ ⊔ L₂) ⊓ M

  sorry


/-- A polyhedral cone with FGDual linearlity space is itself FGDual. -/
lemma IsPolyhedral.fgdual_of_lineal_fgdual {C : PointedCone R N}
    (hC : C.IsPolyhedral) (hlin : C.lineal.FGDual p) : FGDual p C := by
  obtain ⟨_, hfg, hD⟩ := hC.exists_fg_sup_lineal
  rw [← hD]
  exact sup_fg_fgdual hfg hlin

/-- A polyhedral cone is FGDual if and only if its lineality space is FGDual. -/
lemma IsPolyhedral.fgdual_iff_lineal_fgdual {C : PointedCone R N} {hC : C.IsPolyhedral} :
    C.FGDual p ↔ C.lineal.FGDual p := ⟨FGDual.lineal_fgdual, hC.fgdual_of_lineal_fgdual⟩

variable (p) [Fact (Surjective p)] in
/-- If `C` is a polyhedral cone and `S` is a subspace codisjoint to the linear span of `C`,
  then `C ⊔ S` is FGDual. This is the counterpart to `IsPolyhedral.fgdual_inf_of_disjoint_lineal`.
-/
lemma IsPolyhedral.fgdual_sup_of_codisjoint_span {C : PointedCone R N} (hC : C.IsPolyhedral)
    {S : Submodule R N} (hS : Codisjoint C.linSpan S) : FGDual p (C ⊔ S) := by
  refine fgdual_of_lineal_fgdual (hC.sup_submodule S) (CoFG.fgdual p ?_)
  refine cofg_lineal_of_span_top (hC.sup_submodule _) ?_
  simpa [← coe_sup_submodule_span, Submodule.span_union] using codisjoint_iff.mp hS

variable (p) [Fact (Surjective p)] in
/-- A polyhedral cone `C` can be written as the intersection of a FGDual cone with the
  linear span of `C`. -/
lemma IsPolyhedral.exists_fgdual_inf_span {C : PointedCone R N} (hC : C.IsPolyhedral) :
    ∃ D : PointedCone R N, D.FGDual p ∧ D ⊓ C.linSpan = C := by
  have ⟨S, hS⟩ := Submodule.exists_isCompl (Submodule.span R (C : Set N))
  exact ⟨C ⊔ S, hC.fgdual_sup_of_codisjoint_span p hS.codisjoint,
    sup_inf_submodule_span_of_disjoint hS.disjoint⟩

variable (p) in
/-- Duals generated from a finite set are polyhedral. -/
lemma IsPolyhedral.of_dual_of_finset (s : Finset M) : (dual p s).IsPolyhedral := by
  obtain ⟨D, hfg, hD⟩ := exists_fg_sup_dual p s
  rw [← hD]
  exact .of_fg_sup_submodule hfg _

variable (p) in
/-- Duals of FG cones are polyhedral. -/
lemma IsPolyhedral.of_dual_of_fg (hC : C.FG) : (dual p C).IsPolyhedral := by
  obtain ⟨D, hfg, hD⟩ := FG.exists_fg_sup_dual p hC
  rw [← hD]
  exact .of_fg_sup_submodule hfg _

/-- FGDual cones are polyhedral. -/
lemma IsPolyhedral.of_fgdual {C : PointedCone R N} (hC : C.FGDual p) : C.IsPolyhedral := by
  obtain ⟨D, hfg, rfl⟩ := hC.exists_fg_dual
  exact .of_dual_of_fg p hfg

/-- The intersection of a polyhedral cone with an FG cone is FG. -/
lemma IsPolyhedral.fg_of_inf_fg_submodule (hC : C.IsPolyhedral)
    {S : Submodule R M} (hS : FG S) : FG (C ⊓ S) := by
  obtain ⟨D, hcofg, hD⟩ := hC.exists_fgdual_inf_span .id
  rw [← hD, inf_assoc, ← coe_inf]
  exact inf_fgdual_fg hcofg <| coe_fg <| FG.of_le hS inf_le_right

/-- The intersection of two polyhedral cones is polyhdral. -/
lemma IsPolyhedral.inf (h₁ : C₁.IsPolyhedral) (h₂ : C₂.IsPolyhedral) :
    (C₁ ⊓ C₂).IsPolyhedral := by
  -- The proof reduces the problem to the case of intersecting FG cones using the aux lemma.
  -- Then we can use `inf_fg` from the FG theory.
  obtain ⟨D₁, hfg₁, hD₁⟩ := h₁.exists_fg_sup_lineal
  obtain ⟨D₂, hfg₂, hD₂⟩ := h₂.exists_fg_sup_lineal
  replace hD₁ := congrArg (Submodule.span R ∘ SetLike.coe) hD₁
  replace hD₂ := congrArg (Submodule.span R ∘ SetLike.coe) hD₂
  simp only [Function.comp_apply] at hD₁ hD₂
  rw [← PointedCone.coe_sup_submodule_span, Submodule.span_union] at hD₁ hD₂
  simp only [Submodule.coe_restrictScalars, span_coe_eq_restrictScalars] at hD₁ hD₂
  --
  have h := Submodule.le_span (R := R) (M := M) (s := (C₁ ⊓ C₂ : PointedCone R M))
  replace h := le_trans h <| Set.subset_inter (span_mono inf_le_left) (span_mono inf_le_right)
  --replace h := le_trans h (span_inter_le _ _)
  rw [← Submodule.coe_inf, ← hD₁, ← hD₂] at h
  --
  obtain ⟨P, hPfg, hP⟩ := aux (submodule_span_fg hfg₁) (submodule_span_fg hfg₂) C₁.lineal C₂.lineal
  simp_rw [Submodule.restrictScalars_self, hP] at h
  nth_rw 2 [← ofSubmodule_coe] at h
  rw [Set.le_iff_subset] at h
  rw [SetLike.coe_subset_coe] at h
  --
  rw [← inf_eq_left.mpr h]
  have H := inf_le_inf (lineal_le C₁) (lineal_le C₂)
  rw [coe_sup, inf_sup_assoc_of_submodule_le _ H]
  --
  rw [← inf_idem P, inf_assoc, inf_comm, coe_inf, ← inf_assoc, inf_assoc]
  refine .of_fg_sup_submodule (inf_fg ?_ ?_) _
  · exact h₂.fg_of_inf_fg_submodule hPfg
  · simpa [inf_comm] using h₁.fg_of_inf_fg_submodule hPfg

/-- If `C` is a polyhedral cone and `S` is a submodule disjoint to its lineality, then
  `C ⊓ S` is FG. This is a strengthened version of `IsPolyhedral.fg_inf_of_isCompl`. -/
lemma IsPolyhedral.fg_inf_of_disjoint_lineal (hC : C.IsPolyhedral)
    {S : Submodule R M} (hS : Disjoint C.lineal S) : FG (C ⊓ S) := by
  refine fg_of_fg_lineal (hC.inf <| .of_submodule S) ?_
  simp only [lineal_inf, lineal_submodule, disjoint_iff.mp hS, fg_bot]
  -- TODO: fg_bot should be a simp lemma

variable (p) in
/-- The dual of a polyhedral cone is polyhedral. -/
lemma IsPolyhedral.dual (hC : C.IsPolyhedral) : (dual p C).IsPolyhedral := by
  obtain ⟨D, hDfg, hD⟩ := hC.exists_fg_sup_lineal
  rw [← hD, dual_sup_dual_inf_dual, Submodule.coe_restrictScalars, dual_eq_submodule_dual]
  exact IsPolyhedral.inf (.of_dual_of_fg p hDfg) (.of_submodule _)

variable (p) in
-- I believe proving this requires a lot of other work to be done before (above).
-- Essentially, in a lot of lemmas we need to replace `[Fact (Surjective p)]` by an
-- an assumption about lineal, most likely, that lineal is dual closed.
-- However, the assumption `[Fact (Surjective p)]` is preferable because it can be
-- inferred automatically in the finite dimensional case.
lemma IsPolyhedral.dualClosed_iff_lineal (hC : C.IsPolyhedral) :
    C.DualClosed p ↔ C.lineal.DualClosed p := by
  constructor <;> intro h
  · exact h.lineal
  -- here we need that a dual closed cone + an FG cone stays dual closed. This theory does not
  -- yet exist.
  sorry

variable (p) [Fact (Surjective p.flip)] in
lemma IsPolyhedral.dualClosed (hC : C.IsPolyhedral) : C.DualClosed p := by
  obtain ⟨D, hdual, hD⟩ := hC.exists_fgdual_inf_span p.flip
  rw [← hD]
  exact DualClosed.inf (FGDual.dualClosed hdual)
    (dualClosed_coe <| Submodule.dualClosed p _)

-- This doubling of theorems should be unnecessary if we define `[Fact (Surjective p)]` correctly.
variable (p) [Fact (Surjective p)] in
lemma IsPolyhedral.dualClosed_flip {C : PointedCone R N} (hC : C.IsPolyhedral) :
    C.DualClosed p.flip := by
  rw [← flip_flip p]; exact hC.dualClosed p.flip

variable (p) [Fact (Surjective p.flip)] in
lemma IsPolyhedral.dual_flip_dual (hC : C.IsPolyhedral) :
  PointedCone.dual p.flip (PointedCone.dual p C) = C := hC.dualClosed p

-- This doubling of theorems should be unnecessary if we define `[Fact (Surjective p)]` correctly.
variable (p) [Fact (Surjective p)] in
lemma IsPolyhedral.dual_dual_flip {C : PointedCone R N} (hC : C.IsPolyhedral) :
    PointedCone.dual p (PointedCone.dual p.flip C) = C := hC.dualClosed_flip p

/- NOTE: some restriction like `IsPerfPair` is necessary. Consider two subspaces S, T that are not
  dual closed and with S ⊓ T = ⊥. The left side is ⊤. But the right side is ⊥ ⊔ ⊥ = ⊥.
  Alterantively, we can assume that C₁ and C₂ are dual closed. But this version must stay
  because type inference makes its assumptions automatic in finite dimensions. Maybe a weaker
  assumoption suffices though (it seems to be the case for FG and FGDual). -/
-- variable (p) [p.IsPerfPair] in
variable (p) [Fact (Surjective p)] in
variable [Fact (Surjective p.flip)] in
lemma IsPolyhedral.dual_inf_dual_sup_dual (hC₁ : C₁.IsPolyhedral) (hC₂ : C₂.IsPolyhedral) :
    PointedCone.dual p (C₁ ∩ C₂) = PointedCone.dual p C₁ ⊔ PointedCone.dual p C₂ := by
  nth_rw 1 [← hC₁.dual_flip_dual p, ← hC₂.dual_flip_dual p,
    ← Submodule.coe_inf, ← dual_sup_dual_inf_dual]
  exact dual_dual_flip p <| (hC₁.dual p).sup (hC₂.dual p)

/- Wishlist:
  * polyhedra are dual closed
  * dual (C ⊓ D) = dual C ⊔ dual D
-/






-- variable (p) [Fact p.IsFaithfulPair] in
-- private lemma IsPolyhedral.dual_fg_of_lineal_cofg' {C : PointedCone R M}
--     (hC : C.IsPolyhedral) (hlin : CoFG C.lineal) : FG (dual p C) := by
--   obtain ⟨_, hfg, hD⟩ := hC.exists_fg_sup_lineal
--   rw [← hD]
--   exact FGDual.dual_fg (sup_fg_cofg hfg <| CoFG.cofg p.flip hlin)

variable (p) [Fact (Surjective p)] in
@[deprecated fgdual_of_lineal_cofg (since := "...")]
private lemma IsPolyhedral.fgdual_of_lineal_cofg {C : PointedCone R N}
    (hC : C.IsPolyhedral) (hlin : CoFG C.lineal) : FGDual p C := by
  obtain ⟨_, hfg, hD⟩ := hC.exists_fg_sup_lineal
  rw [← hD]
  exact sup_fg_fgdual hfg (CoFG.fgdual p hlin)

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
  have h := hC'.fgdual_of_lineal_cofg p.flip (hC'.cofg_lineal_of_span_top hh)
  --have h' := FGDual.dual_fg h -- we dont' need FG, we need polyhedral
  have h' : (PointedCone.dual p C').IsPolyhedral := sorry -- FG.isPolyhedral (FGDual.dual_fg h)
  have h'' := FGDual.dualClosed h
  rw [← h'']
  have h'' := Submodule.dualClosed p (Submodule.span R C)
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
--     (hC : C.IsPolyhedral) (hlin : CoFG C.lineal) :
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
--   obtain ⟨E, hfg, hE⟩ := (isPolyhedral_of_dual_of_fg .id hfg).exists_fg_sup_lineal
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
--     rw [DualClosed.dual_lineal_span_dual]
--     ·
--       sorry
--     · sorry
--     -- exact left_eq_sup.mp hE.symm

end Field

section IsNoetherian

variable [IsNoetherian R M]
/-- A polyhedral cone is finitely generated. -/
lemma IsPolyhedral.FG (hC : C.IsPolyhedral) : C.FG :=
  fg_of_fg_lineal hC (IsNoetherian.noetherian _)

lemma IsPolyhedral.iff_FG : C.IsPolyhedral ↔ C.FG := ⟨IsPolyhedral.FG, FG.isPolyhedral⟩

end IsNoetherian










-- ## POLYHEDRAL CONE


variable {R : Type*} [Ring R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]

variable (R M) in
/-- A cone is polyhedral if its salient quotient is finitely generated. -/
structure PolyhedralCone extends PointedCone R M where
  isPolyhedral : IsPolyhedral toSubmodule

namespace PolyhedralCone

-- ## BOILERPLATE

@[coe] abbrev toPointedCone (C : PolyhedralCone R M) : PointedCone R M := C.toSubmodule

instance : Coe (PolyhedralCone R M) (PointedCone R M) := ⟨toPointedCone⟩

--set_option linter.unusedSectionVars false in
lemma toPointedCone_injective :
    Injective (toPointedCone : PolyhedralCone R M → PointedCone R M) :=
  fun C D h => by cases C; cases D; cases h; rfl

instance : SetLike (PolyhedralCone R M) M where
  coe C := C.toPointedCone
  coe_injective' := SetLike.coe_injective.comp toPointedCone_injective

instance : PartialOrder (PolyhedralCone R M) := .ofSetLike (PolyhedralCone R M) M

@[simp] lemma coe_toPointedCone (C : PolyhedralCone R M) :
    (C.toPointedCone : Set M) = C := rfl


-- ## FG

variable {C C₁ C₂ : PolyhedralCone R M}

/-- A finitely generated cone is polyhedral. -/
def of_FG {C : PointedCone R M} (hC : C.FG) : PolyhedralCone R M
    := ⟨C, FG.isPolyhedral hC⟩

variable (R) in
/-- The span of finitely many elements as a polyhedral cone. -/
def finspan (s : Finset M) : PolyhedralCone R M := ⟨_, isPolyhedral_of_span_finset s⟩

@[simp] lemma finspan_eq_span (s : Finset M) : finspan R s = span (E := M) R s := rfl

def finspan_lineal (s : Finset M) (S : Submodule R M) : PolyhedralCone R M :=
  ⟨span R s ⊔ S, IsPolyhedral.sup (isPolyhedral_of_span_finset s) (by simp)⟩

variable [IsNoetherian R M] in
/-- A polyhedral cone is finitely generated. -/
def FG {C : PolyhedralCone R M} : C.FG := C.isPolyhedral.FG



-- ## ORDER

def bot : PolyhedralCone R M := ⟨_, .of_submodule ⊥⟩
def top : PolyhedralCone R M := ⟨_, .of_submodule ⊤⟩

-- alias lineal := bot

instance : OrderBot (PolyhedralCone R M) where
  bot := bot
  bot_le P := sorry

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


-- ## DUAL

section CommRing

variable {R : Type*} [CommRing R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}
variable {C C₁ C₂ F : PolyhedralCone R M}

variable (p) [Fact (Surjective p.flip)] in
lemma dualClosed (C : PolyhedralCone R M) : DualClosed p C :=
  sorry -- C.isPolyhedral.dualClosed p

-- variable (p) in
-- lemma dualClosed_iff (C : PolyhedralCone R M) :
--   DualClosed p C ↔ (lineal C).DualClosed p := sorry

-- Duality flips the face lattice

section Field

variable {R : Type*} [Field R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}

variable (p) in
/-- The dual of a finite set interpreted as a polyhedral cone. -/
def findual (s : Finset M) : PolyhedralCone R N := ⟨dual p s, .of_dual_of_finset p s⟩

variable (p) in
@[simp] lemma findual_eq_dual (s : Finset M) : findual p s = dual p s := rfl

variable (p) in
/-- The dual cone of a polyhedral cone. -/
def dual (P : PolyhedralCone R M) : PolyhedralCone R N := ⟨_, P.isPolyhedral.dual p⟩

variable (p) in
@[simp] lemma coe_dual (P : PolyhedralCone R M) : P.dual p = PointedCone.dual p P := rfl

end Field

end CommRing


-- ## SUBMODULE

instance : Coe (Submodule R M) (PolyhedralCone R M) where
  coe S := ⟨_, .of_submodule S⟩

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

-- def salientQuot : PolyhedralCone R (M ⧸ (C : PointedCone R M).lineal) := sorry
--     -- ⟨_, C.isPolyhedral.salientQuot⟩


-- ## NEG

instance : InvolutiveNeg (PolyhedralCone R M) where
  neg C := ⟨_, C.isPolyhedral.neg⟩
  neg_neg := by simp

@[simp] lemma neg_coe (C : PolyhedralCone R M) :
    (-C : PolyhedralCone R M) = -(C : PointedCone R M) := rfl


end PolyhedralCone
