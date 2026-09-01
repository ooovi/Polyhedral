/-
Copyright (c) 2025 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/
module

public import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Finite.Basic
public import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Finite.Face.Basic
public import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Finite.MinkowskiWeyl

/-! This file defines V-polyhedral cones as cones that can be written as the sum of an FG cone
and a submodule. This agrees with FG cones in finite dimensional modules but has the additional
advantage that it is closed under duality in infinite dimensions.

Combinatorially they are equivalent to FG cones.

Main definitions:
* `PointedCone.IsVPolyhedral`.
-/

@[expose] public section

open Function Module OrderDual LinearMap
open Submodule hiding dual DualClosed
open PointedCone

/- TODO:
 * in finite dim, fg iff polyhedral
 * quotients are polyhedral
 * halfspaces are polyhedral
-/

namespace PointedCone

variable {R M N : Type*}

variable [Semiring R] [PartialOrder R] [IsOrderedRing R] in
variable [AddCommMonoid M] [Module R M] in
/-- We implement V-polyhedral cones as sums of FG cones with submodules. This agrees with FG cones
in finite dimensional modules and behaves well with respect to duality in infinite dimensions.

If `R` is a linearly ordered ring, an equivalent defintion is `FG C.salientQuot`. -/
def IsVPolyhedral (C : PointedCone R M) :=
  ∃ D : PointedCone R M, D.FG ∧ ∃ S : Submodule R M, C = D ⊔ S

namespace IsVPolyhedral

section Semiring

variable [Semiring R] [PartialOrder R] [IsOrderedRing R]
variable [AddCommMonoid M] [Module R M]

variable {C C₁ C₂ F : PointedCone R M}

/-- A cone is polyhedral if and only if it is the sum of an FG cone and a submodule. -/
lemma iff_exists_fg_submoduel_eq_sup :
    C.IsVPolyhedral ↔ ∃ D : PointedCone R M, D.FG ∧ ∃ S : Submodule R M, C = D ⊔ S := .rfl

/-- Submodules are polyhedral cones. -/
@[simp] lemma of_submodule (S : Submodule R M) :
    (S : PointedCone R M).IsVPolyhedral := ⟨⊥, fg_bot, S, by simp⟩

/-- FG cones are polyhedral cones. -/
@[simp] lemma of_fg (hC : C.FG) : C.IsVPolyhedral := ⟨C, hC, ⊥, by simp⟩

alias _root_.PointedCone.FG.isVPolyhedral := of_fg

variable (R) in
/-- The hull of a finite set is a polyhedral cone. -/
lemma of_hull_finite {s : Set M} (hs : s.Finite) : (hull R s).IsVPolyhedral :=
  of_fg <| fg_span hs

variable (R) in
/-- The hull of a finite set is a polyhedral cone. -/
@[simp] lemma of_hull_finset (s : Finset M) : (hull R (s : Set M)).IsVPolyhedral :=
  of_fg ⟨s, rfl⟩

/-- A ray is a polyhedral cone. -/
@[simp] lemma of_hull_singleton (x : M) : IsVPolyhedral (R ∙₊ x) :=
  of_hull_finite R (Set.finite_singleton x)

lemma of_fg_sup_submodule (hC : C.FG) (S : Submodule R M) : IsVPolyhedral (C ⊔ S) :=
  ⟨C, hC, S, rfl⟩

lemma of_submodule_sup_fg (S : Submodule R M) (hC : C.FG) : IsVPolyhedral (S ⊔ C) :=
  ⟨C, hC, S, by ac_rfl⟩

@[simp] protected lemma bot : (⊥ : PointedCone R M).IsVPolyhedral := .of_submodule ⊥

@[simp] protected lemma top : (⊤ : PointedCone R M).IsVPolyhedral := .of_submodule ⊤

protected lemma sup (hC₁ : C₁.IsVPolyhedral) (hC₂ : C₂.IsVPolyhedral) :
    IsVPolyhedral (C₁ ⊔ C₂) := by
  obtain ⟨D₁, hD₁, S₁, rfl⟩ := hC₁
  obtain ⟨D₂, hD₂, S₂, rfl⟩ := hC₂
  refine ⟨D₁ ⊔ D₂, sup_fg hD₁ hD₂, S₂ ⊔ S₁, ?_⟩
  rw [coe_sup]
  ac_rfl

lemma sup_fg (hC₁ : C₁.IsVPolyhedral) (hC₂ : C₂.FG) : IsVPolyhedral (C₁ ⊔ C₂) :=
  hC₁.sup (of_fg hC₂)

lemma fg_sup (hC₁ : C₁.FG) (hC₂ : C₂.IsVPolyhedral) : IsVPolyhedral (C₁ ⊔ C₂) :=
  .sup (of_fg hC₁) hC₂

lemma sup_submodule (hC : C.IsVPolyhedral) (S : Submodule R M) :
  IsVPolyhedral (C ⊔ S) := hC.sup (of_submodule S)

lemma submodule_sup (S : Submodule R M) (hC : C.IsVPolyhedral) :
  IsVPolyhedral (S ⊔ C) := .sup (of_submodule S) hC

variable {N : Type*} [AddCommMonoid N] [Module R N]

protected lemma map (f : M →ₗ[R] N) (hC : C.IsVPolyhedral) : (C.map f).IsVPolyhedral := by
  obtain ⟨D, hD, S, rfl⟩ := hC
  refine ⟨D.map f, hD.map (f.restrictScalars _), S.map f, ?_⟩
  simp only [map, Submodule.map_sup]
  rfl

@[simp] lemma linearEquiv_map (e : M ≃ₗ[R] N) :
    (C.map e.toLinearMap).IsVPolyhedral ↔ C.IsVPolyhedral where
  mpr := .map e.toLinearMap
  mp h := by simpa [map_map] using h.map e.symm.toLinearMap

-- NOTE: over a Field the surjectivity assumption is not necessary because we can intersect
--   `C` with `f.range`, which is still FG.
-- TODO: move
lemma _root_.PointedCone.FG.exists_fg_eq_map_of_surjective {f : N →ₗ[R] M} (hf : Surjective f)
    (hC : C.FG) : ∃ D : PointedCone R N, D.FG ∧ C = D.map f :=
  Submodule.FG.exists_fg_eq_map_of_surjective (R := Nonneg R) hf hC

end Semiring

section AddCommGroup

variable [Semiring R] [PartialOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]

variable {C C₁ C₂ F : PointedCone R M}

-- TODO: move
/- TODO: does this need AddCommGroup? Can I do it more directly without going via
  `exists_fg_eq_map_of_surjective`? -/
omit [PartialOrder R] [IsOrderedRing R] in
lemma _root_.Submodule.FG.exists_fg_comap_eq_sup_ker_of_surjective {f : N →ₗ[R] M}
    (hf : Surjective f) {S : Submodule R M} (hS : S.FG) :
      ∃ T : Submodule R N, T.FG ∧ S.comap f = T ⊔ f.ker := by
  obtain ⟨T, hT, rfl⟩ := hS.exists_fg_eq_map_of_surjective hf
  rw [comap_map_eq]
  exact ⟨T, hT, rfl⟩

-- TODO: move
lemma _root_.PointedCone.FG.exists_fg_comap_eq_sup_ker_of_surjective {f : N →ₗ[R] M}
    (hf : Surjective f) (hC : C.FG) : ∃ D : PointedCone R N, D.FG ∧ C.comap f = D ⊔ f.ker :=
  Submodule.FG.exists_fg_comap_eq_sup_ker_of_surjective (R := Nonneg R) hf hC

lemma comap_fg_of_surjective {f : N →ₗ[R] M} (hf : Surjective f) (hC : C.FG) :
    (C.comap f).IsVPolyhedral := by
  obtain ⟨D, hD, rfl⟩ := hC.exists_fg_eq_map_of_surjective hf
  simp only [map, comap, comap_map_eq]
  exact ⟨D, hD, by aesop⟩

-- TODO: move (also golf, this is AI-written)
omit [PartialOrder R] [IsOrderedRing R] in
lemma comap_sup_of_surjective {f : M →ₗ[R] N} (hf : Function.Surjective f) (D S : Submodule R N) :
    (D ⊔ S).comap f = D.comap f ⊔ S.comap f := by
  apply le_antisymm
  · intro x hx
    rw [Submodule.mem_comap] at hx
    rw [Submodule.mem_sup] at hx ⊢
    rcases hx with ⟨d, hd, s, hs, hds⟩
    rcases hf d with ⟨y, rfl⟩
    rcases hf s with ⟨z, rfl⟩
    refine ⟨y + (x - (y + z)), ?_, z, ?_, ?_⟩
    · rw [Submodule.mem_comap]
      have hk : f (x - (y + z)) = 0 := by
        rw [map_sub, map_add, hds.symm, sub_self]
      rw [map_add, hk, add_zero]
      exact hd
    · rw [Submodule.mem_comap]
      exact hs
    · abel
  · exact sup_le (comap_mono le_sup_left) (comap_mono le_sup_right)

-- NOTE: over a Field the surjectivity assumption is not necessary because we can intersect
--   `C` with `f.range`, which is still polyhedral.
lemma comap_of_surjective {f : N →ₗ[R] M} (hf : Surjective f) (hC : C.IsVPolyhedral) :
    (C.comap f).IsVPolyhedral := by
  obtain ⟨D, hD, S, rfl⟩ := hC
  unfold comap
  rw [comap_sup_of_surjective]
  · refine IsVPolyhedral.sup (comap_fg_of_surjective hf hD) ?_
    change IsVPolyhedral <| ofSubmodule <| Submodule.comap f S
    exact of_submodule _
  · exact hf

/-- The preimage of a cone is polyhedral if and only if the cone itself is polyhdral,
assuming that the map is surjective. -/
lemma comap_iff_of_surjective {f : N →ₗ[R] M} (hf : Surjective f) :
    (C.comap f).IsVPolyhedral ↔ C.IsVPolyhedral where
  mp h := by
    have h := h.map f
    unfold map comap at h
    rwa [map_comap_eq_of_surjective] at h
    exact hf
  mpr := comap_of_surjective hf

end AddCommGroup

section Ring

variable [Ring R] [LinearOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]

variable {C C₁ C₂ F : PointedCone R M}

/- NOTE: The proof below is AI generated and likely one can extract some intermediate lemmas
of independent interest -/
/-- A cone is polyhedral if and only if it is the sum of a salient FG cone and a submodule. -/
lemma exists_fg_salient_submoduel_eq_sup
    [NoZeroSMulDivisors R (M ⧸ (C.lineal : Submodule R M))]
    (hC : C.IsVPolyhedral) :
    ∃ D : PointedCone R M, D.FG ∧ Salient D ∧ C = D ⊔ C.lineal := by classical
  obtain ⟨D, hD, S, hCDS⟩ := hC
  have hCD : C = D ⊔ C.lineal := by
    have hS := submodule_le_lineal (hCDS ▸ le_sup_right)
    apply le_antisymm
    · exact hCDS.le.trans <| sup_le le_sup_left fun x hx ↦
        (show (C.lineal : PointedCone R M) ≤ D ⊔ C.lineal from le_sup_right) (hS hx)
    · exact sup_le (hCDS ▸ le_sup_left) (lineal_le C)
  obtain ⟨s, hs⟩ := hD.map (C.lineal.mkQ.restrictScalars (Nonneg R))
  let t : Finset (M ⧸ C.lineal) := s.erase 0
  have ht : hull R (t : Set (M ⧸ C.lineal)) = hull R (s : Set (M ⧸ C.lineal)) := by
    by_cases h₀ : 0 ∈ s
    · rw [← Finset.insert_erase h₀]
      simp [t]
    · simp [t, h₀]
  let T := hull R (surjInv (Submodule.mkQ_surjective C.lineal) '' (t : Set _))
  refine ⟨T, ?_, ?_, ?_⟩
  · exact fg_span (t.finite_toSet.image _)
  · apply salient_hull_surjInv (by simp [t])
    have hs : hull R (t : Set _) = D.quot C.lineal := ht.trans hs
    rw [hs, ← sup_quot_eq_quot, ← hCD, ← salientQuot_eq_quot_lineal]
    exact salientQuot_salient C
  · refine hCD.trans <| quot_eq_iff_sup_eq.mp ?_
    simp only [map_hull, mkQ_apply, Set.image_image, surjInv_eq, Set.image_id', T]
    exact (ht.trans hs).symm

/-- A polyhedral cone is the sum of an FG cone with its lineality space. -/
lemma exists_fg_eq_sup_lineal (hC : C.IsVPolyhedral) :
    ∃ D : PointedCone R M, D.FG ∧ C = D ⊔ C.lineal := by
  obtain ⟨D, hD, S, h⟩ := hC
  refine ⟨D, hD, le_antisymm ?_ (by simp [h])⟩
  have : lineal S ≤ C.lineal := lineal_mono (by simp [h])
  rw [submodule_lineal] at this
  nth_rw 1 [h]
  apply sup_le_sup_left
  exact this

/-- A cone is polyhedral if and only if it is the sum of an FG cone with its lineality space. -/
lemma exists_fg_eq_sup_lineal_iff :
    C.IsVPolyhedral ↔ ∃ D : PointedCone R M, D.FG ∧ C = D ⊔ C.lineal where
  mpr := by
    rintro ⟨D, hD, h⟩
    exact ⟨D, hD, C.lineal, h⟩
  mp := exists_fg_eq_sup_lineal

/-- A polyhedral cone with FG lineality space is FG. -/
lemma fg_of_fg_lineal (hC : C.IsVPolyhedral) (h : C.lineal.FG) : C.FG := by
  obtain ⟨D, hD, hD'⟩ := hC.exists_fg_eq_sup_lineal
  rw [hD']
  exact Submodule.sup_fg hD (FG.coe_fg_iff.mpr h)

/-- If the lineality space is FG then a cone is polyhedral if and only if it is FG. -/
lemma iff_fg_of_fg_lineal {h : C.lineal.FG} : C.IsVPolyhedral ↔ C.FG :=
  ⟨(IsVPolyhedral.fg_of_fg_lineal · h), FG.isVPolyhedral⟩

/-- A salient polyhedral cone is FG. -/
lemma fg_of_salient (hC : C.IsVPolyhedral) (hsal : C.Salient) : C.FG :=
  hC.fg_of_fg_lineal (by simpa [salient_iff_lineal_bot.mp hsal] using fg_bot)

/-- A salient cone is polyhedral if and only if it is FG. -/
lemma iff_fg_of_salient (hC : C.Salient) : C.IsVPolyhedral ↔ C.FG :=
  ⟨(IsVPolyhedral.fg_of_salient · hC), FG.isVPolyhedral⟩

lemma quot (hC : C.IsVPolyhedral) (S : Submodule R M) :
    (C.quot S).IsVPolyhedral := hC.map _

lemma salientQuot_fg (hC : C.IsVPolyhedral) : FG C.salientQuot := by
  obtain ⟨D, hD, hCD⟩ := hC.exists_fg_eq_sup_lineal
  have hq := congrArg (PointedCone.quot · C.lineal) hCD
  rw [salientQuot_eq_quot_lineal, hq, sup_quot_eq_quot]
  exact quot_fg hD C.lineal

lemma iff_salientQuot_fg : FG C.salientQuot ↔ C.IsVPolyhedral where
  mpr := salientQuot_fg
  mp h := by
    obtain ⟨D, hD, hCD⟩ := h.exists_fg_eq_map_of_surjective (mkQ_surjective C.lineal)
    refine ⟨D, hD, C.lineal, ?_⟩
    exact (sup_eq_left.mpr (lineal_le C)).symm.trans (quot_eq_iff_sup_eq.mp hCD)

lemma salientQuot (hC : C.IsVPolyhedral) : IsVPolyhedral C.salientQuot :=
  hC.salientQuot_fg.isVPolyhedral

lemma finSalRank (hC : C.IsVPolyhedral) : C.FinSalRank :=
  hC.salientQuot_fg.finRank

open Pointwise

@[simp] protected lemma neg_iff : (-C).IsVPolyhedral ↔ C.IsVPolyhedral where
  mpr := fun hC => by simpa only [← map_id_eq_neg] using hC.map _
  mp hC := by
    simp [← map_id_eq_neg] at hC
    simpa [map_map] using hC.map (-.id)

protected lemma neg (hC : C.IsVPolyhedral) : (-C).IsVPolyhedral := by simpa using hC

section IsNoetherian

variable [IsNoetherian R M]

/-- A polyhedral cone is finitely generated. This assumes that the ambient module is noetherian. -/
protected lemma fg (hC : C.IsVPolyhedral) : C.FG :=
  fg_of_fg_lineal hC <| IsNoetherian.noetherian _

lemma iff_fg : C.IsVPolyhedral ↔ C.FG := ⟨IsVPolyhedral.fg, FG.isVPolyhedral⟩

end IsNoetherian

section IsNoetherianRing

variable [IsNoetherianRing R]

-- MOVE
lemma _root_.PointedCone.submodule_fg_of_le_fg (hC : C.FG) {S : Submodule R M} (hS : S ≤ C) :
    S.FG := by
  refine .of_le (Submodule.FG.span hC) ?_
  rw [← ofSubmodule_le_ofSubmodule]
  exact le_trans hS Submodule.le_span

lemma fg_of_span_fg (hC : C.IsVPolyhedral) (h : (span R C : Submodule R M).FG) : C.FG := by
  obtain ⟨D, hD, S, rfl⟩ := hC
  refine Submodule.sup_fg hD (FG.coe_fg (.of_le h ?_))
  rw [← ofSubmodule_le_ofSubmodule]
  exact le_trans le_sup_right Submodule.le_span

lemma fg_iff_span_fg (hC : C.IsVPolyhedral) : C.FG ↔ (span R C : Submodule R M).FG :=
  ⟨.span, fg_of_span_fg hC⟩

lemma fg_iff_lineal_fg (hC : C.IsVPolyhedral) : C.FG ↔ C.lineal.FG :=
  ⟨lineal_fg, fg_of_fg_lineal hC⟩

end IsNoetherianRing

end Ring

section CommRing

variable [CommRing R] [LinearOrder R] [IsOrderedRing R] -- Q: do I need Comm?
variable [AddCommGroup M] [Module R M]

variable {C C₁ C₂ F : PointedCone R M}

/-- If `C` is polyhedral and `S` is a submodule complementary to `C`'s linearlity space,
  then `C ⊓ S` is FG. A stronger version that only requires `S` to be disjoint to the lineality
  is `IsVPolyhedral.fg_inf_of_disjoint_lineal`. -/
lemma fg_inf_of_isCompl (hC : C.IsVPolyhedral) {S : Submodule R M} (hS : IsCompl C.lineal S) :
    FG (C ⊓ S) := by
  obtain ⟨D, hD, hCD⟩ := hC.exists_fg_eq_sup_lineal
  refine FG.linearEquiv (IsCompl.map_mkQ_equiv_inf hS C.lineal_le) ?_
  have hquot := congrArg (fun K : PointedCone R M ↦ K.quot C.lineal) hCD
  simp only [sup_quot_eq_quot] at hquot
  rw [hquot]
  exact hD.map _

end CommRing

section DivisionRing

variable [DivisionRing R] [LinearOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M]

variable {C C₁ C₂ F : PointedCone R M}

/-- A polyhedral cone is FG if and only if its lineality space is FG. -/
lemma fg_iff_fg_lineal {hC : C.IsVPolyhedral} : C.FG ↔ C.lineal.FG :=
  ⟨lineal_fg, hC.fg_of_fg_lineal⟩

end DivisionRing

section Field

variable [Field R] [LinearOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]

variable {p : M →ₗ[R] N →ₗ[R] R}

variable {C C₁ C₂ F : PointedCone R M}

-- ## DUAL

-- FIX: fix `fg_inf_of_isCompl` first
-- Q: Is DivisionRing necessary?
/-- The lineality space of a full-dimensional polyhedral cone is CoFG. -/
lemma cofg_lineal_of_span_top (hC : C.IsVPolyhedral)
    (h : Submodule.span R (C : Set M) = ⊤) : CoFG C.lineal := by
  obtain ⟨_, hS⟩ := Submodule.exists_isCompl C.lineal
  have hh := congrArg (Submodule.span R ∘ SetLike.coe) <| inf_sup_lineal hS.codisjoint
  simp only [Function.comp_apply, h, ← coe_sup_submodule_span, Submodule.coe_restrictScalars,
    Submodule.span_union, span_coe_eq_restrictScalars] at hh
  refine FG.codisjoint_cofg (codisjoint_iff.mpr hh) (FG.span_fg <| hC.fg_inf_of_isCompl hS)

-- lemma IsVPolyhedral.exists_fg_salient_sup_lineal (hC : C.IsVPolyhedral) :
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

/-- A polyhedral cone with DualFG linearlity space is itself DualFG. -/
lemma dualfg_of_lineal_dualfg {C : PointedCone R N}
    (hC : C.IsVPolyhedral) (hlin : C.lineal.DualFG p) : DualFG p C := by
  obtain ⟨_, hfg, hD⟩ := hC.exists_fg_eq_sup_lineal
  rw [hD]
  exact sup_fg_dualfg hfg hlin

/-- A polyhedral cone is DualFG if and only if its lineality space is DualFG. -/
lemma dualfg_iff_lineal_dualfg {C : PointedCone R N} {hC : C.IsVPolyhedral} :
    C.DualFG p ↔ C.lineal.DualFG p :=
  ⟨DualFG.lineal_dualfg, hC.dualfg_of_lineal_dualfg⟩

variable (p) [Fact (Surjective p)] in
/-- If `C` is a polyhedral cone and `S` is a subspace codisjoint to the linear span of `C`,
  then `C ⊔ S` is DualFG. This is the counterpart to `IsVPolyhedral.dualfg_inf_of_disjoint_lineal`.
-/
lemma dualfg_sup_of_codisjoint_span {C : PointedCone R N} (hC : C.IsVPolyhedral)
    {S : Submodule R N} (hS : Codisjoint (span R C) S) : DualFG p (C ⊔ S) := by
  refine dualfg_of_lineal_dualfg (hC.sup_submodule S) (CoFG.dualfg p ?_)
  refine cofg_lineal_of_span_top (hC.sup_submodule _) ?_
  simpa [← coe_sup_submodule_span, Submodule.span_union] using codisjoint_iff.mp hS

variable (p) [Fact (Surjective p)] in
/-- A polyhedral cone `C` can be written as the intersection of a DualFG cone with the
  linear span of `C`. -/
lemma exists_dualfg_inf_span {C : PointedCone R N} (hC : C.IsVPolyhedral) :
    ∃ D : PointedCone R N, D.DualFG p ∧ D ⊓ (span R (C : Set N)) = C := by
  have ⟨S, hS⟩ := Submodule.exists_isCompl (Submodule.span R (C : Set N))
  exact ⟨C ⊔ S, hC.dualfg_sup_of_codisjoint_span p hS.codisjoint,
    sup_inf_submodule_span_of_disjoint hS.disjoint⟩

variable (p) in
/-- Duals generated from a finite set are polyhedral. -/
lemma of_dual_of_finset (s : Finset M) : (dual p s).IsVPolyhedral := by
  obtain ⟨D, hfg, hD⟩ := exists_fg_sup_dual p s
  rw [← hD]
  exact .of_fg_sup_submodule hfg _

variable (p) in
/-- Duals of FG cones are polyhedral. -/
lemma of_dual_of_fg (hC : C.FG) : (dual p C).IsVPolyhedral := by
  obtain ⟨D, hfg, hD⟩ := FG.exists_fg_sup_dual p hC
  rw [← hD]
  exact .of_fg_sup_submodule hfg _

/-- DualFG cones are polyhedral. -/
lemma of_dualfg {C : PointedCone R N} (hC : C.DualFG p) : C.IsVPolyhedral := by
  obtain ⟨D, hfg, rfl⟩ := hC.exists_fg_dual
  exact .of_dual_of_fg p hfg

/-- The intersection of a polyhedral cone with an FG cone is FG. -/
lemma fg_of_inf_fg_submodule (hC : C.IsVPolyhedral)
    {S : Submodule R M} (hS : S.FG) : FG (C ⊓ S) := by
  obtain ⟨D, hcofg, hD⟩ := hC.exists_dualfg_inf_span .id
  rw [← hD, inf_assoc, ← coe_inf]
  exact inf_dualfg_fg hcofg <| FG.coe_fg <| FG.of_le hS inf_le_right

lemma of_dualfg_inf_submodule (hC : C.DualFG .id) (S : Submodule R M) :
    (C ⊓ S).IsVPolyhedral := by
  have h := (of_dualfg (DualFG.restrict_id hC S)).map S.subtype
  change ((C.restrict S).embed).IsVPolyhedral at h
  simpa [inf_comm] using h

lemma of_submodule_inf_dualfg (S : Submodule R M) (hC : C.DualFG .id) :
    ((S : PointedCone R M) ⊓ C).IsVPolyhedral := by
  rw [inf_comm]
  exact of_dualfg_inf_submodule hC S

/-- The intersection of two polyhedral cones is polyhedral. -/
lemma inf (h₁ : C₁.IsVPolyhedral) (h₂ : C₂.IsVPolyhedral) : (C₁ ⊓ C₂).IsVPolyhedral := by
  obtain ⟨D₁, hD₁, hD₁eq⟩ := h₁.exists_dualfg_inf_span .id
  obtain ⟨D₂, hD₂, hD₂eq⟩ := h₂.exists_dualfg_inf_span .id
  rw [← hD₁eq, ← hD₂eq]
  let S : Submodule R M := span R C₁ ⊓ span R C₂
  rw [show (D₁ ⊓ span R (C₁ : Set M)) ⊓ (D₂ ⊓ span R (C₂ : Set M)) = (D₁ ⊓ D₂) ⊓ S by
    ext x; simp [S, and_assoc, and_left_comm]]
  exact of_dualfg_inf_submodule (hD₁.inf hD₂) S

protected lemma comap (f : N →ₗ[R] M) (hC : C.IsVPolyhedral) :
    (C.comap f).IsVPolyhedral := by
  obtain ⟨D, hD, hDC⟩ := hC.exists_dualfg_inf_span .id
  rw [← hDC]
  let S : Submodule R N := (span R (C : Set M)).comap f
  rw [show (D ⊓ span R (C : Set M)).comap f = D.comap f ⊓ S by
    ext x; simp [S]]
  exact of_dualfg_inf_submodule (DualFG.comap hD f).id S

/-- If `C` is a polyhedral cone and `S` is a submodule disjoint to its lineality, then
  `C ⊓ S` is FG. This is a strengthened version of `IsVPolyhedral.fg_inf_of_isCompl`. -/
lemma fg_inf_of_disjoint_lineal (hC : C.IsVPolyhedral)
    {S : Submodule R M} (hS : Disjoint C.lineal S) : FG (C ⊓ S) := by
  refine fg_of_fg_lineal (hC.inf <| .of_submodule S) ?_
  simp only [lineal_inf, submodule_lineal, disjoint_iff.mp hS, fg_bot]
  -- TODO: fg_bot should be a simp lemma

variable (p) in
/-- The dual of a polyhedral cone is polyhedral. -/
lemma dual (hC : C.IsVPolyhedral) : (dual p C).IsVPolyhedral := by
  obtain ⟨D, hDfg, hD⟩ := hC.exists_fg_eq_sup_lineal
  rw [hD, dual_sup_dual_inf_dual, Submodule.coe_restrictScalars, dual_eq_submodule_dual]
  exact .inf (.of_dual_of_fg p hDfg) (.of_submodule _)

/- NOTE: This currently relies on the unproven `DualClosed.fg_sup_submodule_dualClosed`, which is
very plausibly true (a proof was also given by ChatGPT). -/
variable (p) in
lemma dualClosed_iff_lineal (hC : C.IsVPolyhedral) :
    C.DualClosed p ↔ C.lineal.DualClosed p := by
  constructor
  · exact DualClosed.lineal
  · intro h
    obtain ⟨D, hD, hD'⟩ := hC.exists_fg_eq_sup_lineal
    rw [hD']
    exact .fg_sup_submodule_dualClosed hD h

variable (p) [Fact (Surjective p.flip)] in
lemma dualClosed (hC : C.IsVPolyhedral) : C.DualClosed p := by
  obtain ⟨D, hdual, hD⟩ := hC.exists_dualfg_inf_span p.flip
  rw [← hD]
  exact DualClosed.inf (DualFG.dualClosed hdual)
    (dualClosed_coe <| Submodule.dualClosed p _)

-- This doubling of theorems should be unnecessary if we define `[Fact (Surjective p)]` correctly.
variable (p) [Fact (Surjective p)] in
lemma dualClosed_flip {C : PointedCone R N} (hC : C.IsVPolyhedral) :
    C.DualClosed p.flip := by
  rw [← flip_flip p]; exact hC.dualClosed p.flip

variable (p) [Fact (Surjective p.flip)] in
lemma dual_flip_dual (hC : C.IsVPolyhedral) :
  PointedCone.dual p.flip (PointedCone.dual p C) = C := hC.dualClosed p

-- This doubling of theorems should be unnecessary if we define `[Fact (Surjective p)]` correctly.
variable (p) [Fact (Surjective p)] in
lemma dual_dual_flip {C : PointedCone R N} (hC : C.IsVPolyhedral) :
    PointedCone.dual p (PointedCone.dual p.flip C) = C := hC.dualClosed_flip p

lemma dual_inf_dual_sup_dual_of_dualClosed
    (hC₁ : C₁.DualClosed p) (hC₂ : C₂.DualClosed p)
    (hdual : (PointedCone.dual p C₁ ⊔ PointedCone.dual p C₂).DualClosed p.flip) :
    PointedCone.dual p (C₁ ∩ C₂) = PointedCone.dual p C₁ ⊔ PointedCone.dual p C₂ := by
  nth_rw 1 [← hC₁, ← hC₂, ← Submodule.coe_inf, ← dual_sup_dual_inf_dual]
  exact hdual

/- NOTE: some restriction like `IsPerfPair` is necessary. Consider two subspaces S, T that are not
  dual closed and with S ⊓ T = ⊥. The left side is ⊤. But the right side is ⊥ ⊔ ⊥ = ⊥.
  Alterantively, we can assume that C₁ and C₂ are dual closed. But this version must stay
  because type inference makes its assumptions automatic in finite dimensions. Maybe a weaker
  assumoption suffices though (it seems to be the case for FG and DualFG). -/
-- variable (p) [p.IsPerfPair] in
variable (p) [Fact (Surjective p)] [Fact (Surjective p.flip)] in
lemma dual_inf_dual_sup_dual (hC₁ : C₁.IsVPolyhedral) (hC₂ : C₂.IsVPolyhedral) :
    PointedCone.dual p (C₁ ∩ C₂) = PointedCone.dual p C₁ ⊔ PointedCone.dual p C₂ := by
  nth_rw 1 [← hC₁.dual_flip_dual p, ← hC₂.dual_flip_dual p,
    ← Submodule.coe_inf, ← dual_sup_dual_inf_dual]
  exact dual_dual_flip p <| (hC₁.dual p).sup (hC₂.dual p)

variable (p) [Fact (Surjective p)] in
private lemma dualfg_of_lineal_cofg {C : PointedCone R N}
    (hC : C.IsVPolyhedral) (hlin : CoFG C.lineal) : DualFG p C := by
  obtain ⟨_, hfg, hD⟩ := hC.exists_fg_eq_sup_lineal
  rw [hD]
  exact sup_fg_dualfg hfg (CoFG.dualfg p hlin)

variable (p) [Fact (Surjective p.flip)] in
lemma exists_isVPolyhedral_dual (hC : C.IsVPolyhedral) :
    ∃ D : PointedCone R N, D.IsVPolyhedral ∧ PointedCone.dual p.flip D = C := by
  exact ⟨PointedCone.dual p C, hC.dual p, hC.dual_flip_dual p⟩

end Field

end IsVPolyhedral

end PointedCone
