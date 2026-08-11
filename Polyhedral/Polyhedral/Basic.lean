/-
Copyright (c) 2025 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/

import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Finite.Basic
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Finite.Face.Basic
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Finite.MinkowskiWeyl

/-! This file defines polyhedral cones via the predicate `PointedCone.IsPolyhedral`. -/

open Function Module OrderDual LinearMap
open Submodule hiding dual DualClosed
open PointedCone

/- TODO:
 * in finite dim, fg iff polyhedral
 * faces are polyhedral
 * quotients are polyhedral
 * halfspaces are polyhedral
 * lattice of polyhedral cones
 * finitely many faces / finite face lattice
 * dual closed
-/

namespace PointedCone

variable {R : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommMonoid M] [Module R M]

/-- We implement polyhedral cones as sums of FG cones with submodules. This agrees with FG cones
in finite dimensional modules and behaves well with respect to duality in infinite dimensions.

If `R` is a linearly ordered ring, an equivalent defintion is `FG C.salientQuot`. -/
def IsPolyhedral (C : PointedCone R M) :=
  ∃ D : PointedCone R M, D.FG ∧ ∃ S : Submodule R M, C = D ⊔ S

namespace IsPolyhedral

section Semiring

variable {R : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommMonoid M] [Module R M]

variable {C C₁ C₂ F : PointedCone R M}

/-- A cone is polyhedral if and only if it is the sum of an FG cone and a submodule. -/
lemma iff_exists_fg_submoduel_eq_sup :
    C.IsPolyhedral ↔ ∃ D : PointedCone R M, D.FG ∧ ∃ S : Submodule R M, C = D ⊔ S := .rfl

/-- Submodules are polyhedral cones. -/
@[simp] lemma of_submodule (S : Submodule R M) :
    (S : PointedCone R M).IsPolyhedral := ⟨⊥, fg_bot, S, by simp⟩

/-- FG cones are polyhedral cones. -/
@[simp] lemma of_fg (hC : C.FG) : C.IsPolyhedral := ⟨C, hC, ⊥, by simp⟩

alias _root_.PointedCone.FG.isPolyhedral := of_fg

variable (R) in
/-- The hull of a finite set is a polyhedral cone. -/
lemma of_hull_finite {s : Set M} (hs : s.Finite) : (hull R s).IsPolyhedral :=
  of_fg <| fg_span hs

variable (R) in
/-- The hull of a finite set is a polyhedral cone. -/
@[simp] lemma of_hull_finset (s : Finset M) : (hull R (s : Set M)).IsPolyhedral :=
  of_fg ⟨s, rfl⟩

/-- A ray is a polyhedral cone. -/
@[simp] lemma of_hull_singleton (x : M) : IsPolyhedral (R ∙₊ x) :=
  of_hull_finite R (Set.finite_singleton x)

lemma of_fg_sup_submodule (hC : C.FG) (S : Submodule R M) : IsPolyhedral (C ⊔ S) :=
  ⟨C, hC, S, rfl⟩

lemma of_submodule_sup_fg (S : Submodule R M) (hC : C.FG) : IsPolyhedral (S ⊔ C) :=
  ⟨C, hC, S, by ac_rfl⟩

@[simp] protected lemma bot : (⊥ : PointedCone R M).IsPolyhedral := .of_submodule ⊥

@[simp] protected lemma top : (⊤ : PointedCone R M).IsPolyhedral := .of_submodule ⊤

protected lemma sup (hC₁ : C₁.IsPolyhedral) (hC₂ : C₂.IsPolyhedral) :
    IsPolyhedral (C₁ ⊔ C₂) := by
  obtain ⟨D₁, hD₁, S₁, rfl⟩ := hC₁
  obtain ⟨D₂, hD₂, S₂, rfl⟩ := hC₂
  refine ⟨D₁ ⊔ D₂, sup_fg hD₁ hD₂, S₂ ⊔ S₁, ?_⟩
  rw [coe_sup]
  ac_rfl

lemma sup_fg (hC₁ : C₁.IsPolyhedral) (hC₂ : C₂.FG) : IsPolyhedral (C₁ ⊔ C₂) :=
  hC₁.sup (of_fg hC₂)

lemma fg_sup (hC₁ : C₁.FG) (hC₂ : C₂.IsPolyhedral) : IsPolyhedral (C₁ ⊔ C₂) :=
  .sup (of_fg hC₁) hC₂

lemma sup_submodule (hC : C.IsPolyhedral) (S : Submodule R M) :
  IsPolyhedral (C ⊔ S) := hC.sup (of_submodule S)

lemma submodule_sup (S : Submodule R M) (hC : C.IsPolyhedral) :
  IsPolyhedral (S ⊔ C) := .sup (of_submodule S) hC

variable {N : Type*} [AddCommMonoid N] [Module R N]

protected lemma map (f : M →ₗ[R] N) (hC : C.IsPolyhedral) : (C.map f).IsPolyhedral := by
  obtain ⟨D, hD, S, rfl⟩ := hC
  refine ⟨D.map f, hD.map (f.restrictScalars _), S.map f, ?_⟩
  simp only [map, Submodule.map_sup]
  rfl

@[simp] lemma linearEquiv_map (e : M ≃ₗ[R] N) :
    (C.map e.toLinearMap).IsPolyhedral ↔ C.IsPolyhedral where
  mpr := .map e.toLinearMap
  mp h := by simpa [map_map] using h.map e.symm.toLinearMap

-- TODO: move this and the below
-- NOTE: over a (Semi)Field the surjectivity assumption is not necessary because we can intersect
--   `C` with `f.range`, which is still FG.
omit [PartialOrder R] [IsOrderedRing R] in
lemma _root_.Submodule.FG.exists_fg_eq_map_of_surjective {f : N →ₗ[R] M}
    (hf : Surjective f) {S : Submodule R M} (hS : S.FG) :
      ∃ T : Submodule R N, T.FG ∧ S = T.map f := by classical
  obtain ⟨s, rfl⟩ := hS
  use span R (Finset.image (surjInv hf) s)
  constructor
  · use Finset.image (surjInv hf) s
  simp [Submodule.map_span, Set.image_image, surjInv_eq]

-- NOTE: over a Field the surjectivity assumption is not necessary because we can intersect
--   `C` with `f.range`, which is still FG.
lemma _root_.PointedCone.FG.exists_fg_eq_map_of_surjective {f : N →ₗ[R] M} (hf : Surjective f)
    (hC : C.FG) : ∃ D : PointedCone R N, D.FG ∧ C = D.map f :=
  Submodule.FG.exists_fg_eq_map_of_surjective (R := Nonneg R) hf hC

end Semiring

section AddCommGroup

variable {R : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]

variable {C C₁ C₂ F : PointedCone R M}

-- TODO: move
/- TODO: does this need AddCommGroup?? Can I do it more directly without going via
  `exists_fg_eq_map_of_surjective`? -/
omit [PartialOrder R] [IsOrderedRing R] in
lemma _root_.Submodule.FG.exists_fg_comap_eq_sup_ker_of_surjective {f : N →ₗ[R] M}
    (hf : Surjective f) {S : Submodule R M} (hS : S.FG) :
      ∃ T : Submodule R N, T.FG ∧ S.comap f = T ⊔ f.ker := by
  obtain ⟨T, hT, rfl⟩ := hS.exists_fg_eq_map_of_surjective hf
  rw [comap_map_eq]
  exact ⟨T, hT, rfl⟩

-- TODO: move
lemma _root_.PointedCOne.FG.exists_fg_comap_eq_sup_ker_of_surjective {f : N →ₗ[R] M}
    (hf : Surjective f) (hC : C.FG) : ∃ D : PointedCone R N, D.FG ∧ C.comap f = D ⊔ f.ker :=
  Submodule.FG.exists_fg_comap_eq_sup_ker_of_surjective (R := Nonneg R) hf hC

lemma comap_fg_of_surjective {f : N →ₗ[R] M} (hf : Surjective f) (hC : C.FG) :
    (C.comap f).IsPolyhedral := by
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
lemma comap_of_surjective {f : N →ₗ[R] M} (hf : Surjective f) (hC : C.IsPolyhedral) :
    (C.comap f).IsPolyhedral := by
  obtain ⟨D, hD, S, rfl⟩ := hC
  unfold comap
  rw [comap_sup_of_surjective]
  · refine IsPolyhedral.sup (comap_fg_of_surjective hf hD) ?_
    change IsPolyhedral <| ofSubmodule <| Submodule.comap f S
    exact of_submodule _
  · exact hf

/-- The preimage of a cone is polyhedral if and only if the cone itself is polyhdral,
assuming that the map is surjective. -/
lemma comap_iff_of_surjective {f : N →ₗ[R] M} (hf : Surjective f) :
    (C.comap f).IsPolyhedral ↔ C.IsPolyhedral where
  mp h := by
    have h := h.map f
    unfold map comap at h
    rwa [map_comap_eq_of_surjective] at h
    exact hf
  mpr := comap_of_surjective hf

end AddCommGroup

section Ring

variable {R : Type*} [Ring R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]

variable {C C₁ C₂ F : PointedCone R M}

/-- A cone is polyhedral if and only if it is the sum of a salient FG cone and a submodule. -/
lemma iff_exists_fg_salient_submoduel_eq_sup (hC : C.IsPolyhedral) :
    ∃ D : PointedCone R M, D.FG ∧ Salient D ∧ C = D ⊔ C.lineal := by
  sorry

/-- A polyhedral cone is the sum of an FG cone with its lineality space. -/
lemma exists_fg_eq_sup_lineal (hC : C.IsPolyhedral) :
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
    C.IsPolyhedral ↔ ∃ D : PointedCone R M, D.FG ∧ C = D ⊔ C.lineal where
  mpr := by
    rintro ⟨D, hD, h⟩
    exact ⟨D, hD, C.lineal, h⟩
  mp := exists_fg_eq_sup_lineal

/-- A polyhedral cone with FG lineality space is FG. -/
lemma fg_of_fg_lineal (hC : C.IsPolyhedral) (h : C.lineal.FG) : C.FG := by
  obtain ⟨D, hD, hD'⟩ := hC.exists_fg_eq_sup_lineal
  rw [hD']
  exact Submodule.sup_fg hD (FG.coe_fg_iff.mpr h)

/-- If the lineality space is FG then a cone is polyhedral if and only if it is FG. -/
lemma iff_fg_of_fg_lineal {h : C.lineal.FG} : C.IsPolyhedral ↔ C.FG :=
  ⟨(IsPolyhedral.fg_of_fg_lineal · h), FG.isPolyhedral⟩

/-- A salient polyhedral cone is FG. -/
lemma fg_of_salient (hC : C.IsPolyhedral) (hsal : C.Salient) : C.FG :=
  hC.fg_of_fg_lineal (by simpa [salient_iff_lineal_bot.mp hsal] using fg_bot)

/-- A salient cone is polyhedral if and only if it is FG. -/
lemma iff_fg_of_salient (hC : C.Salient) : C.IsPolyhedral ↔ C.FG :=
  ⟨(IsPolyhedral.fg_of_salient · hC), FG.isPolyhedral⟩

lemma quot (hC : C.IsPolyhedral) (S : Submodule R M) :
    (C.quot S).IsPolyhedral := hC.map _

-- TODO: prove `C.IsPolyhedral ↔ FG C.salientQuot`

-- lemma salientQuot_fg (hC : C.IsPolyhedral) : FG C.salientQuot := sorry

-- lemma salientQuot (hC : C.IsPolyhedral) : IsPolyhedral C.salientQuot :=
--   hC.salientQuot_fg.isPolyhedral

open Pointwise

@[simp] protected lemma neg_iff : (-C).IsPolyhedral ↔ C.IsPolyhedral where
  mpr := fun hC => by simpa only [← map_id_eq_neg] using hC.map _
  mp hC := by
    simp [← map_id_eq_neg] at hC
    simpa [map_map] using hC.map (-.id)

protected lemma neg (hC : C.IsPolyhedral) : (-C).IsPolyhedral := by simpa using hC

section IsNoetherian

variable [IsNoetherian R M]

/-- A polyhedral cone is finitely generated. This assumes that the ambient module is noetherian. -/
protected lemma fg (hC : C.IsPolyhedral) : C.FG :=
  fg_of_fg_lineal hC <| IsNoetherian.noetherian _

lemma iff_fg : C.IsPolyhedral ↔ C.FG := ⟨IsPolyhedral.fg, FG.isPolyhedral⟩

end IsNoetherian

section IsNoetherianRing

variable [IsNoetherianRing R]

-- MOVE
lemma _root_.PointedCone.submodule_fg_of_le_fg (hC : C.FG) {S : Submodule R M} (hS : S ≤ C) :
    S.FG := by
  refine .of_le (Submodule.FG.span hC) ?_
  rw [← ofSubmodule_le_ofSubmodule]
  exact le_trans hS Submodule.le_span

lemma fg_of_span_fg (hC : C.IsPolyhedral) (h : (span R C : Submodule R M).FG) : C.FG := by
  obtain ⟨D, hD, S, rfl⟩ := hC
  refine Submodule.sup_fg hD (FG.coe_fg (.of_le h ?_))
  rw [← ofSubmodule_le_ofSubmodule]
  exact le_trans le_sup_right Submodule.le_span

lemma fg_iff_span_fg (hC : C.IsPolyhedral) : C.FG ↔ (span R C : Submodule R M).FG :=
  ⟨.span, fg_of_span_fg hC⟩

lemma fg_iff_lineal_fg (hC : C.IsPolyhedral) : C.FG ↔ C.lineal.FG :=
  ⟨lineal_fg, fg_of_fg_lineal hC⟩

end IsNoetherianRing

end Ring

section CommRing

variable {R : Type*} [CommRing R] [LinearOrder R] [IsOrderedRing R] -- do I need Comm?
variable {M : Type*} [AddCommGroup M] [Module R M]

variable {C C₁ C₂ F : PointedCone R M}

/-- If `C` is polyhedral and `S` is a submodule complementary to `C`'s linearlity space,
  then `C ⊓ S` is FG. A stronger version that only requires `S` to be disjoint to the lineality
  is `IsPolyhedral.fg_inf_of_disjoint_lineal`. -/
lemma fg_inf_of_isCompl (hC : C.IsPolyhedral) {S : Submodule R M} (hS : IsCompl C.lineal S) :
    FG (C ⊓ S) := by
  obtain ⟨D, hD, T, rfl⟩ := hC
  #check inf_sup_lineal
  sorry -- hC.linearEquiv <| IsCompl.map_mkQ_equiv_inf hS C.lineal_le

end CommRing


-- ----

-- ## NOTE: this is legacy code, that remains here for transferring some of the proofs.

-- /-- A cone is polyhedral if its salient quotient is finitely generated. -/
-- abbrev IsPolyhedral (C : PointedCone R M) := FG C.salientQuot

-- lemma IsPolyhedral.def : C.IsPolyhedral ↔ FG C.salientQuot := by rfl

-- lemma IsPolyhedral.salientQuot_fg (hC : C.IsPolyhedral) : FG C.salientQuot := hC

-- /-- Submodules are polyhedral cones. -/
-- @[simp] lemma IsPolyhedral.of_submodule (S : Submodule R M) :
--     (S : PointedCone R M).IsPolyhedral := by
--   simp [IsPolyhedral, salientQuot_of_submodule, fg_bot]

-- /-- FG cones are polyhedral. -/
-- lemma FG.isPolyhedral (hC : C.FG) : C.IsPolyhedral := hC.salientQuot_fg

-- lemma IsPolyhedral.bot : (⊥ : PointedCone R M).IsPolyhedral := IsPolyhedral.of_submodule ⊥

-- lemma IsPolyhedral.top : (⊤ : PointedCone R M).IsPolyhedral := IsPolyhedral.of_submodule ⊤

-- lemma IsPolyhedral.salientQuot (hC : C.IsPolyhedral) : IsPolyhedral C.salientQuot :=
--     FG.isPolyhedral hC.salientQuot_fg

-- /-- The hull of a finite set is polyhedral. -/
-- lemma IsPolyhedral.of_hull_finite {s : Set M} (hs : s.Finite) : (hull R s).IsPolyhedral :=
--   FG.isPolyhedral (fg_def.mpr ⟨s, hs, rfl⟩)

-- /-- The hull of a finite set is polyhedral. -/
-- lemma isPolyhedral_of_hull_finset (s : Finset M) : (hull (E := M) R s).IsPolyhedral :=
--   .of_hull_finite s.finite_toSet

-- set_option backward.isDefEq.respectTransparency false in
-- /- If the quotient by any contained submodule is FG, then the cone is polyhedral. -/
-- lemma IsPolyhedral.of_quot_fg {S : Submodule R M} (hS : S ≤ C) (hC : FG (C.quot S)) :
--     C.IsPolyhedral := by
--   simpa only [IsPolyhedral, map, ← factor_comp_mk <| le_lineal hS,
--     restrictScalars_comp, map_comp] using FG.map _ hC

-- /-- The salient quotient of a polyhedral `C` cone can be written as the quotient of an
--    FG cone by the lineality space of `C`. -/
-- lemma IsPolyhedral.exists_finset_hull_quot_lineal (hC : C.IsPolyhedral) :
--     ∃ s : Finset M, (hull R s).quot C.lineal = C.salientQuot := by classical
--   obtain ⟨s, hs⟩ := hC
--   use Finset.image (surjInv <| mkQ_surjective _) s
--   simp only [map_hull, Finset.coe_image, Set.image_image, surjInv_eq, Set.image_id', hs]

-- -- lemma IsPolyhedral.exists_finset_inter_hull_quot_lineal (hC : C.IsPolyhedral) :
-- --     ∃ s : Finset M, (s : Set M) ∩ C.lineal = ∅ ∧ (hull R s).quot C.lineal = C.salientQuot := by
-- --   classical
-- --   obtain ⟨s, hs⟩ := exists_finset_hull_quot_lineal hC
-- --   use {x ∈ s | x ∉ C.lineal}
-- --   constructor
-- --   · ext; simp
-- --   · rw [← hs]
-- --     simp
-- --     ext x
-- --     simp [mem_sup]
-- --     sorry

-- /-- A polyhedral cone can be written as the sum of its lineality space with an FG cone. -/
-- lemma IsPolyhedral.exists_finset_sup_lineal (hC : C.IsPolyhedral) :
--     ∃ s : Finset M, hull R s ⊔ C.lineal = C := by classical
--   obtain ⟨s, hs⟩ := exists_finset_hull_quot_lineal hC
--   exact ⟨s, by simpa [quot_eq_iff_sup_eq] using hs⟩

-- /-- A polyhedral cone can be written as the sum of its lineality space with an FG cone. -/
-- lemma IsPolyhedral.exists_fg_sup_lineal (hC : C.IsPolyhedral) :
--     ∃ D : PointedCone R M, D.FG ∧ D ⊔ C.lineal = C := by
--   obtain ⟨s, hs⟩ := hC.exists_finset_sup_lineal
--   exact ⟨hull R s, fg_span s.finite_toSet, hs⟩


-- /-- A polyhedral cone with FG lineality space is FG. -/
-- lemma IsPolyhedral.fg_of_fg_lineal (hC : C.IsPolyhedral) (h : C.lineal.FG) : C.FG := by
--   obtain ⟨D, hD, hD'⟩ := hC.exists_fg_sup_lineal
--   rw [← hD']
--   exact sup_fg hD (FG.coe_fg_iff.mpr h)

-- /-- If the lineality space is FG then a cone is polyhedral if and only if it is FG. -/
-- lemma IsPolyhedral.iff_fg_of_fg_lineal {h : C.lineal.FG} : C.IsPolyhedral ↔ C.FG :=
--   ⟨(IsPolyhedral.fg_of_fg_lineal · h), FG.isPolyhedral⟩

-- /-- A salient polyhedral cone is FG. -/
-- lemma IsPolyhedral.fg_of_salient (hC : C.IsPolyhedral) (hsal : C.Salient) : C.FG :=
--   hC.fg_of_fg_lineal (by simpa [salient_iff_lineal_bot.mp hsal] using fg_bot)

-- /-- A salient cone is polyhedral if and only if it is FG. -/
-- lemma IsPolyhedral.iff_fg_of_salient (hC : C.Salient) : C.IsPolyhedral ↔ C.FG :=
--   ⟨(IsPolyhedral.fg_of_salient · hC), FG.isPolyhedral⟩

-- section CommRing

-- variable {R : Type*} [CommRing R] [LinearOrder R] [IsOrderedRing R]
-- variable {M : Type*} [AddCommGroup M] [Module R M]
-- variable {N : Type*} [AddCommGroup N] [Module R N]
-- variable {C C₁ C₂ F : PointedCone R M}

-- /-- If `C` is polyhedral and `S` is a submodule complementary to `C`'s linearlity spacen,
--   then `C ⊓ S` is FG. A stronger version that only requires `S` to be disjoint to the lineality
--   is `IsPolyhedral.fg_inf_of_disjoint_lineal`. -/
-- lemma IsPolyhedral.fg_inf_of_isCompl (hC : C.IsPolyhedral)
--     {S : Submodule R M} (hS : IsCompl C.lineal S) : FG (C ⊓ S) :=
--   hC.linearEquiv <| IsCompl.map_mkQ_equiv_inf hS C.lineal_le

-- end CommRing

-- -- ## SUP

-- /-- The sum of an FG cone with a submodule is polyhedral. -/
-- lemma IsPolyhedral.of_fg_sup_submodule (hC : C.FG) (S : Submodule R M) :
--     (C ⊔ S).IsPolyhedral := by
--   refine .of_quot_fg le_sup_right ?_
--   simpa [sup_quot_eq_quot] using quot_fg hC S

-- /-- The sum of two polyhedral cones is polyhedral -/
-- lemma IsPolyhedral.sup (h₁ : C₁.IsPolyhedral) (h₂ : C₂.IsPolyhedral) :
--     (C₁ ⊔ C₂).IsPolyhedral := by
--   obtain ⟨D₁, hD₁, hD₁'⟩ := h₁.exists_fg_sup_lineal
--   obtain ⟨D₂, hD₂, hD₂'⟩ := h₂.exists_fg_sup_lineal
--   rw [← hD₁', ← hD₂', sup_assoc]
--   nth_rw 2 [sup_comm]
--   rw [sup_assoc, ← sup_assoc, ← coe_sup]
--   exact .of_fg_sup_submodule (sup_fg hD₁ hD₂) _

-- /-- The sum of a polyhedral cone with a submodule is polyhedral. -/
-- lemma IsPolyhedral.sup_submodule (hC : C.IsPolyhedral) (S : Submodule R M) :
--     (C ⊔ S).IsPolyhedral := hC.sup (.of_submodule S)

-- /-- The sum of a polyhedral cone with an FG cone is polyhedral. -/
-- lemma IsPolyhedral.sup_fg (hC : C.IsPolyhedral) {D : PointedCone R M} (hD : D.FG) :
--     (C ⊔ D).IsPolyhedral := hC.sup (FG.isPolyhedral hD)

-- -- ## MAP / COMAP

-- set_option backward.isDefEq.respectTransparency false in
-- lemma IsPolyhedral.map (hC : C.IsPolyhedral) (f : M →ₗ[R] N) : (C.map f).IsPolyhedral := by
--   obtain ⟨D, hfg, hD'⟩ := hC.exists_fg_sup_lineal
--   rw [← hD']
--   simp only [PointedCone.map, Submodule.map_sup] -- `map` should be an abbrev
--   refine sup ?_ ?_
--   · exact FG.isPolyhedral (FG.map _ hfg)
--   · rw [← restrictScalars_map]
--     simp

-- lemma IsPolyhedral.comap (hC : C.IsPolyhedral) (f : N →ₗ[R] M) : (C.comap f).IsPolyhedral := by
--   unfold IsPolyhedral PointedCone.salientQuot quot at *
--   -- apply FG.map
--   rw [comap_lineal]
--   sorry

-- lemma IsPolyhedral.quot (hC : C.IsPolyhedral) (S : Submodule R M) :
--     (C.quot S).IsPolyhedral := hC.map _

-- open Pointwise in
-- @[simp] lemma IsPolyhedral.neg_iff : (-C).IsPolyhedral ↔ C.IsPolyhedral where
--   mp := by
--     intro hC;
--     simp [← map_id_eq_neg] at hC;
--     simpa [map_map] using hC.map (-.id)
--   mpr := fun hC => by simpa only [← map_id_eq_neg] using hC.map _

-- open Pointwise in
-- lemma IsPolyhedral.neg (hC : C.IsPolyhedral) : (-C).IsPolyhedral := by simpa using hC


section DivisionRing

variable {R : Type*} [DivisionRing R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

variable {C C₁ C₂ F : PointedCone R M}

/-- A polyhedral cone is FG if and only if its lineality space is FG. -/
lemma fg_iff_fg_lineal {hC : C.IsPolyhedral} : C.FG ↔ C.lineal.FG :=
  ⟨lineal_fg, hC.fg_of_fg_lineal⟩

end DivisionRing

section Field

variable {R : Type*} [Field R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]

variable {p : M →ₗ[R] N →ₗ[R] R}

variable {C C₁ C₂ F : PointedCone R M}

-- ## DUAL

-- FIX: fix `fg_inf_of_isCompl` first
-- Q: Is DivisionRing necessary?
/-- The lineality space of a full-dimensional cone is CoFG. -/
lemma cofg_lineal_of_span_top (hC : C.IsPolyhedral)
    (h : Submodule.span R (C : Set M) = ⊤) : CoFG C.lineal := by
  obtain ⟨_, hS⟩ := Submodule.exists_isCompl C.lineal
  have hh := congrArg (Submodule.span R ∘ SetLike.coe) <| inf_sup_lineal hS.codisjoint
  simp only [Function.comp_apply, h, ← coe_sup_submodule_span, Submodule.coe_restrictScalars,
    Submodule.span_union, span_coe_eq_restrictScalars] at hh
  refine FG.codisjoint_cofg (codisjoint_iff.mpr hh) (FG.span_fg <| hC.fg_inf_of_isCompl hS)

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

/-- A polyhedral cone with DualFG linearlity space is itself DualFG. -/
lemma dualfg_of_lineal_dualfg {C : PointedCone R N}
    (hC : C.IsPolyhedral) (hlin : C.lineal.DualFG p) : DualFG p C := by
  obtain ⟨_, hfg, hD⟩ := hC.exists_fg_eq_sup_lineal
  rw [hD]
  exact sup_fg_dualfg hfg hlin

/-- A polyhedral cone is DualFG if and only if its lineality space is DualFG. -/
lemma dualfg_iff_lineal_dualfg {C : PointedCone R N} {hC : C.IsPolyhedral} :
    C.DualFG p ↔ C.lineal.DualFG p := ⟨DualFG.lineal_dualfg, hC.dualfg_of_lineal_dualfg⟩

variable (p) [Fact (Surjective p)] in
/-- If `C` is a polyhedral cone and `S` is a subspace codisjoint to the linear span of `C`,
  then `C ⊔ S` is DualFG. This is the counterpart to `IsPolyhedral.dualfg_inf_of_disjoint_lineal`.
-/
lemma dualfg_sup_of_codisjoint_span {C : PointedCone R N} (hC : C.IsPolyhedral)
    {S : Submodule R N} (hS : Codisjoint (span R C) S) : DualFG p (C ⊔ S) := by
  refine dualfg_of_lineal_dualfg (hC.sup_submodule S) (CoFG.dualfg p ?_)
  refine cofg_lineal_of_span_top (hC.sup_submodule _) ?_
  simpa [← coe_sup_submodule_span, Submodule.span_union] using codisjoint_iff.mp hS

variable (p) [Fact (Surjective p)] in
/-- A polyhedral cone `C` can be written as the intersection of a DualFG cone with the
  linear span of `C`. -/
lemma exists_dualfg_inf_span {C : PointedCone R N} (hC : C.IsPolyhedral) :
    ∃ D : PointedCone R N, D.DualFG p ∧ D ⊓ (span R (C : Set N)) = C := by
  have ⟨S, hS⟩ := Submodule.exists_isCompl (Submodule.span R (C : Set N))
  exact ⟨C ⊔ S, hC.dualfg_sup_of_codisjoint_span p hS.codisjoint,
    sup_inf_submodule_span_of_disjoint hS.disjoint⟩

variable (p) in
/-- Duals generated from a finite set are polyhedral. -/
lemma of_dual_of_finset (s : Finset M) : (dual p s).IsPolyhedral := by
  obtain ⟨D, hfg, hD⟩ := exists_fg_sup_dual p s
  rw [← hD]
  exact .of_fg_sup_submodule hfg _

variable (p) in
/-- Duals of FG cones are polyhedral. -/
lemma of_dual_of_fg (hC : C.FG) : (dual p C).IsPolyhedral := by
  obtain ⟨D, hfg, hD⟩ := FG.exists_fg_sup_dual p hC
  rw [← hD]
  exact .of_fg_sup_submodule hfg _

/-- DualFG cones are polyhedral. -/
lemma of_dualfg {C : PointedCone R N} (hC : C.DualFG p) : C.IsPolyhedral := by
  obtain ⟨D, hfg, rfl⟩ := hC.exists_fg_dual
  exact .of_dual_of_fg p hfg

/-- The intersection of a polyhedral cone with an FG cone is FG. -/
lemma fg_of_inf_fg_submodule (hC : C.IsPolyhedral)
    {S : Submodule R M} (hS : S.FG) : FG (C ⊓ S) := by
  obtain ⟨D, hcofg, hD⟩ := hC.exists_dualfg_inf_span .id
  rw [← hD, inf_assoc, ← coe_inf]
  exact inf_dualfg_fg hcofg <| FG.coe_fg <| FG.of_le hS inf_le_right

lemma of_dualfg_inf_submodule (hC : C.DualFG .id) (S : Submodule R M) :
    (C ⊓ S).IsPolyhedral := by
  have h := (of_dualfg (DualFG.restrict_id hC S)).map S.subtype
  change ((C.restrict S).embed).IsPolyhedral at h
  simpa [inf_comm] using h

lemma of_submodule_inf_dualfg (S : Submodule R M) (hC : C.DualFG .id) :
    ((S : PointedCone R M) ⊓ C).IsPolyhedral := by
  rw [inf_comm]
  exact of_dualfg_inf_submodule hC S

/-- The intersection of two polyhedral cones is polyhedral. -/
lemma inf (h₁ : C₁.IsPolyhedral) (h₂ : C₂.IsPolyhedral) : (C₁ ⊓ C₂).IsPolyhedral := by
  obtain ⟨D₁, hD₁, hD₁eq⟩ := h₁.exists_dualfg_inf_span .id
  obtain ⟨D₂, hD₂, hD₂eq⟩ := h₂.exists_dualfg_inf_span .id
  rw [← hD₁eq, ← hD₂eq]
  let S : Submodule R M := span R C₁ ⊓ span R C₂
  rw [show (D₁ ⊓ span R (C₁ : Set M)) ⊓ (D₂ ⊓ span R (C₂ : Set M)) = (D₁ ⊓ D₂) ⊓ S by
    ext x; simp [S, and_assoc, and_left_comm]]
  exact of_dualfg_inf_submodule (hD₁.inf hD₂) S

protected lemma comap (f : N →ₗ[R] M) (hC : C.IsPolyhedral) :
    (C.comap f).IsPolyhedral := by
  obtain ⟨D, hD, hDC⟩ := hC.exists_dualfg_inf_span .id
  rw [← hDC]
  let S : Submodule R N := (span R (C : Set M)).comap f
  rw [show (D ⊓ span R (C : Set M)).comap f = D.comap f ⊓ S by
    ext x; simp [S]]
  exact of_dualfg_inf_submodule (DualFG.comap hD f).id S

/-- If `C` is a polyhedral cone and `S` is a submodule disjoint to its lineality, then
  `C ⊓ S` is FG. This is a strengthened version of `IsPolyhedral.fg_inf_of_isCompl`. -/
lemma fg_inf_of_disjoint_lineal (hC : C.IsPolyhedral)
    {S : Submodule R M} (hS : Disjoint C.lineal S) : FG (C ⊓ S) := by
  refine fg_of_fg_lineal (hC.inf <| .of_submodule S) ?_
  simp only [lineal_inf, submodule_lineal, disjoint_iff.mp hS, fg_bot]
  -- TODO: fg_bot should be a simp lemma

variable (p) in
/-- The dual of a polyhedral cone is polyhedral. -/
lemma dual (hC : C.IsPolyhedral) : (dual p C).IsPolyhedral := by
  obtain ⟨D, hDfg, hD⟩ := hC.exists_fg_eq_sup_lineal
  rw [hD, dual_sup_dual_inf_dual, Submodule.coe_restrictScalars, dual_eq_submodule_dual]
  exact IsPolyhedral.inf (.of_dual_of_fg p hDfg) (.of_submodule _)

variable (p) in
-- I believe proving this requires a lot of other work to be done before (above).
-- Essentially, in a lot of lemmas we need to replace `[Fact (Surjective p)]` by
-- an assumption about lineal, most likely, that lineal is dual closed.
-- However, the assumption `[Fact (Surjective p)]` is preferable because it can be
-- inferred automatically in the finite dimensional case.
lemma dualClosed_iff_lineal (hC : C.IsPolyhedral) :
    C.DualClosed p ↔ C.lineal.DualClosed p := by
  constructor <;> intro h
  · exact h.lineal
  -- here we need that a dual closed cone + an FG cone stays dual closed. This theory does not
  -- yet exist.
  sorry

variable (p) [Fact (Surjective p.flip)] in
lemma dualClosed (hC : C.IsPolyhedral) : C.DualClosed p := by
  obtain ⟨D, hdual, hD⟩ := hC.exists_dualfg_inf_span p.flip
  rw [← hD]
  exact DualClosed.inf (DualFG.dualClosed hdual)
    (dualClosed_coe <| Submodule.dualClosed p _)

-- This doubling of theorems should be unnecessary if we define `[Fact (Surjective p)]` correctly.
variable (p) [Fact (Surjective p)] in
lemma dualClosed_flip {C : PointedCone R N} (hC : C.IsPolyhedral) :
    C.DualClosed p.flip := by
  rw [← flip_flip p]; exact hC.dualClosed p.flip

variable (p) [Fact (Surjective p.flip)] in
lemma dual_flip_dual (hC : C.IsPolyhedral) :
  PointedCone.dual p.flip (PointedCone.dual p C) = C := hC.dualClosed p

-- This doubling of theorems should be unnecessary if we define `[Fact (Surjective p)]` correctly.
variable (p) [Fact (Surjective p)] in
lemma dual_dual_flip {C : PointedCone R N} (hC : C.IsPolyhedral) :
    PointedCone.dual p (PointedCone.dual p.flip C) = C := hC.dualClosed_flip p

/- NOTE: some restriction like `IsPerfPair` is necessary. Consider two subspaces S, T that are not
  dual closed and with S ⊓ T = ⊥. The left side is ⊤. But the right side is ⊥ ⊔ ⊥ = ⊥.
  Alterantively, we can assume that C₁ and C₂ are dual closed. But this version must stay
  because type inference makes its assumptions automatic in finite dimensions. Maybe a weaker
  assumoption suffices though (it seems to be the case for FG and DualFG). -/
-- variable (p) [p.IsPerfPair] in
variable (p) [Fact (Surjective p)] in
variable [Fact (Surjective p.flip)] in
lemma dual_inf_dual_sup_dual (hC₁ : C₁.IsPolyhedral) (hC₂ : C₂.IsPolyhedral) :
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
--   exact DualFG.dual_fg (sup_fg_cofg hfg <| CoFG.cofg p.flip hlin)

variable (p) [Fact (Surjective p)] in
@[deprecated dualfg_of_lineal_cofg (since := "...")]
private lemma dualfg_of_lineal_cofg {C : PointedCone R N}
    (hC : C.IsPolyhedral) (hlin : CoFG C.lineal) : DualFG p C := by
  obtain ⟨_, hfg, hD⟩ := hC.exists_fg_eq_sup_lineal
  rw [hD]
  exact sup_fg_dualfg hfg (CoFG.dualfg p hlin)

variable (p) [Fact (Surjective p.flip)] in -- [Fact p.IsFaithfulPair]
lemma exists_isPolyhedral_dual (hC : C.IsPolyhedral) :
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
  have h := hC'.dualfg_of_lineal_cofg p.flip (hC'.cofg_lineal_of_span_top hh)
  --have h' := DualFG.dual_fg h -- we dont' need FG, we need polyhedral
  have h' : (PointedCone.dual p C').IsPolyhedral := sorry -- FG.isPolyhedral (DualFG.dual_fg h)
  have h'' := DualFG.dualClosed h
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

end IsPolyhedral

end PointedCone
