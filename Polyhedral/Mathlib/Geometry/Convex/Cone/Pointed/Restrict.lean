/-
Copyright (c) 2025 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/

import Polyhedral.Mathlib.Algebra.Module.Submodule.Restrict
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Basic

/-! This file defines restrictions of convex cones to submodules and proves basic lemmas. -/

namespace PointedCone

section Semiring

open Module Function
open Submodule (span)

variable {R M : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R] [AddCommMonoid M]
  [Module R M] {S : Set M}

/- TODO: generalize these restrict/embed lemmas to general case where we restrict a
  restrictScalar subspace to a normal subspace. -/

-- TODO: generalize to restrict using restrictScalar, so we can need to write only one instead
--  of two for submodules and pointed cones.

-- Q: Do we maybe want notation for this? For example: `S ⊓ᵣ C`?
/-- The intersection `C ⊓ S` considered as a cone in `S`. -/
abbrev restrict (S : Submodule R M) (C : PointedCone R M) : PointedCone R S
  := C.submoduleOf S -- C.comap S.subtype

-- alias pointedConeOf := restrict

-- @[simp]
lemma coe_restrict (S T : Submodule R M) :
    restrict S T = Submodule.restrict S T := by
  unfold restrict Submodule.restrict Submodule.submoduleOf
  sorry

lemma restrict_eq_comap_subtype (S : Submodule R M) (T : PointedCone R M) :
    restrict S T = comap S.subtype T := rfl

-- @[simp] lemma restrict_top (S : Submodule R M) : restrict S ⊤ = ⊤ := Submodule.restrict_top _
-- @[simp] lemma restrict_bot (S : Submodule R M) : restrict S ⊥ = ⊥ := Submodule.restrict_bot _

-- @[simp] lemma restrict_self (S : Submodule R M) : restrict S S = ⊤ := Submodule.restrict_self _

-- lemma mem_restrict {S : Submodule R M} {T : PointedCone R M} {x : S} (h : x ∈ restrict S T) :
--     (x : M) ∈ T := h

lemma mem_restrict_iff {S : Submodule R M} {T : PointedCone R M} {x : S} :
    x ∈ restrict S T ↔ (x : M) ∈ T := ⟨id, id⟩

/-- A cone `C` in a submodule `S` of `M` intepreted as a cone in `M`. -/
@[coe] abbrev embed {S : Submodule R M} (C : PointedCone R S) : PointedCone R M := C.map S.subtype

lemma embed_injective {S : Submodule R M} : Injective (embed : PointedCone R S → PointedCone R M)
  := Submodule.map_injective_of_injective S.subtype_injective

@[simp] lemma embed_inj {S : Submodule R M} {T₁ T₂ : PointedCone R S} :
    embed T₁ = embed T₂ ↔ T₁ = T₂ := Injective.eq_iff embed_injective

-- TODO: use `Monotone`
lemma embed_mono {S : Submodule R M} {C₁ C₂ : PointedCone R S} (hT : C₁ ≤ C₂) :
    embed C₁ ≤ embed C₂ := Submodule.map_mono hT

lemma embed_mono_rev {S : Submodule R M} {C₁ C₂ : PointedCone R S} (hC : embed C₁ ≤ embed C₂) :
    C₁ ≤ C₂ := (by simpa using @hC ·)

@[simp] lemma embed_mono_iff {S : Submodule R M} {C₁ C₂ : PointedCone R S} :
    embed C₁ ≤ embed C₂ ↔ C₁ ≤ C₂ where
  mp := embed_mono_rev
  mpr := embed_mono

-- this should have higher priority than `map_top`
@[simp] lemma embed_top {S : Submodule R M} : embed (⊤ : PointedCone R S) = S := by sorry
@[simp] lemma embed_bot {S : Submodule R M} : embed (⊥ : PointedCone R S) = ⊥ := by sorry

@[simp] lemma embed_le {S : Submodule R M} {C : PointedCone R S} : embed C ≤ S := by sorry

@[simp] lemma embed_restrict (S : Submodule R M) (C : PointedCone R M) :
    (C.restrict S).embed = (S ⊓ C : PointedCone R M) := by
  -- unfold embed restrict map comap
  -- -- rw [← Submodule.restrictScalars_]
  -- --rw [Submodule.restrictScalars_s]
  -- --rw [comap_restrictScalar]
  -- rw [← Submodule.restrictScalars_map]
  -- exact Submodule.map_comap_subtype
  sorry -- map_comap_subtype _ _

@[simp]
lemma restrict_embed (S : Submodule R M) (C : PointedCone R S) : restrict S (embed C) = C
  := by sorry -- simp [restrict, embed, pointedConeOf, submoduleOf, map, comap_map_eq]

lemma embed_fg_of_fg (S : Submodule R M) {C : PointedCone R S} (hC : C.FG) :
    C.embed.FG := Submodule.FG.map _ hC

lemma fg_of_embed_fg {S : Submodule R M} {C : PointedCone R S} (hC : C.embed.FG) : C.FG
    := Submodule.fg_of_fg_map_injective _ (Submodule.injective_subtype (S : PointedCone R M)) hC

@[simp] lemma embed_fg_iff_fg {S : Submodule R M} {C : PointedCone R S} : C.embed.FG ↔ C.FG
  := ⟨fg_of_embed_fg, embed_fg_of_fg S⟩

lemma restrict_fg_of_fg_le {S : Submodule R M} {C : PointedCone R M} (hSC : C ≤ S) (hC : C.FG) :
    (C.restrict S).FG := by
  rw [← (inf_eq_left.mpr hSC), inf_comm, ← embed_restrict] at hC
  exact fg_of_embed_fg hC

lemma fg_of_restrict_le {S : Submodule R M} {C : PointedCone R M}
    (hSC : C ≤ S) (hC : (C.restrict S).FG) : C.FG := by
  rw [← (inf_eq_left.mpr hSC), inf_comm, ← embed_restrict]
  exact embed_fg_of_fg S hC

@[simp] lemma fg_iff_restrict_le {S : Submodule R M} {C : PointedCone R M} (hSC : C ≤ S) :
    (C.restrict S).FG ↔ C.FG := ⟨fg_of_restrict_le hSC, restrict_fg_of_fg_le hSC⟩

lemma restrict_fg_iff_inf_fg (S : Submodule R M) (C : PointedCone R M) :
    (C.restrict S).FG ↔ (S ⊓ C : PointedCone R M).FG := by
  rw [← embed_restrict, embed_fg_iff_fg]

lemma restrict_mono (S : Submodule R M) {C D : PointedCone R M} (hCD : C ≤ D) :
    C.restrict S ≤ D.restrict S := fun _ => (hCD ·)

lemma restrict_inf (S : Submodule R M) {C D : PointedCone R M} :
    (C ⊓ D).restrict S = C.restrict S ⊓ D.restrict S
  := by
  ext x
  rw [mem_restrict_iff]
  constructor <;> exact fun hx ↦ ⟨hx.1, hx.2⟩

@[simp]
lemma restrict_inf_submodule (S : Submodule R M) (C : PointedCone R M) :
    (C ⊓ S).restrict S = C.restrict S := by
  ext x
  rw [mem_restrict_iff, mem_restrict_iff]
  exact and_iff_left x.property

@[simp]
lemma restrict_submodule_inf (S : Submodule R M) (C : PointedCone R M) :
    (S ⊓ C : PointedCone R M).restrict S = C.restrict S := by
      simp only [Submodule.restrict_inf_self]
      exact embed_inj.mp rfl

end Semiring

end PointedCone
