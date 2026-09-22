/-
Copyright (c) 2025 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/
module

public import Polyhedral.Mathlib.Algebra.Module.Submodule.Basic

import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Noetherian.Basic

/-! This file contains useful results about FG submodules. -/

public section

open Module
open Function

namespace Submodule

variable {R M M₁ M₂ : Type*}

section Semiring

variable [Semiring R]
variable [AddCommMonoid M] [Module R M]
variable [AddCommMonoid M₁] [Module R M₁]
variable [AddCommMonoid M₂] [Module R M₂]

alias sup_fg := Submodule.FG.sup

-- This seems to be the more appropriate version of `Submodule.fg_of_linearEquiv` which
-- is probably better called `Module.fg_of_linearEquiv` or so.
lemma FG.linearEquiv {S : Submodule R M₁} {T : Submodule R M₂} (e : S ≃ₗ[R] T) (hS : S.FG) :
    T.FG := by -- T.fg_top.mp <| fg_of_linearEquiv e.symm (S.fg_top.mpr hS)
  rw [← Submodule.fg_top] at *
  exact fg_of_linearEquiv e.symm hS

-- ## RESTRICT / EMBED

lemma embed_fg_of_fg {S : Submodule R M} {T : Submodule R S} (hC : T.FG) :
    (embed T).FG := Submodule.FG.map _ hC

lemma fg_of_embed_fg {S : Submodule R M} {T : Submodule R S} (hT : (embed T).FG) : T.FG
    := fg_of_fg_map_injective _ (injective_subtype (S : Submodule R M)) hT

@[simp] lemma embed_fg_iff_fg {S : Submodule R M} {T : Submodule R S} : (embed T).FG ↔ T.FG
  := ⟨fg_of_embed_fg, embed_fg_of_fg⟩

lemma restrict_fg_of_fg_le {S T : Submodule R M} (hST : T ≤ S) (hT : T.FG) :
    (restrict S T).FG := by
  rw [← (inf_eq_left.mpr hST), inf_comm, ← embed_restrict] at hT
  exact fg_of_embed_fg hT

lemma fg_of_restrict_le {S T : Submodule R M} (hST : T ≤ S) (hC : (restrict S T).FG) :
    T.FG := by
  rw [← (inf_eq_left.mpr hST), inf_comm, ← embed_restrict]
  exact embed_fg_of_fg hC

@[simp] lemma fg_iff_restrict_le {S T : Submodule R M} (hST : T ≤ S) :
    (restrict S T).FG ↔ T.FG := ⟨fg_of_restrict_le hST, restrict_fg_of_fg_le hST⟩

lemma restrict_fg_iff_inf_fg {S T : Submodule R M} :
    (restrict S T).FG ↔ (S ⊓ T : Submodule R M).FG := by
  rw [← embed_restrict, embed_fg_iff_fg]

/-- Given a map `f`, every FG submodule `S` in the codomain is the image of an FG submodule `T`
from the domain. -/
lemma FG.exists_fg_eq_map_of_surjective {f : M₁ →ₗ[R] M₂} (hf : Surjective f)
    {S : Submodule R M₂} (hS : S.FG) : ∃ T : Submodule R M₁, T.FG ∧ S = T.map f := by classical
  obtain ⟨s, rfl⟩ := hS
  use span R (Finset.image (surjInv hf) s)
  exact ⟨⟨_, rfl⟩, by simp [Submodule.map_span, Set.image_image, surjInv_eq]⟩

end Semiring

section IsNoetherianRing

variable [Ring R] [IsNoetherianRing R]
variable [AddCommGroup M] [Module R M]

/-- The restriction of an FG submodule to an arbitrary submodule is FG. -/
lemma restrict_fg (S : Submodule R M) {T : Submodule R M} (hT : T.FG) : (restrict S T).FG := by
  rw [restrict_fg_iff_inf_fg]; exact FG.of_le hT inf_le_right

end IsNoetherianRing

section Field

variable [Field R]
variable [AddCommGroup M₁] [Module R M₁]
variable [AddCommGroup M₂] [Module R M₂]

/-- The preimage of an FG submodule can be written as the sum of an FG submodule woth the
kernel of the map. -/
lemma FG.exists_fg_comap_eq_sup_ker {f : M₁ →ₗ[R] M₂} {S : Submodule R M₂} (hS : S.FG) :
    ∃ T : Submodule R M₁, T.FG ∧ S.comap f = T ⊔ f.ker := by
  have hcomap : (S.comap (LinearMap.range f).subtype).FG := by
    apply fg_of_fg_map_injective _ (injective_subtype _)
    simpa [map_comap_eq, inf_comm] using FG.of_le hS inf_le_left
  obtain ⟨T, hT, hmap⟩ := hcomap.exists_fg_eq_map_of_surjective f.surjective_rangeRestrict
  refine ⟨T, hT, ?_⟩
  calc S.comap f = (S.comap (LinearMap.range f).subtype).comap f.rangeRestrict := by rfl
    _ = (T.map f.rangeRestrict).comap f.rangeRestrict   := by rw [← hmap]
    _ = T ⊔ LinearMap.ker f.rangeRestrict               := by rw [comap_map_eq]
    _ = T ⊔ LinearMap.ker f                             := by congr 1; ext; simp

end Field

end Submodule
