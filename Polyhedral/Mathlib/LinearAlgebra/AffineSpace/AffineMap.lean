/-
Copyright (c) 2026 Martin Winter, Olivia Röhrig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter, Olivia Röhrig
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic

import Mathlib.LinearAlgebra.AffineSpace.AffineMap

/-! The content of this file should go into `AffineSpace/AffineMap.lean`. -/

@[expose] public section

open Affine Module AffineSubspace

section

variable {k V V₁ V₂ P P₁ P₂ : Type*}

namespace AffineMap

variable [Ring k]
variable [AddCommGroup V] [Module k V]
variable [AddCommGroup V₁] [Module k V₁]
variable [AddCommGroup V₂] [Module k V₂]
variable [AffineSpace V P] [AffineSpace V₁ P₁] [AffineSpace V₂ P₂]

/-- The range of an affine map is an affine subspace. -/
def range (f : P₁ →ᵃ[k] P₂) : AffineSubspace k P₂ where
  carrier := Set.range f
  smul_vsub_vadd_mem' := by
    simp only [Set.mem_range, forall_exists_index]
    intro c _ _ _ x₁ h₁ x₂ h₂ x₃ h₃
    exact ⟨c • (x₁ -ᵥ x₂) +ᵥ x₃, by simp [map_vadd, ← h₁, ← h₂, ← h₃]⟩

instance instNonemptyRange (f : P₁ →ᵃ[k] P₂) : Nonempty (range f) :=
  Set.instNonemptyRange f

@[simp]
theorem mem_range (f : P₁ →ᵃ[k] P₂) (x : P₂) : x ∈ f.range ↔ ∃ (y : P₁), f y = x :=
  Iff.rfl

@[simp]
theorem coe_range (f : P₁ →ᵃ[k] P₂) : f.range = Set.range f := rfl

theorem range_eq_map (f : P₁ →ᵃ[k] P₂) : range f = map f ⊤ := by
  ext
  simp

theorem mem_range_self (f : P₁ →ᵃ[k] P₂) (x : P₁) : f x ∈ range f :=
  ⟨x, rfl⟩

@[simp]
theorem range_id : range (AffineMap.id k P₁) = ⊤ :=
  SetLike.coe_injective Set.range_id

theorem range_comp (f : P₁ →ᵃ[k] P₂) (g : P₂ →ᵃ[k] P) : range (g.comp f) = map g (range f) :=
  SetLike.coe_injective (Set.range_comp g f)

theorem range_comp_le_range (f : P₁ →ᵃ[k] P₂) (g : P₂ →ᵃ[k] P) : range (g.comp f) ≤ range g :=
  SetLike.coe_mono (Set.range_comp_subset_range f g)

theorem range_eq_top {f : P₁ →ᵃ[k] P₂} : range f = ⊤ ↔ Function.Surjective f := by
  rw [SetLike.ext'_iff, coe_range, top_coe, Set.range_eq_univ]

theorem range_eq_top_of_surjective (f : P₁ →ᵃ[k] P₂) (hf : Function.Surjective f) :
    range f = ⊤ := range_eq_top.mpr hf

theorem range_le_iff_comap {f : P₁ →ᵃ[k] P₂} {p : AffineSubspace k P₂} :
    range f ≤ p ↔ comap f p = ⊤ := by rw [range_eq_map, map_le_iff_le_comap, eq_top_iff]

theorem map_le_range {f : P₁ →ᵃ[k] P₂} {p : AffineSubspace k P₁} : map f p ≤ range f :=
  SetLike.coe_mono (Set.image_subset_range f p)

theorem comap_le_comap_iff {f : P₁ →ᵃ[k] P₂} (hf : range f = ⊤) {p p'} :
    comap f p ≤ comap f p' ↔ p ≤ p' :=
  ⟨fun H ↦ by rwa [SetLike.le_def, (range_eq_top.mp hf).forall], comap_mono⟩

theorem comap_injective {f : P₁ →ᵃ[k] P₂} (hf : range f = ⊤) : Function.Injective (comap f) :=
  fun _ _ h ↦ le_antisymm ((comap_le_comap_iff hf).mp (le_of_eq h))
    ((comap_le_comap_iff hf).mp (ge_of_eq h))

@[simp]
theorem map_top (f : P₁ →ᵃ[k] P₂) : map f ⊤ = range f :=
  (range_eq_map f).symm

@[simp]
theorem affineSpan_range_eq_range (f : P₁ →ᵃ[k] P₂) : affineSpan k (Set.range f) = f.range := by
  simp [← Set.image_univ, ← AffineSubspace.map_span]

lemma range_direction (f : P₁ →ᵃ[k] P₂) : f.range.direction = f.linear.range := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro _ ⟨p₁, h₁, p₂, h₂, h⟩
    simp only [SetLike.mem_coe, mem_range] at h₁ h₂
    obtain ⟨p₁, rfl⟩ := h₁
    obtain ⟨p₂, rfl⟩ := h₂
    exact ⟨p₁ -ᵥ p₂, h ▸ f.linearMap_vsub _ _⟩
  · apply Submodule.span_le.mp
    intro v hv
    rw [Submodule.span_coe_eq_restrictScalars] at hv
    obtain ⟨w, rfl⟩ := hv
    apply Submodule.subset_span
    simp only [Set.mem_vsub, SetLike.mem_coe, mem_range, exists_exists_eq_and]
    exact ⟨(w +ᵥ Classical.arbitrary P₁), (Classical.arbitrary P₁), by simp⟩

lemma range_eq_copmap_top (f : P₁ →ᵃ[k] P₂) : f.range = .map f ⊤ := by ext; simp

def rangeRestrict (f : P₁ →ᵃ[k] P₂) : P₁ →ᵃ[k] f.range where
  toFun p := ⟨f p, p, rfl⟩
  linear := (LinearEquiv.ofEq _ _ f.range_direction.symm).toLinearMap ∘ₗ f.linear.rangeRestrict
  map_vadd' _ _ := by ext; simp [map_vadd]

lemma rangeRestrict_injective_iff (f : P₁ →ᵃ[k] P₂) :
    (rangeRestrict f).toFun.Injective ↔ f.toFun.Injective := by
  simp only [Function.Injective, rangeRestrict, toFun_eq_coe, coe_mk]
  constructor
  · intro h p q hpq
    exact h <| Subtype.ext hpq
  · intro h p q hpq
    exact h <| congrArg Subtype.val hpq

end AffineMap

end
