/-
Copyright (c) 2025 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.Geometry.Convex.Cone.Pointed

import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Lineal
import Polyhedral.Hyperplane

/-!
# Halfspace

...
-/

open Function Module

variable {R R M N M' N' : Type*}

namespace PointedCone

section Halfspace

-- ### HalfspaceOrTop

variable {R : Type*} [CommRing R] [LinearOrder R] [IsOrderedRing R]
  {M : Type*} [AddCommGroup M] [Module R M] -- [AddCommGroup (Dual R M)]
  {M' : Type*} [AddCommGroup M'] [Module R M']

-- Maybe define this on `Set M` instead?
def IsHalfspaceOrTop (P : PointedCone R M)
    := ∃ x : (Dual R M), dual .id {x} = P

lemma IsHalfspaceOrTop.top : IsHalfspaceOrTop (⊤ : PointedCone R M)
    := by use 0; ext x; simp

lemma IsHalfspaceOrTop.of_map {f : M →ₗ[R] M'} (hf : Surjective f)
    {P : PointedCone R M} (hP : P.IsHalfspaceOrTop) : (map f P).IsHalfspaceOrTop := by
  unfold IsHalfspaceOrTop
  obtain ⟨x, hx⟩ := hP
  -- use f.dualMap x
  sorry

variable (R M) in
structure HalfspaceOrTop extends PointedCone R M where
  isHalfspaceOrTop : IsHalfspaceOrTop toSubmodule

namespace HalfspaceOrTop

-- alias toPointedCone := toSubmodule

instance : Coe (HalfspaceOrTop R M) (PointedCone R M) where
  coe := toSubmodule

abbrev of_isHalfspaceOrTop {P : PointedCone R M} (hS : P.IsHalfspaceOrTop) :
    HalfspaceOrTop R M := ⟨P, hS⟩

abbrev of_point (x : Dual R M) : HalfspaceOrTop R M := ⟨dual .id {x}, by use x⟩

-- Q: should these be simp lemmas?
lemma toPointedCone_injective :
    Injective (toSubmodule : HalfspaceOrTop R M → PointedCone R M) :=
  fun ⟨_, _⟩ _ ↦ by congr!

instance : SetLike (HalfspaceOrTop R M) M where
  coe C := C.toSubmodule
  coe_injective' := SetLike.coe_injective.comp toPointedCone_injective

@[simp] lemma coe_toSubmodule (C : HalfspaceOrTop R M) : (C.toSubmodule : Set M) = C := rfl

abbrev of_dual_pt (x : Dual R M) : HalfspaceOrTop R M := ⟨dual .id {x}, by use x⟩

-- @[simp] lemma mem_dual (H : HalfspaceOrTop R M) (y : M): y ∈ H ↔ ∀ ⦃x⦄, x ∈ s → 0 ≤ p x y := .rfl

-- def top : HalfspaceOrTop R M := of_isHalfspaceOrTop IsHalfspaceOrTop.top

instance : Top (HalfspaceOrTop R M) := ⟨_, IsHalfspaceOrTop.top⟩

@[simp]
lemma top_coe : (⊤ : HalfspaceOrTop R M) = (⊤ : PointedCone R M) := by rfl

def map {f : M →ₗ[R] M'} (P : HalfspaceOrTop R M) (hf : Surjective f) : HalfspaceOrTop R M'
  := of_isHalfspaceOrTop <| IsHalfspaceOrTop.of_map hf P.2

-- TODO: comap

-- omit [PartialOrder R] [IsOrderedRing R] in
-- lemma LinearMap.neg_surj {f : M →ₗ[R] M} (hf : Surjective f) : Surjective (-f) := by
--   intro x
--   obtain ⟨y, rfl⟩ := hf x
--   use -y
--   simp

abbrev opposite (P : HalfspaceOrTop R M) := map (f := -.id) P (⟨-·, by simp⟩)
    -- := map (f := -.id) P (LinearMap.neg_surj surjective_id)

instance : Neg (HalfspaceOrTop R M) := ⟨opposite⟩

-- private lemma is_hyportop_of_inf_neg (P : HalfspaceOrTop R M) :
--     ∃ H : Submodule.HyperplaneOrTop R M, (P ⊓ -P : PointedCone R M) = H := by
--   obtain ⟨x, hx⟩ := P.isHalfspaceOrTop
--   use .of_dual_pt x
--   ext y; simp [← hx, antisymm_iff, Eq.comm]

-- def boundary (P : HalfspaceOrTop R M) : Submodule.HyperplaneOrTop R M where
--   carrier := (P ⊓ -P : PointedCone R M)
--   add_mem' a b := by sorry -- aesop
--   zero_mem' := by sorry -- simp
--   smul_mem' := by simp; sorry
--   isHyperplaneOrTop := by simp; sorry

-- def boundary' (P : HalfspaceOrTop R M) : Submodule.HyperplaneOrTop R M where
--   carrier := (P ⊓ -P : PointedCone R M)
--   add_mem' := by obtain ⟨H, hH⟩ := P.is_hyportop_of_inf_neg; rw [hH]; exact H.add_mem'
--   zero_mem' := by obtain ⟨H, hH⟩ := P.is_hyportop_of_inf_neg; rw [hH]; exact H.zero_mem'
--   smul_mem' := by obtain ⟨H, hH⟩ := P.is_hyportop_of_inf_neg; rw [hH]; exact H.smul_mem'
--   isHyperplaneOrTop := by sorry
--     -- unfold Submodule.IsHyperplaneOrTop
--     -- obtain ⟨H, hH⟩ := P.is_hyportop_of_inf_neg; rw [hH]; exact H.isHyperplaneOrTop


-- private lemma is_submodule_of_inter_neg'' (P : HalfspaceOrTop R M) :
--     ∃ S : Submodule R M, (P ∩ -P : Set M) = S := by
--   obtain ⟨x, hx⟩ := P.isHalfspaceOrTop
--   rw [← SetLike.coe_set_eq, coe_toSubmodule] at hx
--   use Submodule.dual .id {x}
--   ext y; simp [← hx, antisymm_iff]

-- private lemma is_submodule_of_inter_neg (P : HalfspaceOrTop R M) :
--     ∃ S : Submodule R M, (P ⊓ -P : PointedCone R M) = S := by
--   obtain ⟨x, hx⟩ := P.isHalfspaceOrTop
--   rw [← hx]
--   use Submodule.dual .id {x}
--   ext y; simp [antisymm_iff]

-- private abbrev boundary_Submodule'' (P : HalfspaceOrTop R M) : Submodule R M :=
--   .copy' (P ∩ -P) P.is_submodule_of_inter_neg''

-- private abbrev boundary_Submodule (P : HalfspaceOrTop R M) : Submodule R M :=
--   .copy' (P ⊓ -P : PointedCone R M) <| (by
--     obtain ⟨S, hS⟩ := P.is_submodule_of_inter_neg
--     use S
--     sorry
--     -- rw [Submodule.coe_inf]
--     -- rw [← SetLike.coe_eq_coe] at hS
--     -- exact SetLike.coe_eq_coe.mpr hS
--   )

-- -- private abbrev boundary_Submodule (P : HalfspaceOrTop R M) : Submodule R M where
-- --   carrier := P ∩ -P -- (P ⊓ -P : PointedCone R M)
-- --   add_mem' := by obtain ⟨S, hS⟩ := P.is_submodule_of_inter_neg; rw [hS]; exact S.add_mem'
-- --   zero_mem' := by simp; exact Submodule.zero_mem P.toSubmodule
-- --   smul_mem' := by obtain ⟨S, hS⟩ := P.is_submodule_of_inter_neg; rw [hS]; exact S.smul_mem'

-- def boundary'' (P : HalfspaceOrTop R M) : Submodule.HyperplaneOrTop R M where
--   carrier := P ∩ -P -- (P ⊓ -P : PointedCone R M)
--   add_mem' := by obtain ⟨S, hS⟩ := P.is_submodule_of_inter_neg''; rw [hS]; exact S.add_mem'
--   zero_mem' := by simp; exact Submodule.zero_mem P.toSubmodule
--   smul_mem' := by obtain ⟨S, hS⟩ := P.is_submodule_of_inter_neg''; rw [hS]; exact S.smul_mem'
--   isHyperplaneOrTop := by
--     obtain ⟨x, hx⟩ := P.isHalfspaceOrTop
--     use x
--     ext y
--     simp
--     repeat rw [← SetLike.mem_coe]
--     rw [← SetLike.coe_set_eq, coe_toSubmodule] at hx
--     simp [← hx, antisymm_iff]

-- def boundary''' (P : HalfspaceOrTop R M) : Submodule.HyperplaneOrTop R M
--     := .of_isHyperplaneOrTop (S := P.boundary_Submodule'') (by
--   obtain ⟨x, hx⟩ := P.isHalfspaceOrTop
--   use x; ext y
--   rw [← SetLike.coe_set_eq, coe_toSubmodule] at hx
--   rw [← SetLike.mem_coe]
--   simp [← hx, antisymm_iff] )

-- TODO: move out of namespace `HyperplaneOrTop`.
lemma lineal_is_hyperplaneOrTop (P : HalfspaceOrTop R M) :
    (PointedCone.lineal (P : PointedCone R M)).IsHyperplaneOrTop := by
  obtain ⟨S, x, rfl⟩ := P
  use x; ext y
  simp [lineal_mem, antisymm_iff]

/-- The boundary of a hyperplane `H` is equivalently given by `H ⊓ -H` or `H.lineal`. -/
def boundary (P : HalfspaceOrTop R M) : Submodule.HyperplaneOrTop R M
    := ⟨_, P.lineal_is_hyperplaneOrTop⟩

@[simp]
lemma boundary_eq_lineal (P : HalfspaceOrTop R M) :
    (P.boundary : Submodule R M) = PointedCone.lineal P := by rfl

@[simp]
lemma boundary_top : (⊤ : HalfspaceOrTop R M).boundary = ⊤ := by
  apply Submodule.HyperplaneOrTop.toSubmodule_injective
  simp -- rw [boundary_eq_lineal, top_coe, lineal_top, Submodule.HyperplaneOrTop.top_coe]

end HalfspaceOrTop

-- ### Line

-- ## TODO: Fix Definition!!
def IsHalfspace (P : PointedCone R M)
    := ∃ x : (Dual R M), x ≠ 0 ∧ dual .id {x} = P

variable (R M) in
structure Halfspace extends PointedCone R M where
  isHalfspace : IsHalfspace toSubmodule

namespace Halfspace

instance : Coe (Halfspace R M) (PointedCone R M) where
  coe := toSubmodule

def of_isHalfspace {P : PointedCone R M} (hS : P.IsHalfspace) : Halfspace R M := ⟨P, hS⟩

-- Q: should these be simp lemmas?
lemma toSubmodule_injective :
    Injective (toSubmodule : Halfspace R M → PointedCone R M) :=
  fun ⟨_, _⟩ _ ↦ by congr!

instance : SetLike (Halfspace R M) M where
  coe C := C.toSubmodule
  coe_injective' := SetLike.coe_injective.comp toSubmodule_injective

@[simp] lemma coe_toSubmodule (C : Halfspace R M) : (C.toSubmodule : Set M) = C := rfl

end Halfspace

end Halfspace

end PointedCone
