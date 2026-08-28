/-
Copyright (c) 2026 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/

import Mathlib.Geometry.Convex.ConvexSpace.Module

import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Basic
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.LinearMap
import Polyhedral.Mathlib.GroupTheory.GroupAction.SubMulActionWithZero.Closure

/-! This file contains results involving both `PointedCone` and `SubMulAction₀`. -/

variable {R M : Type*}

namespace PointedCone

open Function Module SubMulAction₀

section Semiring

variable [Semiring R] [PartialOrder R] [IsOrderedRing R]
variable [AddCommMonoid M] [Module R M]

-- NOTE: this notation seems to be not used by the pretty printer

/- Note that the character `∙` U+2219 used below is different from the scalar multiplication
character `•` U+2022. -/
/-- Notation for the `SubMulAction₀` generated from a set `s` w.r.t. positive scalars,
short for `SubMulAction₀.closure R≥0 s`. -/
scoped notation:70 (priority := high) R:70 " ∙₊ " s:70 => { c : R // 0 ≤ c } ∙ s

local notation "R≥0" => {c : R // 0 ≤ c}

section SubMulAction₀

/-- Reinterpret a `PointedCone` as a `SubMulAction₀`. -/
@[coe] protected abbrev toSubMulAction₀ (p : PointedCone R M) :
    SubMulAction₀ R≥0 M := .ofClass (R := R≥0) p

instance instSubMulAction₀ : Coe (PointedCone R M) (SubMulAction₀ R≥0 M) :=
  ⟨PointedCone.toSubMulAction₀⟩

@[simp]
theorem coe_toSubMulAction₀ (p : PointedCone R M) :
    (p.toSubMulAction₀ : Set M) = p :=
  rfl

@[simp]
theorem mem_toSubMulAction₀ (p : PointedCone R M) {x : M} :
    x ∈ p.toSubMulAction₀ ↔ x ∈ p :=
  Iff.rfl

theorem toSubMulAction₀_injective :
    Function.Injective (PointedCone.toSubMulAction₀ (R := R) (M := M)) := by
  intro p q h
  ext x
  change x ∈ p.toSubMulAction₀ ↔ x ∈ q.toSubMulAction₀
  rw [h]

@[simp]
theorem toSubMulAction₀_inj {p q : PointedCone R M} :
    p.toSubMulAction₀ = q.toSubMulAction₀ ↔ p = q :=
  toSubMulAction₀_injective.eq_iff

theorem toSubMulAction₀_le {p q : PointedCone R M} :
    p.toSubMulAction₀ ≤ q.toSubMulAction₀ ↔ p ≤ q :=
  Iff.rfl

@[gcongr, mono]
theorem toSubMulAction₀_strictMono :
    StrictMono (PointedCone.toSubMulAction₀ (R := R) (M := M)) := by
  intro p q hpq
  exact hpq

@[gcongr, mono]
theorem toSubMulAction₀_monotone :
    Monotone (PointedCone.toSubMulAction₀ (R := R) (M := M)) :=
  toSubMulAction₀_strictMono.monotone

/-- The order embedding from PointedCones to zero-containing smul invariant subsets. -/
def toSubMulAction₀OrderEmbedding : PointedCone R M ↪o SubMulAction₀ R≥0 M where
  toFun := PointedCone.toSubMulAction₀
  inj' := toSubMulAction₀_injective
  map_rel_iff' := toSubMulAction₀_le

end SubMulAction₀

lemma mulAction_closure_le_hull (s : Set M) : closure R≥0 s ≤ hull R s := by
  intro x hx
  rw [mem_closure] at hx
  exact hx (hull R s) subset_hull

@[simp] theorem hull_mulAction_closure_eq_hull (s : Set M) :
    hull R (closure R≥0 s) = hull R s := by
  refine le_antisymm ?_ <| hull_mono subset_closure
  nth_rw 2 [← hull_hull]
  exact hull_mono (mulAction_closure_le_hull _)

lemma smulSet_le_hull (s : Set M) : R≥0 ∙ s ≤ hull R s := by
  rw [← closure_eq_smulSet]
  exact mulAction_closure_le_hull s

@[simp] theorem hull_smulSet_eq_hull (s : Set M) :
    hull R (R≥0 ∙ s) = hull R s := by
  rw [← closure_eq_smulSet]
  exact hull_mulAction_closure_eq_hull s

end Semiring

end PointedCone
