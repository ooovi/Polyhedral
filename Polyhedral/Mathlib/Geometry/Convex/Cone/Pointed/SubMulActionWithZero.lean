/-
Copyright (c) 2026 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/

import Mathlib.Geometry.Convex.ConvexSpace.Module

import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Basic
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.LinearMap
import Polyhedral.Mathlib.GroupTheory.GroupAction.SubMulActionWithZero.Closure

/-! This file contains results involving both `PointedCone` and `SubMulActionWithZero`. -/

variable {R M : Type*}

namespace PointedCone

open Function Module SubMulActionWithZero

section Semiring

variable [Semiring R] [PartialOrder R] [IsOrderedRing R]
variable [AddCommMonoid M] [Module R M]

-- NOTE: this notation seems to be not used by the pretty printer

/- Note that the character `∙` U+2219 used below is different from the scalar multiplication
character `•` U+2022. -/
/-- Notation for the `SubMulActionWithZero` generated from a set `s` w.r.t. positive scalars,
short for `SubMulActionWithZero.closure R≥0 s`. -/
scoped notation:70 (priority := high) R:70 " ∙₊ " s:70 => { c : R // 0 ≤ c } ∙ s

local notation "R≥0" => {c : R // 0 ≤ c}

section SubMulActionWithZero

/-- Reinterpret a `PointedCone` as a `SubMulActionWithZero`. -/
@[coe] protected abbrev toSubMulActionWithZero (p : PointedCone R M) :
    SubMulActionWithZero R≥0 M := .ofClass (R := R≥0) p

instance instSubMulActionWithZero : Coe (PointedCone R M) (SubMulActionWithZero R≥0 M) :=
  ⟨PointedCone.toSubMulActionWithZero⟩

@[simp]
theorem coe_toSubMulActionWithZero (p : PointedCone R M) :
    (p.toSubMulActionWithZero : Set M) = p :=
  rfl

@[simp]
theorem mem_toSubMulActionWithZero (p : PointedCone R M) {x : M} :
    x ∈ p.toSubMulActionWithZero ↔ x ∈ p :=
  Iff.rfl

theorem toSubMulActionWithZero_injective :
    Function.Injective (PointedCone.toSubMulActionWithZero (R := R) (M := M)) := by
  intro p q h
  ext x
  change x ∈ p.toSubMulActionWithZero ↔ x ∈ q.toSubMulActionWithZero
  rw [h]

@[simp]
theorem toSubMulActionWithZero_inj {p q : PointedCone R M} :
    p.toSubMulActionWithZero = q.toSubMulActionWithZero ↔ p = q :=
  toSubMulActionWithZero_injective.eq_iff

theorem toSubMulActionWithZero_le {p q : PointedCone R M} :
    p.toSubMulActionWithZero ≤ q.toSubMulActionWithZero ↔ p ≤ q :=
  Iff.rfl

@[gcongr, mono]
theorem toSubMulActionWithZero_strictMono :
    StrictMono (PointedCone.toSubMulActionWithZero (R := R) (M := M)) := by
  intro p q hpq
  exact hpq

@[gcongr, mono]
theorem toSubMulActionWithZero_mono :
    Monotone (PointedCone.toSubMulActionWithZero (R := R) (M := M)) :=
  toSubMulActionWithZero_strictMono.monotone

/-- The order embedding from PointedCones to zero-containing smul invariant subsets. -/
def toSubMulActionWithZeroOrderEmbedding : PointedCone R M ↪o SubMulActionWithZero R≥0 M where
  toFun := PointedCone.toSubMulActionWithZero
  inj' := toSubMulActionWithZero_injective
  map_rel_iff' := toSubMulActionWithZero_le

end SubMulActionWithZero

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
