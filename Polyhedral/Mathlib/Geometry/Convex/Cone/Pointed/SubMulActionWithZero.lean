

import Mathlib.Geometry.Convex.ConvexSpace.Module

import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Basic
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.LinearMap
import Polyhedral.Mathlib.GroupTheory.GroupAction.SubMulActionWithZero.Closure

/-! This file conains results about `PointedCone` and `SubMulActionWithZero`. -/

variable {R M : Type*}

namespace SubMulActionWithZero

section Semiring

variable [Semiring R] [PartialOrder R] [IsOrderedRing R]
variable [AddCommMonoid M] [Module R M]

-- TODO: this notation seems to be not recognized by the elaborator. Why?

/- Note that the character `∙` U+2219 used below is different from the scalar multiplication
character `•` U+2022. -/
/-- Notation for the `SubMulActionWithZero` generated from a set `s` w.r.t. positive scalars,
short for `SubMulActionWithZero.closure R≥0 s`. -/
scoped notation:70 R:70 " ∙₊ " s:70 => SubMulActionWithZero.closure R≥0 s

end Semiring

/- # Convexity # -/

open Convexity

section Semiring

variable [DivisionSemiring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [AddCommMonoid M] [Module R M] [ConvexSpace R M] [IsModuleConvexSpace R M]

local notation "R≥0" => {c : R // 0 ≤ c}

def toPointedCone {S : SubMulActionWithZero R≥0 M} (hS : IsConvexSet R (S : Set M)) :
    PointedCone R M where
  carrier := S
  add_mem' := by
    intro x y hx hy
    have : 0 ≤ (2 : R)⁻¹ := by sorry
    have :=  hS.convexCombPair_mem hx hy this this (by sorry)
    rw [convexCombPair_eq_sum] at this
    have := S.smul_mem 2 this
    simp at this
    -- rw [smul_smul] at this
    sorry
  zero_mem' := S.zero_mem
  smul_mem' := S.smul_mem

end Semiring

end SubMulActionWithZero

namespace PointedCone

open Function Module

section Semiring

variable [Semiring R] [PartialOrder R] [IsOrderedRing R]
variable [AddCommMonoid M] [Module R M]

local notation "R≥0" => {c : R // 0 ≤ c}

/-- Reinterpret a `PointedCone` as a `SubMulActionWithZero`. -/
@[coe] protected abbrev toSubMulActionWithZero (p : PointedCone R M) :
    SubMulActionWithZero R≥0 M :=
  SubMulActionWithZero.ofClass (R := R≥0) p

/- Is this coe a bad idea? -/
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
    Function.Injective
      (PointedCone.toSubMulActionWithZero (R := R) (M := M)) := by
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
    StrictMono
      (PointedCone.toSubMulActionWithZero (R := R) (M := M)) := by
  intro p q hpq
  exact hpq

@[gcongr, mono]
theorem toSubMulActionWithZero_mono :
    Monotone
      (PointedCone.toSubMulActionWithZero (R := R) (M := M)) :=
  toSubMulActionWithZero_strictMono.monotone

/-- The order embedding from PointedCones to zero-containing smul invariant subsets. -/
def toSubMulActionWithZeroOrderEmbedding :
    PointedCone R M ↪o SubMulActionWithZero R≥0 M where
  toFun := PointedCone.toSubMulActionWithZero
  inj' := toSubMulActionWithZero_injective
  map_rel_iff' := toSubMulActionWithZero_le

end Semiring

end PointedCone
