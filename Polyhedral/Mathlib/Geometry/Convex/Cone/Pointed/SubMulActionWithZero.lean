
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Basic
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.LinearMap
import Polyhedral.Mathlib.GroupTheory.GroupAction.SubMulActionWithZero.Closure

/-! This file conains results about `PointedCone` and `SubMulActionWithZero`. -/

namespace PointedCone

open Function Module

variable {R : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommMonoid M] [Module R M]

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

end PointedCone

namespace SubMulActionWithZero

variable {R : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommMonoid M] [Module R M]

-- TODO: this notation seems to be not recognized by the elaborator. Why?

/- Note that the character `∙` U+2219 used below is different from the scalar multiplication
character `•` U+2022. -/
/-- Notation for the `SubMulActionWithZero` generated from a set `s` w.r.t. positive scalars,
short for `SubMulActionWithZero.closure R≥0 s`. -/
scoped notation:70 R:70 " ∙₊ " s:70 => SubMulActionWithZero.closure R≥0 s

end SubMulActionWithZero
