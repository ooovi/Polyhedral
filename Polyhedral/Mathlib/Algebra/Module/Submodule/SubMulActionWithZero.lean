
import Mathlib.Algebra.Module.Submodule.Defs

import Polyhedral.Mathlib.GroupTheory.GroupAction.SubMulActionWithZero

/-! This file conains results about `Submodule` and `SubMulActionWithZero`. -/

namespace Submodule

open Function Module

section SubMulActionWithZero

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/-- Reinterpret a `Submodule` as a `SubMulActionWithZero`. -/
@[coe] protected abbrev toSubMulActionWithZero (p : Submodule R M) :
    SubMulActionWithZero R M :=
  SubMulActionWithZero.ofClass (R := R) p

/- Is this coe a bad idea?
  * on the one hand, there is no such coercion from Submdule to SubMulAction.
  * on the other hand will we need this coercion to work with SubMulActionWithZero conveniently.
-/
instance instSubMulActionWithZero : Coe (Submodule R M) (SubMulActionWithZero R M) :=
  ⟨Submodule.toSubMulActionWithZero⟩

@[simp]
theorem coe_toSubMulActionWithZero (p : Submodule R M) :
    (p.toSubMulActionWithZero : Set M) = p :=
  rfl

@[simp]
theorem mem_toSubMulActionWithZero (p : Submodule R M) {x : M} :
    x ∈ p.toSubMulActionWithZero ↔ x ∈ p :=
  Iff.rfl

theorem toSubMulActionWithZero_injective :
    Function.Injective
      (Submodule.toSubMulActionWithZero (R := R) (M := M)) := by
  intro p q h
  ext x
  change x ∈ p.toSubMulActionWithZero ↔ x ∈ q.toSubMulActionWithZero
  rw [h]

@[simp]
theorem toSubMulActionWithZero_inj {p q : Submodule R M} :
    p.toSubMulActionWithZero = q.toSubMulActionWithZero ↔ p = q :=
  toSubMulActionWithZero_injective.eq_iff

theorem toSubMulActionWithZero_le {p q : Submodule R M} :
    p.toSubMulActionWithZero ≤ q.toSubMulActionWithZero ↔ p ≤ q :=
  Iff.rfl

@[gcongr, mono]
theorem toSubMulActionWithZero_strictMono :
    StrictMono
      (Submodule.toSubMulActionWithZero (R := R) (M := M)) := by
  intro p q hpq
  exact hpq

@[gcongr, mono]
theorem toSubMulActionWithZero_mono :
    Monotone
      (Submodule.toSubMulActionWithZero (R := R) (M := M)) :=
  toSubMulActionWithZero_strictMono.monotone

/-- The order embedding from submodules to zero-containing smul invariant subsets. -/
def toSubMulActionWithZeroOrderEmbedding :
    Submodule R M ↪o SubMulActionWithZero R M where
  toFun := Submodule.toSubMulActionWithZero
  inj' := toSubMulActionWithZero_injective
  map_rel_iff' := toSubMulActionWithZero_le

end SubMulActionWithZero

end Submodule
