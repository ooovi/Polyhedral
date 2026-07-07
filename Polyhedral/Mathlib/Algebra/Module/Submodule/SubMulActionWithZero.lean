
import Mathlib.Algebra.Module.Submodule.Defs

import Polyhedral.Mathlib.GroupTheory.GroupAction.SubMulActionWithZero

/-! This file conains results about `Submodule` and `SubMulAction₀`. -/

namespace Submodule

open Function Module

section SubMulAction₀

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/-- Reinterpret a `Submodule` as a `SubMulAction₀`. -/
@[coe] protected abbrev toSubMulAction₀ (p : Submodule R M) :
    SubMulAction₀ R M :=
  SubMulAction₀.ofClass (R := R) p

/- Is this coe a bad idea?
  * on the one hand, there is no such coercion from Submdule to SubMulAction.
  * on the other hand will we need this coercion to work with SubMulAction₀ conveniently.
-/
instance instSubMulAction₀ : Coe (Submodule R M) (SubMulAction₀ R M) :=
  ⟨Submodule.toSubMulAction₀⟩

@[simp]
theorem coe_toSubMulAction₀ (p : Submodule R M) :
    (p.toSubMulAction₀ : Set M) = p :=
  rfl

@[simp]
theorem mem_toSubMulAction₀ (p : Submodule R M) {x : M} :
    x ∈ p.toSubMulAction₀ ↔ x ∈ p :=
  Iff.rfl

theorem toSubMulAction₀_injective :
    Function.Injective
      (Submodule.toSubMulAction₀ (R := R) (M := M)) := by
  intro p q h
  ext x
  change x ∈ p.toSubMulAction₀ ↔ x ∈ q.toSubMulAction₀
  rw [h]

@[simp]
theorem toSubMulAction₀_inj {p q : Submodule R M} :
    p.toSubMulAction₀ = q.toSubMulAction₀ ↔ p = q :=
  toSubMulAction₀_injective.eq_iff

theorem toSubMulAction₀_le {p q : Submodule R M} :
    p.toSubMulAction₀ ≤ q.toSubMulAction₀ ↔ p ≤ q :=
  Iff.rfl

@[gcongr, mono]
theorem toSubMulAction₀_strictMono :
    StrictMono
      (Submodule.toSubMulAction₀ (R := R) (M := M)) := by
  intro p q hpq
  exact hpq

@[gcongr, mono]
theorem toSubMulAction₀_mono :
    Monotone
      (Submodule.toSubMulAction₀ (R := R) (M := M)) :=
  toSubMulAction₀_strictMono.monotone

/-- The order embedding from submodules to zero-containing smul invariant subsets. -/
def toSubMulAction₀OrderEmbedding :
    Submodule R M ↪o SubMulAction₀ R M where
  toFun := Submodule.toSubMulAction₀
  inj' := toSubMulAction₀_injective
  map_rel_iff' := toSubMulAction₀_le

end SubMulAction₀

end Submodule
