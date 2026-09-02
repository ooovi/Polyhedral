/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Data.Finsupp.Option

import Polyhedral.Mathlib.Data.Finsupp.Basic

/-!
# Restricting a finsupp on `Option`, `WithTop` or `WithBot`

This file contains material destined for `Mathlib/Data/Finsupp/Option.lean`.

## Main declarations

* `Finsupp.withTopSome`/`Finsupp.withBotSome`: `Finsupp.some` stated for `WithTop`/`WithBot` rather
  than for `Option`, so that the two are duals of each other under `@[to_dual]`.
-/

public noncomputable section

namespace Finsupp
variable {α M N : Type*}

section Option
variable [Zero M]

@[simp]
lemma embDomain_some_of_none_eq_zero {f : Option α →₀ M} (hf : f none = 0) :
    f.some.embDomain .some = f := by
  ext a
  cases a with
  | none => rw [embDomain_some_none, hf]
  | some a => rw [embDomain_some_some, some_apply]

@[to_additive]
lemma prod_some [CommMonoid N] {f : Option α →₀ M} (hf : f none = 0) (g : Option α → M → N) :
    (f.some.prod fun a ↦ g (Option.some a)) = f.prod g := by
  conv_rhs => rw [← embDomain_some_of_none_eq_zero hf]
  rw [prod_embDomain]
  rfl

end Option

section WithTop
variable [Zero M]

/-- Restrict a finitely supported function on `WithTop α` to a finitely supported function on `α`.

This is `Finsupp.some` stated for `WithTop`, so that it dualises to `Finsupp.withBotSome`. -/
@[expose, to_dual
/-- Restrict a finitely supported function on `WithBot α` to a finitely supported function on `α`.

This is `Finsupp.some` stated for `WithBot`, so that it dualises to `Finsupp.withTopSome`. -/]
def withTopSome (f : WithTop α →₀ M) : α →₀ M := f.comapDomain (↑) WithTop.coe_injective.injOn

@[to_dual (attr := simp)]
lemma withTopSome_apply (f : WithTop α →₀ M) (a : α) : f.withTopSome a = f a := rfl

@[to_additive (attr := to_dual)]
lemma prod_withTopSome [CommMonoid N] {f : WithTop α →₀ M} (hf : f ⊤ = 0)
    (g : WithTop α → M → N) : (f.withTopSome.prod fun a ↦ g (a : WithTop α)) = f.prod g := by
  refine prod_comapDomain ((↑) : α → WithTop α) f g
    ⟨fun a ha ↦ ha, WithTop.coe_injective.injOn, fun b hb ↦ ?_⟩
  induction b with
  | top => exact absurd (Finsupp.mem_support_iff.1 hb) (not_not.2 hf)
  | coe a => exact ⟨a, hb, rfl⟩

end WithTop

end Finsupp
