/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Data.Finsupp.Basic

/-!
# Miscellaneous lemmas about `Finsupp.mapDomain` and `Finsupp.comapDomain`

This file contains material destined for `Mathlib/Data/Finsupp/Basic.lean`.
-/

public section

namespace Finsupp
variable {α β M N : Type*}

section MapDomain
variable [AddCommMonoid M]

/-- Upstream, this generalises `Finsupp.mapDomain_apply_eq_sum` from `b = f a` to any `b`. -/
lemma mapDomain_apply_eq_sum' [DecidableEq β] (f : α → β) (x : α →₀ M) (b : β) :
    x.mapDomain f b = ∑ i ∈ x.support with f i = b, x i := by
  simp [mapDomain, sum, single_apply, Finset.sum_ite]

@[simp]
lemma filter_mapDomain (v : α →₀ M) (f : α → β) (p : β → Prop) [DecidablePred p] :
    (v.mapDomain f).filter p = (v.filter fun a ↦ p (f a)).mapDomain f := by
  classical
  ext b
  transitivity ∑ a ∈ v.support with f a = b, if p b then v a else 0
  · simp [filter_apply, mapDomain_apply_eq_sum']
  simp only [filter_apply, mapDomain_apply_eq_sum', support_filter, Finset.filter_filter,
    Finset.sum_ite, Finset.sum_const_zero, add_zero]
  congr! 2 with a
  grind

end MapDomain
end Finsupp
