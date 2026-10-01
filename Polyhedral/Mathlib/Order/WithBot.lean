/-
Copyright (c) 2026 Vlad Tsyrklevich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vlad Tsyrklevich
-/

module

public import Mathlib.Algebra.Order.SuccPred.WithBot
public import Mathlib.Data.Nat.SuccPred
public import Mathlib.Order.SuccPred.WithBot
public import Mathlib.Order.WithBot

/-! WithBot lemmas -/

public section

namespace WithBot

theorem natCast_orderSucc (a : ℕ) : Nat.cast (Order.succ a) = Order.succ (a : WithBot ℕ) :=
  WithBot.orderSucc_coe _

@[simp]
theorem pred_natCast_add_one (a : ℕ) : Order.pred ((a : WithBot ℕ) + 1) = a := by
  rw [← Nat.cast_succ, ← Nat.succ_eq_succ, natCast_orderSucc]
  simp

end WithBot
