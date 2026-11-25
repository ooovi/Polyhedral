/-
Copyright (c) 2026 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/
module

public import Mathlib.Algebra.Order.Nonneg.Basic

/-! # Nonnegative elements -/

public section

variable {R : Type*} [Zero R] [LE R]

/-- The underlying value of a nonnegative element is nonnegative. -/
protected lemma Nonneg.nonneg (r : Nonneg R) : 0 ≤ (r : R) := r.property
