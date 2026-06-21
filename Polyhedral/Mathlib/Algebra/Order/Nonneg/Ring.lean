/-
Copyright (c) 2021 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/

import Polyhedral.Mathlib.Algebra.Order.Nonneg.Basic
import Mathlib.Algebra.Order.Ring.Defs

/-!
...
-/

assert_not_exists abs_inv

open Set

variable {R : Type*}

local notation3 "R≥0" => {c : R // 0 ≤ c} -- Nonneg R

namespace Nonneg

variable [Semiring R] [PartialOrder R]

@[simp] lemma coe_eq_zero {a : R≥0} : (a : R) = 0 ↔ a = 0 := by aesop

variable [IsOrderedRing R]

@[simp] lemma coe_eq_one {a : R≥0} : (a : R) = 1 ↔ a = 1 := by aesop

end Nonneg
