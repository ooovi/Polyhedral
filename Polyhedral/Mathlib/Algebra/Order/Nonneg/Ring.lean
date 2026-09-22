/-
Copyright (c) 2026 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/
module

public import Polyhedral.Mathlib.Algebra.Order.Nonneg.Basic
public import Mathlib.Algebra.Order.Ring.Defs

/-!
This file contains auxiliary lemmas for working with `Nonneg R`, where `R` is a semiring.
-/

public section

assert_not_exists abs_inv

open Set

variable {R : Type*}

local notation3 "R≥0" => Nonneg R

namespace Nonneg

variable [Semiring R] [PartialOrder R]

@[simp] lemma coe_eq_zero {a : R≥0} : (a : R) = 0 ↔ a = 0 := by aesop

variable [IsOrderedRing R]

@[simp] lemma coe_eq_one {a : R≥0} : (a : R) = 1 ↔ a = 1 := by aesop

end Nonneg
