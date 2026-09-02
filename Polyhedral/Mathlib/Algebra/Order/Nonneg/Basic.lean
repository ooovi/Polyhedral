/-
Copyright (c) 2026 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/
module

public import Mathlib.Algebra.Order.Nonneg.Basic

/-!
This file defines the name `Nonneg R` for `{c : R // 0 ≤ c}`. Currently, mathlib files that
use the latter type introduce a new notation `R≥0`. But since this notation depends on the
input type being called `R`, this is not a global notation.
-/

public section

assert_not_exists abs_inv

abbrev Nonneg (R : Type*) [Zero R] [LE R] := {c : R // 0 ≤ c}
