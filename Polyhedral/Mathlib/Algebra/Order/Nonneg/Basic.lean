/-
Copyright (c) 2021 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/

import Mathlib.Algebra.Order.Nonneg.Basic

/-!
...
-/

assert_not_exists abs_inv

abbrev Nonneg (R : Type*) [Zero R] [PartialOrder R] := {c : R // 0 ≤ c}
