/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

-- PR #43261

public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Order.Lattice

public section

section MulZero

variable {M₀ α} [Mul M₀] [Zero M₀]

section Preorder
variable [Preorder M₀] [Preorder α] {a : M₀} {f g : α → M₀}

lemma strictMono_mul_left_of_pos' [PosMulStrictMono M₀] (ha : 0 < a) :
    StrictMono fun x ↦ a * x := fun _ _ b_lt_c ↦ mul_lt_mul_of_pos_left b_lt_c ha

lemma strictMono_mul_right_of_pos' [MulPosStrictMono M₀] (ha : 0 < a) :
    StrictMono fun x ↦ x * a := fun _ _ b_lt_c ↦ mul_lt_mul_of_pos_right b_lt_c ha

end Preorder

section LinearOrder
variable [LinearOrder M₀] {a : M₀}

lemma IsLeftRegular.of_pos [PosMulStrictMono M₀] (ha : 0 < a) : IsLeftRegular a :=
  (strictMono_mul_left_of_pos' ha).injective

lemma IsRightRegular.of_pos [MulPosStrictMono M₀] (ha : 0 < a) : IsRightRegular a :=
  (strictMono_mul_right_of_pos' ha).injective

lemma IsRegular.of_pos [PosMulStrictMono M₀] [MulPosStrictMono M₀] (ha : 0 < a) : IsRegular a :=
  ⟨.of_pos ha, .of_pos ha⟩

end LinearOrder

end MulZero

-- end PR #43261
