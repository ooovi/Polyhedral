/-
Copyright (c) 2026 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/

import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Mathlib.Data.Set.NAry
import Mathlib.Data.SetLike.Basic
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Algebra.Group.Defs

import Polyhedral.Mathlib.Data.SetLike.IsConcrete

/-! This files defines the pointwise operations on `SetLike` that are inherited from `Set`-/

variable {α V : Type*}

variable [SetLike α V]

open Pointwise

/- # Zero / One # -/

class IsConcreteZero (α V : Type*) [SetLike α V] [Zero V] [Zero α] where
  coe_zero' : (0 : α) = (0 : Set V)

@[to_additive]
class IsConcreteOne (α V : Type*) [SetLike α V] [One V] [One α] where
  coe_one' : (1 : α) = (1 : Set V)

namespace SetLike

variable [One V] [One α] [IsConcreteOne α V]

@[to_additive (attr := simp, grind =)]
lemma coe_one : (1 : α) = (1 : Set V) := IsConcreteOne.coe_one'

end SetLike

/- # Neg / Inv # -/

class IsConcreteNeg (α V : Type*) [SetLike α V] [Neg V] [Neg α] where
  coe_neg' (a : α) : (-a : α) = (-a : Set V)

@[to_additive]
class IsConcreteInv (α V : Type*) [SetLike α V] [Inv V] [Inv α] where
  coe_inv' (a : α) : (a⁻¹ : α) = (a⁻¹ : Set V)

namespace SetLike

variable [Inv V] [Inv α] [IsConcreteInv α V]

@[to_additive (attr := simp, grind =)]
lemma coe_inv (a : α) : (a⁻¹ : α) = (a⁻¹ : Set V) := IsConcreteInv.coe_inv' a

end SetLike

/- # InvolutiveNeg / InvolutiveInv # -/

namespace SetLike

variable [InvolutiveInv V] [Inv α] [IsConcreteInv α V]

@[to_additive, reducible]
def _root_.InvolutiveInv.ofSetLike : InvolutiveInv α where
  inv_inv := by simp [← coe_set_eq]

end SetLike

/- # Add / Mul # -/

class IsConcreteAdd (α V : Type*) [SetLike α V] [Add V] [Add α] where
  coe_add' (a b : α) : (a + b : α) = (a + b : Set V)

@[to_additive]
class IsConcreteMul (α V : Type*) [SetLike α V] [Mul V] [Mul α] where
  coe_mul' (a b : α) : (a * b : α) = (a * b : Set V)

namespace SetLike

variable [Mul V] [Mul α] [IsConcreteMul α V]

@[to_additive (attr := simp, grind =)]
lemma coe_mul (a b : α) : (a * b : α) = (a * b : Set V) := IsConcreteMul.coe_mul' a b

end SetLike

/- # Div / Sub # -/

class IsConcreteSub (α V : Type*) [SetLike α V] [Sub V] [Sub α] where
  coe_sub' (a b : α) : (a - b : α) = (a - b : Set V)

@[to_additive]
class IsConcreteDiv (α V : Type*) [SetLike α V] [Div V] [Div α] where
  coe_div' (a b : α) : (a / b : α) = (a / b : Set V)

namespace SetLike

variable [Div V] [Div α] [IsConcreteDiv α V]

@[to_additive (attr := simp, grind =)]
lemma coe_div (a b : α) : (a / b : α) = (a / b : Set V) := IsConcreteDiv.coe_div' a b

end SetLike

-- TODO: implement `SetLike.NPow`?

variable (α V)

/- # Algebraic Hierarchy # -/

/- # Semigroup -/

@[reducible, to_additive]
def Semigroup.ofSetLike [Semigroup V] [SetLike α V] [Mul α] [IsConcreteMul α V] :
    Semigroup α where
  mul_assoc := by simp [← SetLike.coe_set_eq, mul_assoc]

class IsConcreteAddSemigroup [SetLike α V] [AddSemigroup V] [AddSemigroup α]
    extends IsConcreteAdd α V

@[to_additive]
class IsConcreteSemigroup [SetLike α V] [Semigroup V] [Semigroup α]
    extends IsConcreteMul α V

@[to_additive]
instance [Semigroup V] [SetLike α V] [Mul α] [IsConcreteMul α V] :
    letI := Semigroup.ofSetLike α V; IsConcreteSemigroup α V :=
  letI := Semigroup.ofSetLike α V; { }

/- # CommSemigroup -/

@[reducible, to_additive]
def CommSemigroup.ofSetLike [CommSemigroup V] [SetLike α V] [Mul α] [IsConcreteMul α V] :
    CommSemigroup α where
  __ := Semigroup.ofSetLike ..
  mul_comm := by simp [← SetLike.coe_set_eq, mul_comm]

class IsConcreteAddCommSemigroup [SetLike α V] [AddSemigroup V] [AddSemigroup α]
    extends IsConcreteAddSemigroup α V

@[to_additive]
class IsConcreteCommSemigroup [SetLike α V] [Semigroup V] [Semigroup α]
    extends IsConcreteSemigroup α V

@[to_additive]
instance [CommSemigroup V] [SetLike α V] [Mul α] [IsConcreteMul α V] :
    letI := CommSemigroup.ofSetLike α V; IsConcreteCommSemigroup α V :=
  letI := CommSemigroup.ofSetLike α V; { }

/- # MulOneClass -/

@[reducible, to_additive]
def MulOneClass.ofSetLike [MulOneClass V] [SetLike α V] [One α] [IsConcreteOne α V]
    [Mul α] [IsConcreteMul α V] : MulOneClass α where
  one_mul := by simp [← SetLike.coe_set_eq]
  mul_one := by simp [← SetLike.coe_set_eq]

class IsConcreteAddZeroClass [SetLike α V] [AddZeroClass V] [AddZeroClass α]
    extends IsConcreteZero α V, IsConcreteAdd α V

@[to_additive]
class IsConcreteMulOneClass [SetLike α V] [MulOneClass V] [MulOneClass α]
    extends IsConcreteOne α V, IsConcreteMul α V

@[to_additive]
instance [MulOneClass V] [SetLike α V] [One α] [IsConcreteOne α V] [Mul α] [IsConcreteMul α V] :
    letI := MulOneClass.ofSetLike α V; IsConcreteMulOneClass α V :=
  letI := MulOneClass.ofSetLike α V; { }

/- # Monoid -/

@[reducible, to_additive]
def Monoid.ofSetLike [Monoid V] [SetLike α V] [One α] [IsConcreteOne α V]
    [Mul α] [IsConcreteMul α V] : Monoid α where
  __ := Semigroup.ofSetLike ..
  __ := MulOneClass.ofSetLike ..
  -- TODO: provide explicit NPow?

class IsConcreteAddMonoid [SetLike α V] [AddMonoid V] [AddMonoid α]
    extends IsConcreteAddSemigroup α V, IsConcreteAddZeroClass α V

@[to_additive]
class IsConcreteMonoid [SetLike α V] [Monoid V] [Monoid α]
    extends IsConcreteSemigroup α V, IsConcreteMulOneClass α V

@[to_additive]
instance [Monoid V] [SetLike α V] [One α] [IsConcreteOne α V] [Mul α] [IsConcreteMul α V] :
    letI := Monoid.ofSetLike α V; IsConcreteMonoid α V :=
  letI := Monoid.ofSetLike α V; { }

/- # CommMonoid -/

@[reducible, to_additive]
def CommMonoid.ofSetLike [CommMonoid V] [SetLike α V] [One α] [IsConcreteOne α V]
    [Mul α] [IsConcreteMul α V] : CommMonoid α where
  __ := Monoid.ofSetLike ..
  __ := CommSemigroup.ofSetLike ..

class IsConcreteAddCommMonoid [SetLike α V] [AddCommMonoid V] [AddCommMonoid α]
    extends IsConcreteAddCommSemigroup α V, IsConcreteAddMonoid α V

@[to_additive]
class IsConcreteCommMonoid [SetLike α V] [CommMonoid V] [CommMonoid α]
    extends IsConcreteCommSemigroup α V, IsConcreteMonoid α V

@[to_additive]
instance [CommMonoid V] [SetLike α V] [One α] [IsConcreteOne α V] [Mul α] [IsConcreteMul α V] :
    letI := CommMonoid.ofSetLike α V; IsConcreteCommMonoid α V :=
  letI := CommMonoid.ofSetLike α V; { }

/- # DivisionMonoid -/

@[reducible, to_additive]
def DivisionMonoid.ofSetLike [DivisionMonoid V] [SetLike α V] [One α] [IsConcreteOne α V]
    [Inv α] [IsConcreteInv α V] [Mul α] [IsConcreteMul α V] [Div α] [IsConcreteDiv α V] :
    DivisionMonoid α where
  __ := Monoid.ofSetLike ..
  __ := InvolutiveInv.ofSetLike ..
  div_eq_mul_inv := by simp [← SetLike.coe_set_eq, div_eq_mul_inv]
  mul_inv_rev := by simp [← SetLike.coe_set_eq]
  inv_eq_of_mul s t h := by
    -- NOTE: the obvious way to prove this runs into a diamond between `this.toMul` and `Set.mul`.
    simp only [← SetLike.coe_set_eq, SetLike.coe_mul, SetLike.coe_one, SetLike.coe_inv] at ⊢ h
    obtain ⟨a, b, ha, hb, hab⟩ := Set.mul_eq_one_iff.1 h
    rw [ha, hb, Set.inv_singleton, inv_eq_of_mul_eq_one_right hab]

/- # DivisionCommMonoid -/

@[reducible, to_additive]
def DivisionCommMonoid.ofSetLike [DivisionCommMonoid V] [SetLike α V] [One α] [IsConcreteOne α V]
    [Inv α] [IsConcreteInv α V] [Mul α] [IsConcreteMul α V] [Div α] [IsConcreteDiv α V] :
    DivisionCommMonoid α where
  __ := DivisionMonoid.ofSetLike ..
  __ := CommMonoid.ofSetLike ..
