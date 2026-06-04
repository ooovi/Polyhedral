/-
Copyright (c) 2026 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/

import Mathlib.Algebra.Opposites
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Data.Set.NAry
import Mathlib.Tactic.Monotonicity.Attr
import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
import Mathlib.Algebra.Group.Pointwise.Set.Scalar
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.GroupWithZero.Action.Pointwise.Set

import Polyhedral.Mathlib.Algebra.Group.Pointwise.SetLike.Basic

/-! This files defines the pointwise operations on `SetLike` that are inherited from `Set` and
  are introduced in Set/Scalar.lean -/

variable {ρ R α V : Type*}

variable [SetLike ρ R] [SetLike α V]

open Pointwise

/- # VAdd Set / SMul Set # -/

class IsConcreteVAddSet (R α V : Type*) [SetLike α V] [VAdd R V] [VAdd R α] where
  coe_vaddSet' (r : R) (a : α) : (r +ᵥ a : α) = r +ᵥ (a : Set V)

@[to_additive]
class IsConcreteSMulSet (R α V : Type*) [SetLike α V] [SMul R V] [SMul R α] where
  coe_smulSet' (r : R) (a : α) : (r • a : α) = r • (a : Set V)

namespace SetLike

variable [SMul R V] [SMul R α] [IsConcreteSMulSet R α V]

@[to_additive (attr := simp, grind =)]
lemma coe_smulSet (r : R) (a : α) : (r • a : α) = r • (a : Set V) :=
  IsConcreteSMulSet.coe_smulSet' r a

end SetLike

/- # VAdd / SMul # -/

class IsConcreteVAdd (ρ R α V : Type*) [SetLike ρ R] [SetLike α V] [VAdd R V] [VAdd ρ α] where
  coe_vadd' (r : ρ) (a : α) : (r +ᵥ a : α) = (r : Set R) +ᵥ (a : Set V)

@[to_additive]
class IsConcreteSMul (ρ R α V : Type*) [SetLike ρ R] [SetLike α V] [SMul R V] [SMul ρ α] where
  coe_smul' (r : ρ) (a : α) : (r • a : α) = (r : Set R) • (a : Set V)

namespace SetLike

variable [SMul R V] [SMul ρ α] [IsConcreteSMul ρ R α V]

@[to_additive (attr := simp, grind =)]
lemma coe_smul (r : ρ) (a : α) : (r • a : α) = (r : Set R) • (a : Set V) :=
  IsConcreteSMul.coe_smul' r a

end SetLike

/- # Algebraic Hierarchy -/

variable (ρ R α V)

@[to_additive (attr := reducible)]
def MulAction.ofSetLike [SetLike ρ R] [Monoid R] [Monoid ρ] [IsConcreteOne ρ R] [IsConcreteMul ρ R]
    [SetLike α V] [MulAction R V] [SMul ρ α] [IsConcreteSMul ρ R α V] :
    MulAction ρ α where
  mul_smul := by simp [← SetLike.coe_set_eq, mul_smul]
  one_smul := by simp [← SetLike.coe_set_eq]

@[to_additive (attr := reducible)]
def MulAction.ofSetLike_set [Monoid R] [SetLike α V] [MulAction R V] [SMul R α]
    [IsConcreteSMulSet R α V] : MulAction R α where
  mul_smul := by simp [← SetLike.coe_set_eq, mul_smul]
  one_smul := by simp [← SetLike.coe_set_eq]

/-
TODO:
 - SMulCommClass (VaddCommClass)
 - IsScalarTower (VAddAssoc)
 - IsCentralScalar (IsCentralVAdd)
-/

@[reducible]
def SMulZeroClass.ofSetLike [SetLike α V] [Zero V] [Zero α] [IsConcreteZero α V]
    [SMulZeroClass R V] [SMul R α] [IsConcreteSMulSet R α V] :
    SMulZeroClass R α where
  smul_zero := by simp [← SetLike.coe_set_eq]

@[reducible]
def DistribSMul.ofSetLike [SetLike α V] [AddZeroClass V] [AddZeroClass α]
    [IsConcreteZero α V] [IsConcreteAdd α V] [DistribSMul R V] [SMul R α]
    [IsConcreteSMulSet R α V] : DistribSMul R α where
  __ := SMulZeroClass.ofSetLike ..
  smul_add := by simp [← SetLike.coe_set_eq, smul_add]

@[reducible]
def DistribMulAction.ofSetLike [Monoid R] [SetLike α V] [AddMonoid V] [AddMonoid α]
    [IsConcreteZero α V] [IsConcreteAdd α V] [DistribMulAction R V] [SMul R α]
    [IsConcreteSMulSet R α V] : DistribMulAction R α where
  __ := MulAction.ofSetLike_set ..
  smul_add := by simp [← SetLike.coe_set_eq, smul_add]
  smul_zero :=  by simp [← SetLike.coe_set_eq]

@[reducible]
def MulDistribMulAction.ofSetLike [Monoid R] [SetLike α V] [Monoid V] [Monoid α]
    [IsConcreteOne α V] [IsConcreteMul α V] [MulDistribMulAction R V] [SMul R α]
    [IsConcreteSMulSet R α V] : MulDistribMulAction R α where
  __ := MulAction.ofSetLike_set ..
  smul_one := by simp [← SetLike.coe_set_eq, smul_one]
  smul_mul := by simp [← SetLike.coe_set_eq, smul_mul]

/- NOTE: `SMulWithZero` and `Module` can only be defined on non-empty sets for which we
    have no predefined type. -/
