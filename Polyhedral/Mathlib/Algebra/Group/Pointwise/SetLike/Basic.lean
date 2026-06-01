
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Mathlib.Data.Set.NAry
import Mathlib.Data.SetLike.Basic
import Mathlib.Algebra.Group.Pointwise.Set.Basic

import Polyhedral.Mathlib.Data.SetLike.IsConcrete

/-! ... -/

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
