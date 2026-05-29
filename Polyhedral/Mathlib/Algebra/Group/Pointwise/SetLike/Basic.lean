
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Mathlib.Data.Set.NAry
import Mathlib.Data.SetLike.Basic
import Mathlib.Algebra.Group.Pointwise.Set.Basic

import Polyhedral.Mathlib.Data.SetLike.IsConcrete

variable {α V : Type*}

variable [SetLike α V]

open Pointwise

/- # Neg # -/

class IsConcreteNeg (α V : Type*) [SetLike α V] [Neg V] [Neg α] where
  coe_neg' (a : α) : (-a : α) = (-a : Set V)

namespace SetLike

variable [Neg V] [Neg α] [IsConcreteNeg α V]

@[simp]
lemma coe_neg (a : α) : (-a : α) = (-a : Set V) := IsConcreteNeg.coe_neg' a

end SetLike

/- # Neg # -/

namespace SetLike

variable [InvolutiveNeg V] [Neg α] [IsConcreteNeg α V]

instance : InvolutiveNeg α where
  neg_neg := by simp [← coe_set_eq]

end SetLike


/- # Add # -/

class IsConcreteAdd (α V : Type*) [SetLike α V] [Add V] [Add α] where
  coe_add' (a b : α) : (a + b : α) = (a + b : Set V)

namespace SetLike

variable [Add V] [Add α] [IsConcreteAdd α V]

@[simp]
lemma coe_add (a b : α) : (a + b : α) = (a + b : Set V) := IsConcreteAdd.coe_add' a b

end SetLike
