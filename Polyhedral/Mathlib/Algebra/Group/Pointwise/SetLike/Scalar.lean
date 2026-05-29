
import Mathlib.Algebra.Opposites
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Data.Set.NAry
import Mathlib.Tactic.Monotonicity.Attr
import Mathlib.Algebra.Group.Pointwise.Set.Scalar

import Polyhedral.Mathlib.Algebra.Group.Pointwise.SetLike.Basic

variable {α V β W : Type*}

variable [SetLike α V] [SetLike β W]

open Pointwise

/- # VAdd Set (Translation) # -/

class IsConcreteVAddSet (V β W : Type*) [SetLike β W] [VAdd V W] [VAdd V β] where
  coe_vaddSet' (x : V) (b : β) : (x +ᵥ b : β) = x +ᵥ (b : Set W)

namespace SetLike

variable [VAdd V W] [VAdd V β] [IsConcreteVAddSet V β W]

@[simp]
lemma coe_vaddSet (x : V) (b : β) : (x +ᵥ b : β) = x +ᵥ (b : Set W)
 := IsConcreteVAddSet.coe_vaddSet' x b

end SetLike

/- # VAdd # -/

class IsConcreteVAdd (α V β W : Type*) [SetLike α V] [SetLike β W] [VAdd V W] [VAdd α β] where
  coe_vadd' (a : α) (b : β) : (a +ᵥ b : β) = (a : Set V) +ᵥ (b : Set W)

namespace SetLike

variable [VAdd V W] [VAdd α β] [IsConcreteVAdd α V β W]

@[simp]
lemma coe_vset_add (a : α) (b : β) : (a +ᵥ b : β) = (a : Set V) +ᵥ (b : Set W)
 := IsConcreteVAdd.coe_vadd' a b

end SetLike
