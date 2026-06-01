
import Mathlib.Algebra.Opposites
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Data.Set.NAry
import Mathlib.Tactic.Monotonicity.Attr
import Mathlib.Algebra.Group.Pointwise.Set.Scalar

import Polyhedral.Mathlib.Algebra.Group.Pointwise.SetLike.Basic

/-! ... -/

variable {α V β W : Type*}

variable [SetLike α V] [SetLike β W]

open Pointwise

/- # VAdd Set (Translation) # -/

class IsConcreteVAddSet (V β W : Type*) [SetLike β W] [VAdd V W] [VAdd V β] where
  coe_vaddSet' (x : V) (b : β) : (x +ᵥ b : β) = x +ᵥ (b : Set W)

@[to_additive]
class IsConcreteSMulSet (V β W : Type*) [SetLike β W] [SMul V W] [SMul V β] where
  coe_smulSet' (x : V) (b : β) : (x • b : β) = x • (b : Set W)

namespace SetLike

variable [SMul V W] [SMul V β] [IsConcreteSMulSet V β W]

@[to_additive (attr := simp, grind =)]
lemma coe_smulSet (x : V) (b : β) : (x • b : β) = x • (b : Set W) :=
  IsConcreteSMulSet.coe_smulSet' x b

end SetLike

/- # VAdd # -/

class IsConcreteVAdd (α V β W : Type*) [SetLike α V] [SetLike β W] [VAdd V W] [VAdd α β] where
  coe_vadd' (a : α) (b : β) : (a +ᵥ b : β) = (a : Set V) +ᵥ (b : Set W)

@[to_additive]
class IsConcreteSMul (α V β W : Type*) [SetLike α V] [SetLike β W] [SMul V W] [SMul α β] where
  coe_smul' (a : α) (b : β) : (a • b : β) = (a : Set V) • (b : Set W)

namespace SetLike

variable [SMul V W] [SMul α β] [IsConcreteSMul α V β W]

@[to_additive (attr := simp, grind =)]
lemma coe_smul (a : α) (b : β) : (a • b : β) = (a : Set V) • (b : Set W) :=
  IsConcreteSMul.coe_smul' a b

end SetLike
