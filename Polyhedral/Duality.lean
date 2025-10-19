/-
Copyright (c) 2020 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/
import Mathlib.Order.Closure

open Set OrderDual

/-! ### Preduality operator -/

/- I am uncertain about the connection of all of this to `GaloisConnections`. -/

variable (α β : Type*) -- {ι : Sort*} {κ : ι → Sort*}
variable [Preorder α] [Preorder β]

/-- A closure operator on the preorder `α` is a monotone function which is extensive (every `x`
is less than its closure) and idempotent. -/
structure PreDualityOperator extends α →o β where
  rev' : β →o α
  antitone'    : ∀ s t, s ≤ t → toFun s ≤ toFun t
  antitoneRev' : ∀ s t, s ≤ t → rev' s ≤ rev' t
  subset'      : ∀ s, s ≤ rev' (toFun s)
  subsetRev'   : ∀ s, s ≤ toFun (rev' s)
  triple'      : ∀ s, toFun (rev' (toFun s)) = toFun s
  tripleRev'   : ∀ s, rev' (toFun (rev' s)) = rev' s

namespace PreDualityOperator

instance : FunLike (PreDualityOperator α β) α β where
  coe c := c.1
  coe_injective' := sorry
    --by rintro ⟨⟩ ⟨⟩ h; obtain rfl := DFunLike.ext' h; congr with x; simp_all

instance : OrderHomClass (PreDualityOperator α β) α β where
  map_rel f _ _ h := f.mono h

-- initialize_simps_projections PreDualityOperator (toFun → apply, IsClosed → isClosed)

variable {α β}

def rev (dual : PreDualityOperator α β) : PreDualityOperator β α where
  toFun := dual.rev'
  monotone' := dual.rev'.monotone'
  rev' := dual
  antitone' := dual.antitoneRev'
  antitoneRev' := dual.antitone'
  subset' := dual.subsetRev'
  subsetRev' := dual.subset'
  triple' := dual.tripleRev'
  tripleRev' := dual.triple'

lemma to_GaloisConnection (dual : PreDualityOperator α β)
    : GaloisConnection (toDual ∘ dual) (dual.rev ∘ ofDual) := by
  intro S T
  simp
  sorry
  -- nth_rw 1 [← toDual_ofDual T]
  -- rw [toDual_le_toDual]
  -- constructor
  -- · intro h
  --   unfold dual' at *
  --   have h := dual_antitone (p := p.flip) h
  --   have h := dual_antitone (p := p) h
  --   rw [dual_dual_flip_dual] at h
  --   have h := dual_antitone (p := p.flip) h
  --   rw [dual_flip_dual_dual_flip] at h
  --   exact le_trans subset_dual_dual h
  -- · sorry

def from_GaloisConnection (l : α → β) (u : β → α) (con : GaloisConnection u l) :
    PreDualityOperator α β := sorry

lemma antitone (dual : PreDualityOperator α β) {s t : α} (hst : s ≤ t) :
    dual s ≤ dual t := dual.antitone' s t hst

lemma subset_eq (dual : PreDualityOperator α β) (s : α) : s ≤ dual.rev (dual s) := dual.subset' s

lemma subset_eq_rev (dual : PreDualityOperator α β) (s : β) : s ≤ dual (dual.rev s)
    := dual.rev.subset' s

@[simp] lemma triple (dual : PreDualityOperator α β) (s : α) :
    dual (dual.rev (dual s)) = dual s := dual.triple' s

@[simp] lemma triple_rev (dual : PreDualityOperator α β) (s : β) :
    dual.rev (dual (dual.rev s)) = dual.rev s := dual.rev.triple' s

@[simp] lemma rev_rev (dual : PreDualityOperator α β) : dual.rev.rev = dual := rfl

abbrev closure (dual : PreDualityOperator α β) (s : α) := dual.rev (dual s)

def closureOp (dual : PreDualityOperator α β) : ClosureOperator α where
  toFun := dual.closure
  monotone' _ _ hCD := dual.rev.antitone (dual.antitone hCD)
  le_closure' := dual.subset_eq
  idempotent' s := dual.triple_rev (dual s)

abbrev IsClosed (dual : PreDualityOperator α β) (s : α) := dual.closureOp.IsClosed s

section PartialOrder

variable (α β : Type*)
variable [PartialOrder α] [Preorder β]

abbrev Closeds (dual : PreDualityOperator α β) := dual.closureOp.Closeds

end PartialOrder

end PreDualityOperator

structure DualityOperator extends α →o β where
  rev' : β →o α
  /-- A duality operator is weakly order reversing. -/
  antitone'    : ∀ s t, s ≤ t → toFun s ≤ toFun t
  antitoneRev' : ∀ s t, s ≤ t → rev' s ≤ rev' t
  equal'       : ∀ s, rev' (toFun s) = s
  equalRev'    : ∀ s, toFun (rev' s) = s
  triple'      : ∀ s, toFun (rev' (toFun s)) = toFun s
  tripleRev'   : ∀ s, rev' (toFun (rev' s)) = rev' s

namespace DualityOperator

variable {α β}

instance : FunLike (DualityOperator α β) α β where
  coe c := c.1
  coe_injective' := sorry
    --by rintro ⟨⟩ ⟨⟩ h; obtain rfl := DFunLike.ext' h; congr with x; simp_all

instance : OrderHomClass (DualityOperator α β) α β where
  map_rel f _ _ h := f.mono h

def rev (dual : DualityOperator α β) : DualityOperator β α where
  toFun := dual.rev'
  monotone' := dual.rev'.monotone'
  rev' := dual
  antitone' := dual.antitoneRev'
  antitoneRev' := dual.antitone'
  equal' := dual.equalRev'
  equalRev' := dual.equal'
  triple' := dual.tripleRev'
  tripleRev' := dual.triple'

instance : Coe (DualityOperator α β) (PreDualityOperator α β) := ⟨fun dual => {
  toFun := dual.toFun
  monotone' := dual.monotone'
  rev' := dual.rev'
  antitone' := dual.antitone'
  antitoneRev' := dual.antitoneRev'
  subset' s := by rw [dual.equal']
  subsetRev' s := by rw [dual.equalRev']
  triple' := dual.triple'
  tripleRev' := dual.tripleRev'
}⟩

lemma antitone (dual : DualityOperator α β) {s t : α} (hst : s ≤ t) :
    dual s ≤ dual t := dual.antitone' s t hst

@[simp] lemma equal_eq (dual : DualityOperator α β) (s : α) :
    dual.rev (dual s) = s := dual.equal' s

@[simp] lemma equal_eq_rev (dual : DualityOperator α β) (s : β) : dual (dual.rev s) = s
    := dual.rev.equal' s

@[simp] lemma triple (dual : DualityOperator α β) (s : α) :
    dual (dual.rev (dual s)) = dual s := dual.triple' s

@[simp] lemma triple_rev (dual : DualityOperator α β) (s : β) :
    dual.rev (dual (dual.rev s)) = dual.rev s := dual.rev.triple' s

@[simp] lemma rev_rev (dual : DualityOperator α β) : dual.rev.rev = dual := rfl

end DualityOperator

namespace PreDualityOperator

section PartialOrder

variable (α β : Type*)
variable [PartialOrder α] [PartialOrder β]

def closeOp (dual : PreDualityOperator α β) :
    DualityOperator (dual.Closeds) (dual.rev.Closeds) where
  toFun s := dual.rev.closureOp.toCloseds (dual.toFun s)
  monotone' := sorry
  rev' := sorry
  antitone' := sorry
  antitoneRev' := sorry
  equal' := sorry
  equalRev' := sorry
  triple' := sorry
  tripleRev' := sorry

end PartialOrder

end PreDualityOperator
