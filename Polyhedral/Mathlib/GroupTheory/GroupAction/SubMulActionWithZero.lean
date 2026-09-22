/-
Copyright (c) 2026 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/
module

public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Polyhedral.Mathlib.Data.SetLike.IsConcrete

import Mathlib.Algebra.GroupWithZero.Action.Defs

/-!

# Sets invariant to a `MulActionWithZero`

In this file we define `SubMulAction₀ R M`: a subset of a type `M`
which contains `0` and is closed under scalar multiplication by `R`.

This is the zero-containing analogue of `SubMulAction`. We do not duplicate
the generic `SetLike` scalar-action API from `SubMulAction`; instead, we register
`ZeroMemClass` and `SMulMemClass`, so that the existing generic subtype
instances apply.

## Main definitions

* `SubMulAction₀` - a zero-containing subset closed under scalar multiplication.
* `SubMulAction₀.toSubMulAction` - forget that the subset contains zero.
* `SubMulAction₀.ofSubMulAction` - add a proof that a `SubMulAction` contains zero.
* `SubMulAction₀.toSMulZeroClass` - the subtype inherits `SMulZeroClass`.
* `SubMulAction₀.toSMulWithZero` - the subtype inherits `SMulWithZero`.
* `SubMulAction₀.toMulActionWithZero` - the subtype inherits `MulActionWithZero`.

## Tags

submodule, multiplicative action, zero
-/

@[expose] public section

@[expose] public section

universe u v

variable {R : Type u} {M : Type v}

/- TODO: perhaps `SubMulAction₀` should extend `SubMulAction`.
  Note that the closures are different, but this might not be a blocker. One can define
  `SubMulAction₀.closure s := insert 0 (SubMulAction.closure s)`
-/

/-- A `SubMulAction₀` is a set containing `0` and closed under scalar multiplication. -/
structure SubMulAction₀ (R : Type u) (M : Type v) [Zero M] [SMul R M] : Type v where
  /-- The underlying set of a `SubMulAction₀`. -/
  carrier : Set M
  /-- The carrier set contains zero. -/
  zero_mem' : (0 : M) ∈ carrier
  /-- The carrier set is closed under scalar multiplication. -/
  smul_mem' : ∀ (c : R) {x : M}, x ∈ carrier → c • x ∈ carrier

alias SMulSet := SubMulAction₀

namespace SubMulAction₀

section Zero_SMul

variable [Zero M] [SMul R M]

instance : SetLike (SubMulAction₀ R M) M :=
  ⟨SubMulAction₀.carrier, fun p q h => by cases p; cases q; congr⟩

instance : PartialOrder (SubMulAction₀ R M) :=
  .ofSetLike (SubMulAction₀ R M) M

instance : ZeroMemClass (SubMulAction₀ R M) M where
  zero_mem p := p.zero_mem'

instance : SMulMemClass (SubMulAction₀ R M) R M where
  smul_mem := smul_mem' _

@[simp]
theorem mem_carrier {p : SubMulAction₀ R M} {x : M} :
    x ∈ p.carrier ↔ x ∈ (p : Set M) :=
  Iff.rfl

@[simp] theorem mem_mk {s h₁ h₂ x} :
    x ∈ (⟨s, h₁, h₂⟩ : SubMulAction₀ R M) ↔ x ∈ s := .rfl

@[simp] theorem mk_eq {s h₁ h₂} : (⟨s, h₁, h₂⟩ :
    SubMulAction₀ R M) = s := by ext; simp

@[ext]
theorem ext {p q : SubMulAction₀ R M} (h : ∀ x, x ∈ p ↔ x ∈ q) : p = q :=
  SetLike.ext h

/-- A `SubMulAction₀`, forgetting that it contains zero. -/
protected def toSubMulAction (p : SubMulAction₀ R M) : SubMulAction R M where
  carrier := p
  smul_mem' := p.smul_mem'

instance : Coe (SubMulAction₀ R M) (SubMulAction R M) :=
  ⟨SubMulAction₀.toSubMulAction⟩

@[simp]
theorem coe_toSubMulAction (p : SubMulAction₀ R M) :
    (p.toSubMulAction : Set M) = (p : Set M) :=
  rfl

@[simp]
theorem coe_coe (p : SubMulAction₀ R M) :
    ((p : SubMulAction R M) : Set M) = (p : Set M) :=
  rfl

@[simp]
theorem mem_toSubMulAction {p : SubMulAction₀ R M} {x : M} :
    x ∈ p.toSubMulAction ↔ x ∈ p :=
  Iff.rfl

/-- Promote a `SubMulAction` to a `SubMulAction₀` by providing `0 ∈ p`. -/
def ofSubMulAction (p : SubMulAction R M) (h0 : (0 : M) ∈ p) :
    SubMulAction₀ R M where
  carrier := p
  zero_mem' := h0
  smul_mem' := fun c _ hx => p.smul_mem c hx

@[simp]
theorem coe_ofSubMulAction (p : SubMulAction R M) (h0 : (0 : M) ∈ p) :
    (ofSubMulAction p h0 : Set M) = p :=
  rfl

/-- Copy of a `SubMulAction₀` with a new `carrier` equal to the old one.
Useful to fix definitional equalities. -/
protected def copy (p : SubMulAction₀ R M) (s : Set M) (hs : s = ↑p) :
    SubMulAction₀ R M where
  carrier := s
  zero_mem' := hs.symm ▸ p.zero_mem'
  smul_mem' := hs.symm ▸ p.smul_mem'

@[simp]
theorem coe_copy (p : SubMulAction₀ R M) (s : Set M) (hs : s = ↑p) :
    (p.copy s hs : Set M) = s :=
  rfl

theorem copy_eq (p : SubMulAction₀ R M) (s : Set M) (hs : s = ↑p) :
    p.copy s hs = p :=
  SetLike.coe_injective hs

@[simp]
theorem zero_mem {p : SubMulAction₀ R M} : (0 : M) ∈ p :=
  p.zero_mem'

theorem smul_mem (p : SubMulAction₀ R M) (r : R) {x : M} (hx : x ∈ p) :
    r • x ∈ p :=
  p.smul_mem' r hx

instance (p : SubMulAction₀ R M) : Inhabited p := ⟨0⟩

@[simp, norm_cast]
theorem val_zero (p : SubMulAction₀ R M) : ((0 : p) : M) = 0 :=
  rfl

@[simp, norm_cast]
theorem val_smul {p : SubMulAction₀ R M} (r : R) (x : p) :
    ((r • x : p) : M) = r • (x : M) :=
  rfl

instance : OrderTop (SubMulAction₀ R M) where
  top := {
    carrier := Set.univ
    zero_mem' := by simp
    smul_mem' := by simp }
  le_top _ _ := by simp

@[simp]
theorem mem_top {x : M} : x ∈ (⊤ : SubMulAction₀ R M) :=
  trivial

theorem le_top (p : SubMulAction₀ R M) : p ≤ ⊤ := by
  intro x hx
  trivial

instance : Max (SubMulAction₀ R M) where
  max p q :=
    { carrier := p ∪ q
      zero_mem' := Or.inl p.zero_mem
      smul_mem' := by
        rintro c x (hx | hx)
        · exact Or.inl (p.smul_mem c hx)
        · exact Or.inr (q.smul_mem c hx) }

instance : IsConcreteMax (SubMulAction₀ R M) M := ⟨fun _ _ => rfl⟩

instance : SemilatticeSup (SubMulAction₀ R M) := .ofSetLike ..

@[simp]
theorem mem_sup {p q : SubMulAction₀ R M} {x : M} :
    x ∈ p ⊔ q ↔ x ∈ p ∨ x ∈ q :=
  Iff.rfl

instance : Min (SubMulAction₀ R M) where
  min p q :=
    { carrier := p ∩ q
      zero_mem' := ⟨p.zero_mem, q.zero_mem⟩
      smul_mem' c _ hx := ⟨p.smul_mem c hx.1, q.smul_mem c hx.2⟩ }

instance : IsConcreteMin (SubMulAction₀ R M) M := ⟨fun _ _ => rfl⟩

instance : SemilatticeInf (SubMulAction₀ R M) := .ofSetLike ..

@[simp]
theorem mem_inf {p q : SubMulAction₀ R M} {x : M} :
    x ∈ p ⊓ q ↔ x ∈ p ∧ x ∈ q :=
  Iff.rfl

instance : Lattice (SubMulAction₀ R M) where

instance : InfSet (SubMulAction₀ R M) where
  sInf S := {
    carrier := ⋂₀ (SetLike.coe '' S)
    zero_mem' := by simp
    smul_mem' := by simpa using fun c x hx p hp => p.smul_mem c (hx p hp) }

instance : IsConcreteInfSet (SubMulAction₀ R M) M := ⟨fun _ => rfl⟩

@[simp]
theorem mem_sInf {S : Set (SubMulAction₀ R M)} {x : M} :
    x ∈ sInf S ↔ ∀ p ∈ S, x ∈ p := SetLike.mem_sInf _ _

instance : CompleteSemilatticeInf (SubMulAction₀ R M) := .ofSetLike ..

end Zero_SMul

section SMulZeroClass

variable [Zero M] [SMulZeroClass R M]

instance : Bot (SubMulAction₀ R M) := ⟨{
  carrier := {0}
  zero_mem' := by simp
  smul_mem' c x hx := by
    rw [Set.mem_singleton_iff] at hx ⊢
    rw [hx, smul_zero]
  }⟩

instance : IsConcreteBot₀ (SubMulAction₀ R M) M where
  coe_bot₀' := rfl
  zero_mem' _ := zero_mem

instance : OrderBot (SubMulAction₀ R M) := .ofSetLike₀

theorem mem_bot {x : M} :
    x ∈ (⊥ : SubMulAction₀ R M) ↔ x = 0 :=
  SetLike.mem_bot_iff_zero

instance : SupSet (SubMulAction₀ R M) where
  sSup S := {
    carrier := insert 0 (⋃ s ∈ S, s)
    zero_mem' := Or.inl rfl
    smul_mem' := by simpa using fun c x s hs hx => .inr ⟨s, hs, smul_mem s c hx⟩ }

instance : IsConcreteSupSet₀ (SubMulAction₀ R M) M := ⟨fun _ => rfl⟩

instance : CompleteSemilatticeSup (SubMulAction₀ R M) := .ofSetLike₀ ..

@[simp]
theorem mem_sSup {S : Set (SubMulAction₀ R M)} {x : M} :
    x ∈ sSup S ↔ x = 0 ∨ ∃ p ∈ S, x ∈ p := SetLike.mem_sSup₀ _ _

instance : CompleteLattice (SubMulAction₀ R M) where

end SMulZeroClass

instance (priority := 75) toSMulZeroClass [Zero M] [SMulZeroClass R M]
    (p : SubMulAction₀ R M) : SMulZeroClass R p where
  smul r x := ⟨_, p.smul_mem r x.2⟩
  smul_zero r := Subtype.ext (smul_zero r)

instance (priority := 75) toSMulWithZero [Zero R] [Zero M] [SMulWithZero R M]
    (p : SubMulAction₀ R M) : SMulWithZero R p where
  smul_zero r := Subtype.ext (smul_zero r)
  zero_smul x := Subtype.ext (zero_smul R (x : M))

instance (priority := 75) toMulActionWithZero [MonoidWithZero R] [Zero M]
    [MulActionWithZero R M] (p : SubMulAction₀ R M) : MulActionWithZero R p where
  one_smul x := Subtype.ext (one_smul R (x : M))
  mul_smul r s x := Subtype.ext (mul_smul r s (x : M))
  smul_zero r := Subtype.ext (smul_zero r)
  zero_smul x := Subtype.ext (zero_smul R (x : M))

section OfClass

variable {S R M : Type*} [Zero M] [SMul R M] [SetLike S M]
variable [ZeroMemClass S M] [SMulMemClass S R M]

/-- The actual `SubMulAction₀` obtained from any set-like type whose
members contain `0` and are closed under scalar multiplication. -/
@[coe] def ofClass (s : S) : SubMulAction₀ R M where
  carrier := s
  zero_mem' := ZeroMemClass.zero_mem s
  smul_mem' := fun r _ hx => SMulMemClass.smul_mem r hx

@[simp]
theorem coe_ofClass (s : S) :
    (ofClass (R := R) s : Set M) = s :=
  rfl

@[simp]
theorem mem_ofClass (s : S) {x : M} :
    x ∈ ofClass (R := R) s ↔ x ∈ s :=
  Iff.rfl

end OfClass

section GroupWithZero

variable [GroupWithZero R] [Zero M] [MulActionWithZero R M]
variable {s t : Set M} {x : M}

lemma mem_of_smul_mem {s : SubMulAction₀ R M} {r : R} (hr : r ≠ 0)
    (hx : r • x ∈ s) : x ∈ s := by
  simpa [smul_smul, inv_mul_cancel₀ hr] using smul_mem s r⁻¹ hx

lemma smul_mem_iff_mem {s : SubMulAction₀ R M} {r : R} (hr : r ≠ 0) :
    r • x ∈ s ↔ x ∈ s where
  mp := mem_of_smul_mem hr
  mpr := smul_mem s r

end GroupWithZero

end SubMulAction₀
