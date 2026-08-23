/-
Copyright (c) 2026 Olivia Röhrig, Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Olivia Röhrig, Mara Gruß, Valentina Taylor Cerra, Martin Winter
-/

import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Lattice
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Face.Basic

/-! This file defines faces of convex sets.

TODO: align this API with `Face` for cones.
-/

variable {R M : Type*}

namespace Convexity

section Semiring

variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [ConvexSpace R M]

namespace ConvexSet

/- NOTE: maybe this should be defined on `Set` instead of `ConvexSet`. -/
/-- A face of a convex set `P`. Represents the face lattice of `P`. -/
structure Face (P : ConvexSet R M) extends toConvexSet : ConvexSet R M where
  isFaceOf : IsFaceOf toConvexSet P

attribute [coe] Face.toConvexSet

namespace Face

variable {P : ConvexSet R M}

instance : SetLike (Face P) M where
  coe F := F.toConvexSet.carrier
  coe_injective a b h := by
    cases a; cases b; congr; exact SetLike.coe_injective h

instance : CoeOut (Face P) (ConvexSet R M) := ⟨toConvexSet⟩

@[simp] theorem carrier_eq_coe {F : Face P} : F.carrier = F := by rfl

@[simp] theorem mem_coe {F : Face P} (x : M) : x ∈ F.carrier ↔ x ∈ F := .rfl

@[ext] theorem ext {F₁ F₂ : Face P} (h : ∀ x, x ∈ F₁ ↔ x ∈ F₂) : F₁ = F₂ := SetLike.ext h

@[simp] theorem coe_eq_toConvexSet_coe {F : Face P} : (F : Set M) = F.toConvexSet :=
  SetLike.ext'_iff.mp rfl

@[simp] theorem mem_mk {s h x} : x ∈ (⟨s, h⟩ : Face P) ↔ x ∈ s := .rfl

@[simp] theorem mk_eq {s h} : (⟨s, h⟩ : Face P) = s := by ext; simp

instance : PartialOrder (Face P) := .ofSetLike ..

instance : OrderBot (Face P) where
  bot := ⟨∅, IsFaceOf.empty⟩
  bot_le _ _ := by simp

lemma nonempty_of_ne_bot {F : Face P} (h : F ≠ ⊥) : (F : Set M).Nonempty := by
  rw [Set.nonempty_iff_ne_empty]
  intro heq
  apply h
  ext
  simp [← SetLike.mem_coe, heq, Bot.bot]

instance : OrderTop (Face P) where
  top := ⟨P, IsFaceOf.refl P⟩
  le_top F := F.isFaceOf.le

end ConvexSet.Face

end Semiring

end Convexity
