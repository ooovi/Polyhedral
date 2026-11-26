/-
Copyright (c) 2026 Valentina Taylor Cerra, Mara Gruß, Olivia Röhrig, Martin Winter.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valentina Taylor Cerra, Mara Gruß, Olivia Röhrig, Martin Winter
-/
module

public import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Face.Basic

import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Lattice

/-! This file defines faces of convex sets. Since reflexivity only holds for convex sets, this type
is defined on bundled `ConvexSet`. The use of bundled `ConvexSet` should be avoided where possible,
since it requires tedious coercions. If `Face` being defined on `ConvexSets` turns out to bring
this sort of trouble, we should consider other approaches (like requiring `Fact F.IsConvexSet` for
the `OrderTop`).

TODO: align this API with `Face` for cones.
-/

public section

variable {R X : Type*}

namespace Convexity

section Semiring

variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [ConvexSpace R X]

namespace ConvexSet

/-- A face of a convex set `P`. Represents the face lattice of `P`.

Note: this is defined on bundled `ConvexSet` since convexity is required for the lattice to have a
top element.
-/
structure Face (P : ConvexSet R X) extends toConvexSet : ConvexSet R X where
  isFaceOf : IsFaceOf R toConvexSet (P : Set X)

attribute [coe] Face.toConvexSet

namespace Face

variable {P : ConvexSet R X}

instance : SetLike (Face P) X where
  coe F := F.toConvexSet
  coe_injective a b h := by
    cases a; cases b; congr; exact SetLike.coe_injective h

instance : CoeOut (Face P) (ConvexSet R X) := ⟨toConvexSet⟩

@[simp] theorem carrier_eq_coe {F : Face P} : F.carrier = F := by rfl

@[simp] theorem mem_coe {F : Face P} (x : X) : x ∈ F.carrier ↔ x ∈ F := .rfl

@[ext] theorem ext {F₁ F₂ : Face P} (h : ∀ x, x ∈ F₁ ↔ x ∈ F₂) : F₁ = F₂ := SetLike.ext h

@[simp] theorem coe_eq_toConvexSet_coe {F : Face P} : (F : Set X) = F.toConvexSet :=
  SetLike.ext'_iff.mp rfl

@[simp] theorem mem_mk {s h x} : x ∈ (⟨s, h⟩ : Face P) ↔ x ∈ s := .rfl

@[simp] theorem mk_eq {s h} : (⟨s, h⟩ : Face P) = s := by ext; simp

instance : PartialOrder (Face P) := .ofSetLike ..

instance : OrderBot (Face P) where
  bot := ⟨∅, IsFaceOf.empty⟩
  bot_le _ _ := by simp

lemma nonempty_of_ne_bot {F : Face P} (h : F ≠ ⊥) : (F : Set X).Nonempty := by
  rw [← Set.ne_empty_iff_nonempty]
  intro heq
  apply h
  ext
  simp [← SetLike.mem_coe, heq, Bot.bot]

instance : OrderTop (Face P) where
  top := ⟨P, IsFaceOf.refl P.isConvexSet⟩
  le_top F := F.isFaceOf.le

instance : Inhabited (Face P) := ⟨⊤⟩

theorem toConvexSet_le {F : Face P} : F ≤ P := F.isFaceOf.le

@[simp]
theorem toConvexSet_le_toConvexSet {F₁ F₂ : Face P} :
    F₁.toConvexSet ≤ F₂.toConvexSet ↔ F₁ ≤ F₂ := .rfl

@[simp]
theorem toConvexSet_lt_toConvexSet {F₁ F₂ : Face P} :
    F₁.toConvexSet < F₂.toConvexSet ↔ F₁ < F₂ := .rfl

@[simp]
theorem mem_toConvexSet {F : Face P} (x : X) : x ∈ F.toConvexSet ↔ x ∈ F := .rfl

@[simp] theorem toConvexSet_bot : ((⊥ : Face P) : ConvexSet R X) = ∅ := rfl

@[simp] theorem toConvexSet_top : ((⊤ : Face P) : ConvexSet R X) = P := rfl

/-! ### Infimum, supremum and lattice -/

/-- The infimum of two faces `F₁`, `F₂` of `C` is the intersection of the cones `F₁` and `F₂`. -/
instance : Min (Face P) where
  min F₁ F₂ := ⟨F₁ ⊓ F₂, F₁.isFaceOf.inf_left F₂.isFaceOf⟩

instance : InfSet (Face P) where
  sInf S :=
    { toConvexSet := P ⊓ sInf {(s.toConvexSet) | s ∈ S}
      isFaceOf := IsFaceOf.sInf P.isConvexSet fun f hf ↦ by
        simp only [Set.mem_image, Set.mem_ofPred_eq, exists_exists_and_eq_and] at hf
        obtain ⟨a, ha, rfl⟩ := hf
        exact a.isFaceOf
     }

instance : SemilatticeInf (Face P) where
  inf := min
  inf_le_left _ _ _ xi := xi.1
  inf_le_right _ _ _ xi := xi.2
  le_inf _ _ _ h₁₂ h₂₃ _ xi := ⟨h₁₂ xi, h₂₃ xi⟩

instance : CompleteSemilatticeInf (Face P) where
  __ := instSemilatticeInf
  isGLB_sInf S := by
    constructor <;> intro f fS
    · rw [← toConvexSet_le_toConvexSet]
      refine inf_le_of_right_le ?_
      simpa [LE.le] using fun _ xs ↦ xs f fS
    · simp only [sInf, Set.sInter_image, Set.mem_ofPred_eq,
        Set.iInter_exists, Set.biInter_and', Set.iInter_iInter_eq_right]
      simpa [LE.le] using fun x a ↦ ⟨f.isFaceOf.le a, fun i hi ↦ (mem_coe x).mp (fS hi a)⟩

instance : CompleteLattice (Face P) where
  top := ⟨P, .refl P.isConvexSet⟩
  le_top _ := toConvexSet_le
  __ := completeLatticeOfCompleteSemilatticeInf _

end ConvexSet.Face

end Semiring

end Convexity
