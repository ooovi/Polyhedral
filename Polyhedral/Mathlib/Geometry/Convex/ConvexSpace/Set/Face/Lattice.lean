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

instance : Inhabited (Face P) := ⟨⊤⟩

theorem toConvexSet_le {F : Face P} : F ≤ P := F.isFaceOf.le

@[simp]
theorem toConvexSet_le_toConvexSet {F₁ F₂ : Face P} :
    F₁.toConvexSet ≤ F₂.toConvexSet ↔ F₁ ≤ F₂ := .rfl

@[simp]
theorem toConvexSet_lt_toConvexSet {F₁ F₂ : Face P} :
    F₁.toConvexSet < F₂.toConvexSet ↔ F₁ < F₂ := .rfl

@[simp]
theorem mem_toConvexSet {F : Face P} (x : M) : x ∈ F.toConvexSet ↔ x ∈ F := .rfl

/-! ### Infimum, supremum and lattice -/

/-- The infimum of two faces `F₁`, `F₂` of `C` is the intersection of the cones `F₁` and `F₂`. -/
instance : Min (Face P) where
  min F₁ F₂ := ⟨F₁ ⊓ F₂, F₁.isFaceOf.inf_left F₂.isFaceOf⟩

protected theorem IsFaceOf.sInf (F : Set (ConvexSet R M)) (h : ∀ f ∈ F, f.IsFaceOf P) :
    (P ⊓ sInf F).IsFaceOf P where
  le _ sm := sm.1
  left_mem_of_mem_openSegment := by
    simp only [SetLike.mem_min, SetLike.mem_sInf, and_imp]
    intro x hx y hy z hz h₁ h₂
    simpa [hx] using fun F Fs ↦ (h F Fs).left_mem_of_mem_openSegment hx hy (by grind) h₂

instance : InfSet (Face P) where
  sInf S :=
    { toConvexSet := P ⊓ sInf {s.1 | s ∈ S}
      isFaceOf := IsFaceOf.sInf _ (fun _ ⟨s, _, hs2⟩ ↦ hs2 ▸ s.isFaceOf) }

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
    · simp only [sInf, ConvexSet.carrier_eq_coe, Set.sInter_image, Set.mem_ofPred_eq,
        Set.iInter_exists, Set.biInter_and', Set.iInter_iInter_eq_right]
      simpa [LE.le] using fun x a ↦ ⟨f.2.1 a, fun i hi ↦ (mem_coe x).mp (fS hi a)⟩

instance : CompleteLattice (Face P) where
  top := ⟨P, .refl _⟩
  le_top _ := toConvexSet_le
  __ := completeLatticeOfCompleteSemilatticeInf _

end ConvexSet.Face

end Semiring

end Convexity
