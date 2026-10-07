/-
Copyright (c) 2026 Olivia Röhrig, Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Olivia Röhrig, Mara Gruß, Valentina Taylor Cerra, Martin Winter
-/
module

public import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Face.Basic
public import Polyhedral.Mathlib.Geometry.Convex.Set
import Polyhedral.Mathlib.Data.SetLike.IsConcrete

-- import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Lattice

/-! This file defines faces of convex sets.

TODO: align this API with `Face` for cones.
-/

public section

variable {R M : Type*}

namespace Convexity

section Semiring

variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [ConvexSpace R M]

namespace IsConvexSet

/-- A face of a convex set `P`. Represents the face lattice of `P`. -/
@[ext]
structure Face {p : Set M} (P : IsConvexSet R p) where
  carrier : Set M
  isConvexSet : IsConvexSet R carrier
  isFaceOf : IsFaceOf R carrier p

attribute [coe] Face.carrier

namespace Face

variable {p : Set M} {P : IsConvexSet R p}

instance : SetLike (Face P) M where
  coe F := F.carrier
  coe_injective a b h := by
    cases a; cases b; congr

instance : CoeOut (Face P) (Set M) := ⟨carrier⟩

@[simp] theorem carrier_eq_coe {F : Face P} : F.carrier = F := by rfl

@[simp] theorem mem_coe {F : Face P} (x : M) : x ∈ F.carrier ↔ x ∈ F := .rfl

@[simp] theorem mem_mk {s c h x} : x ∈ (⟨s, c, h⟩ : Face P) ↔ x ∈ s := .rfl

@[simp] theorem mk_eq {s c h} : (⟨s, c, h⟩ : Face P) = s := by ext; simp

instance : PartialOrder (Face P) := .ofSetLike ..

instance : OrderBot (Face P) where
  bot := ⟨_, IsConvexSet.empty, IsFaceOf.empty⟩
  bot_le _ _ := by simp

lemma nonempty_of_ne_bot {F : Face P} (h : F ≠ ⊥) : (F : Set M).Nonempty := by
  rw [Set.nonempty_iff_ne_empty]
  intro heq
  apply h
  ext
  simp [← SetLike.mem_coe, heq, Bot.bot]

instance : OrderTop (Face P) where
  top := ⟨_, P, IsFaceOf.refl⟩
  le_top F := F.isFaceOf.le

instance : Inhabited (Face P) := ⟨⊤⟩

theorem toConvexSet_le {F : Face P} : F.carrier ≤ p := F.isFaceOf.le

@[simp]
theorem toConvexSet_le_toConvexSet {F₁ F₂ : Face P} :
    F₁.carrier ≤ F₂.carrier ↔ F₁ ≤ F₂ := .rfl

@[simp] theorem toConvexSet_bot : ((⊥ : Face P) : Set M) = ∅ := rfl

@[simp] theorem toConvexSet_top : ((⊤ : Face P) : Set M) = p := rfl

/-! ### Infimum, supremum and lattice -/

/-- The infimum of two faces `F₁`, `F₂` of `P` is the intersection of `F₁` and `F₂`. -/
instance : Min (Face P) where
  min F₁ F₂ := ⟨_, F₁.isConvexSet.inter F₂.isConvexSet, F₁.isFaceOf.inf_left F₂.isFaceOf⟩

instance : InfSet (Face P) where
  sInf S :=
    { carrier := p ⊓ sInf {s.1 | s ∈ S}
      isConvexSet := P.inter (IsConvexSet.sInter fun s ⟨s, hs, sh⟩ ↦ sh ▸ s.isConvexSet)
      isFaceOf := IsFaceOf.sInf (by rintro _ ⟨s, hs, rfl⟩; exact s.isFaceOf) }

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
      simp only [carrier_eq_coe, Set.sInf_eq_sInter]
      exact fun _ xs ↦ xs f (by simpa)
    · simp only [sInf, carrier_eq_coe, Set.mem_ofPred_eq, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, SetLike.mem_coe, Set.inf_eq_inter]
      simpa [LE.le] using fun x a ↦ ⟨f.isFaceOf.le a, fun i hi ↦ (mem_coe x).mp (fS hi a)⟩

instance : CompleteLattice (Face P) where
  top := ⟨_, P, .refl⟩
  le_top _ := toConvexSet_le
  __ := completeLatticeOfCompleteSemilatticeInf _

end IsConvexSet.Face

end Semiring

end Convexity
