/-
Copyright (c) 2019 Olivia Röhrig, Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Olivia Röhrig, Martin Winter
-/

import Mathlib.Geometry.Convex.ConvexSpace.AffineSpace

import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Hull
import Polyhedral.Mathlib.LinearAlgebra.AffineSpace.Defs

import Polyhedral.Mathlib.Algebra.Group.Pointwise.SetLike.Scalar

/-! ... -/

variable {ι R K X Y : Type*}

namespace Convexity

/-- A bundled convex set. -/
structure ConvexSet (R X : Type*) [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]
    [ConvexSpace R X] where
  /-- The carrier set. -/
  carrier : Set X
  isConvexSet : IsConvexSet R carrier

namespace ConvexSet

public section Semiring

variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R] [ConvexSpace R X]

variable {K K₁ K₂ : ConvexSet R X}

instance : SetLike (ConvexSet R X) X where
  coe := ConvexSet.carrier
  coe_injective' K₁ K₂ _ := by cases K₁; cases K₂; congr

variable (K) in
@[simp] lemma carrier_eq_coe : K.carrier = K := rfl

@[ext] theorem ext (h : ∀ x, x ∈ K₁ ↔ x ∈ K₂) : K₁ = K₂ := SetLike.ext h

@[simp] theorem mem_mk {s h x} : x ∈ (⟨s, h⟩ : ConvexSet R X) ↔ x ∈ s := .rfl

@[simp] theorem mk_eq {s h} : (⟨s, h⟩ : ConvexSet R X) = s := by ext; simp

/- # LE -/

instance : PartialOrder (ConvexSet R X) := .ofSetLike ..

/- # Bot -/

instance : Bot (ConvexSet R X) where
  bot := ⟨∅, IsConvexSet.empty⟩

instance : Inhabited (ConvexSet R X) := ⟨⊥⟩

instance : IsConcreteBot (ConvexSet R X) X := ⟨rfl⟩

instance : OrderBot (ConvexSet R X) := .ofSetLike ..

/- # Top -/

instance : Top (ConvexSet R X) where
  top := ⟨Set.univ, IsConvexSet.univ⟩

instance : IsConcreteTop (ConvexSet R X) X := ⟨rfl⟩

instance : OrderTop (ConvexSet R X) := .ofSetLike ..

/- # Singleton -/

instance : Singleton X (ConvexSet R X) where
  singleton x := ⟨{x}, .singleton⟩

instance : IsConcreteSingleton (ConvexSet R X) X := ⟨fun _ => rfl⟩

/- # Min -/

/-- The infimum of two convex sets is a convex set. -/
instance : Min (ConvexSet R X) where
  min K₁ K₂ := ⟨_, K₁.isConvexSet.inter K₂.isConvexSet⟩

instance : IsConcreteMin (ConvexSet R X) X := ⟨fun _ _ => rfl⟩

instance : SemilatticeInf (ConvexSet R X) := .ofSetLike ..

/- # InfSet -/

instance : InfSet (ConvexSet R X) where
  sInf S := ⟨⋂ a ∈ S, a, by
    apply IsConvexSet.sInter
    rintro _ ⟨a, rfl⟩
    apply IsConvexSet.sInter
    rintro _ ⟨_, rfl⟩
    exact a.2⟩

instance : IsConcreteInfSet (ConvexSet R X) X := ⟨fun _ => rfl⟩

instance : CompleteSemilatticeInf (ConvexSet R X) := .ofSetLike ..

/- # Max -/

variable (R) in
/-- The convex hull of a set `s`, bundled as a `ConvexSet`. -/
def convexHull (s : Set X) : ConvexSet R X := ⟨Convexity.convexHull R s, .convexHull⟩

instance : Max (ConvexSet R X) where
  max K₁ K₂ := convexHull R (K₁ ∪ K₂)

lemma coe_sup_eq_convexHull_union : (K₁ ⊔ K₂).carrier = Convexity.convexHull R (K₁ ∪ K₂) := by rfl

instance instSemilatticeSup : SemilatticeSup (ConvexSet R X) where
  sup := max
  le_sup_left _ _ _ hs := by
    apply subset_convexHull_self
    simp [hs]
  le_sup_right _ _ _ hs := by
    apply subset_convexHull_self
    simp [hs]
  sup_le K₁ K₂ K₃ h₁₂ h₂₃ x hx := by
    rw [mem_mk, coe_sup_eq_convexHull_union, mem_convexHull_iff] at hx
    refine hx K₃ ?_ K₃.isConvexSet
    simp [h₂₃, h₁₂]

/- # SupSet -/

instance : SupSet (ConvexSet R X) where
  sSup S := convexHull R (⋃ s ∈ S, s)

instance : CompleteSemilatticeSup (ConvexSet R X) where
  isLUB_sSup K := by
    constructor <;> intro L hL
    · intro l hl
      exact (Set.subset_iUnion₂_of_subset _ hL fun ⦃_⦄ a ↦ a).trans subset_convexHull_self hl
    · simp only [sSup, convexHull, Convexity.convexHull,
        ClosureOperator.ofCompletePred_apply, Set.le_eq_subset, Set.iInf_eq_iInter]
      intro x xm
      simp only [mem_mk, Set.mem_iInter, Subtype.forall, Set.iUnion_subset_iff, and_imp] at xm
      exact xm _ hL L.isConvexSet

/- # Complet Lattice -/

instance : CompleteLattice (ConvexSet R X) where

end Semiring

section Pointwise

section Semiring

variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [ConvexSpace R X] [AddCommGroup X] [Module R X] [IsModuleConvexSpace R X]

open Pointwise

/-! ### Zero -/

section Zero

instance : Zero (ConvexSet R X) where
  zero := ⟨0, .singleton⟩

instance : IsConcreteZero (ConvexSet R X) X := ⟨rfl⟩

end Zero

/-! ### Negation -/

section Neg

instance : Neg (ConvexSet R X) where
  neg K := ⟨_, K.isConvexSet.neg⟩

instance : IsConcreteNeg (ConvexSet R X) X := ⟨fun _ => rfl⟩

instance : InvolutiveNeg (ConvexSet R X) := .ofSetLike ..

end Neg

end Semiring

section Ring

variable [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [ConvexSpace R X] [AddCommGroup X] [Module R X] [IsModuleConvexSpace R X]

/-! ### Minkowski addition -/

instance : Add (ConvexSet R X) where
  add K₁ K₂ := ⟨_, K₁.isConvexSet.add K₂.isConvexSet⟩

instance : IsConcreteAdd (ConvexSet R X) X := ⟨fun _ _ => rfl⟩

/-! ### Scalar multiplication -/

instance : SMul R (ConvexSet R X) where
  smul r K := ⟨_, K.isConvexSet.smul r⟩

instance : IsConcreteSMulSet R (ConvexSet R X) X := ⟨fun _ _ => rfl⟩

section AddTorsor

variable [AddTorsor X Y]

noncomputable local instance : ConvexSpace R Y := AddTorsor.toConvexSpace

instance : VAdd (ConvexSet R X) (ConvexSet R Y) where
  vadd K₁ K₂ := ⟨_, K₁.isConvexSet.vadd K₂.isConvexSet⟩

instance : IsConcreteVAdd (ConvexSet R X) X (ConvexSet R Y) Y := ⟨fun _ _ => rfl⟩

end AddTorsor

end Ring

end Pointwise

end ConvexSet


namespace ConvexSet

variable {R A : Type*}
variable [PartialOrder R] [Ring R] [IsStrictOrderedRing R]
variable {V : Type*} [AddCommGroup V] [Module R V]
variable [AddTorsor V A]

attribute [local instance] AddTorsor.toConvexSpace

variable {C : ConvexSet R A}

-- Affine.rank needs ring

noncomputable abbrev rank (C : ConvexSet R A) := Affine.rank R (C : Set A)

noncomputable abbrev finrank (C : ConvexSet R A) := Affine.finrank R (C : Set A)

end ConvexSet

end Convexity
