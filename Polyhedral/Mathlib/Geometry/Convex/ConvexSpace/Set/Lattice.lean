/-
Copyright (c) 2019 Olivia Röhrig, Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Olivia Röhrig, Martin Winter
-/

import Mathlib.Geometry.Convex.ConvexSpace.AffineSpace

import Polyhedral.Mathlib.LinearAlgebra.AffineSpace.Defs

import Polyhedral.Mathlib.Algebra.Group.Pointwise.SetLike.Scalar
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Hull
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Pointwise

/-! This file defines bundled convex sets. -/

variable {ι R X Y : Type*}

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
  sInf S := ⟨⋂₀ (_ '' S), .sInter (by simpa using fun K _ => K.2)⟩

instance : IsConcreteInfSet (ConvexSet R X) X := ⟨fun _ => rfl⟩

instance : CompleteSemilatticeInf (ConvexSet R X) := .ofSetLike ..

/- TODO: We could define the `CompleteLattice` structure using
`completeLatticeOfCompleteSemilatticeInf` as shown below, and then just proof that the
resulting sup and sSup are propext to convex hulls.
But I don't know how important it is to have the definitional to convex hull. -/
-- instance : CompleteLattice (ConvexSet R X) := completeLatticeOfCompleteSemilatticeInf _

/- # Max -/

variable (R) in
/-- The convex hull of a set `s`, bundled as a `ConvexSet`. -/
def convexHull (s : Set X) : ConvexSet R X := ⟨Convexity.convexHull R s, .convexHull⟩

instance : Max (ConvexSet R X) where
  max K₁ K₂ := convexHull R (K₁ ∪ K₂)

lemma coe_sup : K₁ ⊔ K₂ = Convexity.convexHull R (K₁ ∪ K₂ : Set X) := rfl

instance instSemilatticeSup : SemilatticeSup (ConvexSet R X) where
  sup := max
  le_sup_left _ _ _ hs := by
    apply subset_convexHull_self
    simp [hs]
  le_sup_right _ _ _ hs := by
    apply subset_convexHull_self
    simp [hs]
  sup_le K₁ K₂ K₃ h₁₂ h₂₃ x hx := by
    rw [← SetLike.mem_coe, coe_sup, mem_convexHull_iff] at hx
    refine hx K₃ ?_ K₃.isConvexSet
    simp [h₂₃, h₁₂]

/- # SupSet -/

instance : SupSet (ConvexSet R X) where
  sSup S := convexHull R (⋃ K ∈ S, K)

lemma coe_sSup (S : Set (ConvexSet R X)) :
    sSup S = Convexity.convexHull R (⋃ K ∈ S, K : Set X) := rfl

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

/- # Map -/

variable [ConvexSpace R Y]

protected def map (C : ConvexSet R X) {f : X → Y} (hf : IsAffineMap R f) : ConvexSet R Y :=
  ⟨_, C.isConvexSet.image hf⟩

protected def comap (C : ConvexSet R Y) {f : X → Y} (hf : IsAffineMap R f) : ConvexSet R X :=
  ⟨_, C.isConvexSet.preimage hf⟩

end Semiring

section Pointwise

-- TODO: maybe pointwise instances should be scoped?
--  see also issue: https://github.com/ooovi/Polyhedral/issues/58#issue-4580609207

section Semiring

variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [ConvexSpace R X] [AddCommGroup X] [Module R X] [IsModuleConvexSpace R X]

open Pointwise

/-! ### Zero -/

instance : Zero (ConvexSet R X) where
  zero := ⟨0, .singleton⟩

instance : IsConcreteZero (ConvexSet R X) X := ⟨rfl⟩

/-! ### Negation -/

instance : Neg (ConvexSet R X) where
  neg K := ⟨_, K.isConvexSet.neg⟩

instance : IsConcreteNeg (ConvexSet R X) X := ⟨fun _ => rfl⟩

instance : InvolutiveNeg (ConvexSet R X) := .ofSetLike ..

end Semiring

section Ring

variable [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [ConvexSpace R X] [AddCommGroup X] [Module R X] [IsModuleConvexSpace R X]

/-! ### Minkowski addition / subtraction -/

instance : Add (ConvexSet R X) where
  add K₁ K₂ := ⟨_, K₁.isConvexSet.add K₂.isConvexSet⟩

instance : IsConcreteAdd (ConvexSet R X) X := ⟨fun _ _ => rfl⟩

instance : Sub (ConvexSet R X) where
  sub K₁ K₂ := ⟨_, K₁.isConvexSet.sub K₂.isConvexSet⟩

instance : IsConcreteSub (ConvexSet R X) X := ⟨fun _ _ => rfl⟩

instance : SubtractionCommMonoid (ConvexSet R X) := .ofSetLike ..

/-! ### Scalar multiplication -/

instance : SMul R (ConvexSet R X) where
  smul r K := ⟨_, K.isConvexSet.smul r⟩

instance : IsConcreteSMulSet R (ConvexSet R X) X := ⟨fun _ _ => rfl⟩

instance : DistribMulAction R (ConvexSet R X) := .ofSetLike ..

/- NOTE: Nonempty convex sets form a semi-module and hence have the structure of a convex
    space themselves. But we have no obvious way to exclude the empty set. -/

noncomputable section AddTorsor

variable [AddTorsor X Y]

local instance : ConvexSpace R Y := AddTorsor.toConvexSpace

instance : VAdd X (ConvexSet R Y) where
  vadd v K := ⟨_, K.isConvexSet.translate v⟩

instance : IsConcreteVAddSet X (ConvexSet R Y) Y := ⟨fun _ _ => rfl⟩

instance : AddAction X (ConvexSet R Y) := .ofSetLike_set ..

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
