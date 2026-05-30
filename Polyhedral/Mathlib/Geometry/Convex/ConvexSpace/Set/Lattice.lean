/-
Copyright (c) 2019 Olivia Röhrig, Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Olivia Röhrig, Martin Winter
-/

import Mathlib.Geometry.Convex.ConvexSpace.AffineSpace

import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Hull
import Polyhedral.Mathlib.LinearAlgebra.AffineSpace.Defs

-- import Polyhedral.Mathlib.Data.Pointwise.SetLike.IsConcrete
-- import Polyhedral.Mathlib.Algebra.Group.Pointwise.SetLike.Basic
import Polyhedral.Mathlib.Algebra.Group.Pointwise.SetLike.Scalar

/-! ... -/

namespace Convexity

variable {ι R K X Y : Type*}

public section Semiring

variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R] [ConvexSpace R X]

variable (R X) in
/-- A bundled convex set. -/
structure ConvexSet where
  /-- The carrier set. -/
  carrier : Set X
  isConvexSet : IsConvexSet R carrier

variable {K K₁ K₂ : ConvexSet R X}

namespace ConvexSet

instance : SetLike (ConvexSet R X) X where
  coe := ConvexSet.carrier
  coe_injective' K₁ K₂ _ := by cases K₁; cases K₂; congr

variable (K) in
@[simp] lemma carrier_eq_coe : K.carrier = K := rfl

@[ext] theorem ext (h : ∀ x, x ∈ K₁ ↔ x ∈ K₂) : K₁ = K₂ := SetLike.ext h

@[simp] theorem mem_mk {s h x} : x ∈ (⟨s, h⟩ : ConvexSet R X) ↔ x ∈ s := .rfl

@[simp] theorem mk_eq {s h} : (⟨s, h⟩ : ConvexSet R X) = s := by ext; simp

/-!
### Complete lattice
-/

instance : PartialOrder (ConvexSet R X) := .ofSetLike ..

instance : Bot (ConvexSet R X) where
  bot := ⟨∅, IsConvexSet.empty⟩

instance : IsConcreteBot (ConvexSet R X) X := ⟨rfl⟩

instance : Top (ConvexSet R X) where
  top := ⟨Set.univ, IsConvexSet.univ⟩

instance : IsConcreteTop (ConvexSet R X) X := ⟨rfl⟩

instance : Inhabited (ConvexSet R X) := ⟨⊥⟩

/-- The infimum of two convex sets is a convex set. -/
instance : Min (ConvexSet R X) where
  min K₁ K₂ := ⟨_, K₁.isConvexSet.inter K₂.isConvexSet⟩

instance : IsConcreteMin (ConvexSet R X) X := ⟨fun _ _ => rfl⟩

instance : SemilatticeInf (ConvexSet R X) := .ofSetLike ..

protected lemma _root_.Convexity.IsConvexSet.biInter {S : Set (Set X)}
    (hS : ∀ s ∈ S, IsConvexSet R s) :
    IsConvexSet R (⋂ s ∈ S, s) := by simp +contextual [IsConvexSet, (hS _ _).sConvexComb_mem]

instance : InfSet (ConvexSet R X) where
  sInf S := ⟨⋂ a ∈ S, a, by
    apply IsConvexSet.sInter
    rintro _ ⟨a, rfl⟩
    apply IsConvexSet.sInter
    rintro _ ⟨_, rfl⟩
    exact a.2⟩

instance : IsConcreteInfSet (ConvexSet R X) X := ⟨fun _ => rfl⟩

instance : CompleteSemilatticeInf (ConvexSet R X) := .ofSetLike ..

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

instance : CompleteLattice (ConvexSet R X) where

section Pointwise

open Pointwise

/-! ### Negation -/

section Neg

variable [Neg X]

instance : Neg (ConvexSet R X) where
  neg K := ⟨_, K.isConvexSet.neg⟩

instance : IsConcreteNeg (ConvexSet R X) X := ⟨fun _ => rfl⟩

end Neg

/-! ### Minkowski addition -/

section Add

variable [Add X]

instance : Add (ConvexSet R X) where
  add K₁ K₂ := ⟨_, K₁.isConvexSet.add K₂.isConvexSet⟩

instance : IsConcreteAdd (ConvexSet R X) X := ⟨fun _ _ => rfl⟩

end Add

section VAdd

variable [ConvexSpace R Y] [VAdd X Y]

instance : VAdd (ConvexSet R X) (ConvexSet R Y) where
  vadd K₁ K₂ := ⟨_, K₁.isConvexSet.vadd K₂.isConvexSet⟩

instance : IsConcreteVAdd (ConvexSet R X) X (ConvexSet R Y) Y := ⟨fun _ _ => rfl⟩

end VAdd

end Pointwise

end ConvexSet

end Semiring


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
