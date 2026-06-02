/-
Copyright (c) 2019 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter, Olivia Röhrig
-/

import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Lattice
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.Basic
import Polyhedral.Mathlib.Algebra.Group.Pointwise.SetLike.Scalar

/-! ... -/

namespace Convexity

open ConvexSpace

variable {R X Y V : Type*}

section Semiring

variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [ConvexSpace R X]

variable (R X) in
structure Polytope where
  carrier : Set X
  isPolytope : IsPolytope R carrier

end Semiring

namespace Polytope

section Semiring

variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [ConvexSpace R X]

instance : SetLike (Polytope R X) X where
  coe := Polytope.carrier
  coe_injective' P₁ P₂ _ := by cases P₁; cases P₂; congr

variable {P P₁ P₂ : Polytope R X}

variable (P) in
@[simp] lemma carrier_eq_coe : P.carrier = P := rfl

@[ext] theorem ext (h : ∀ x, x ∈ P₁ ↔ x ∈ P₂) : P₁ = P₂ := SetLike.ext h

@[simp] theorem mem_mk {s h x} : x ∈ (⟨s, h⟩ : Polytope R X) ↔ x ∈ s := .rfl

@[simp] theorem mk_eq {s h} : (⟨s, h⟩ : Polytope R X) = s := by ext; simp

instance : Coe (Polytope R X) (ConvexSet R X) where
  coe P := ⟨P, P.isPolytope.isConvexSet⟩

/- # LE -/

instance : PartialOrder (Polytope R X) := .ofSetLike ..

/- # Bot -/

instance : Bot (Polytope R X) where
  bot := ⟨∅, IsPolytope.empty R X⟩

instance : Inhabited (Polytope R X) := ⟨⊥⟩

instance : IsConcreteBot (Polytope R X) X := ⟨rfl⟩

instance : OrderBot (Polytope R X) := .ofSetLike ..

/- # Singleton -/

instance : Singleton X (Polytope R X) where
  singleton x := ⟨{x}, .singleton R x⟩

instance : IsConcreteSingleton (Polytope R X) X := ⟨fun _ => rfl⟩

/- # Max -/

variable (R) in
/-- The convex hull of a `Finset s` as a `Polytope`. -/
def convexHull (s : Finset X) : Polytope R X :=
  ⟨_, IsPolytope.convexHull_finite R s.finite_toSet⟩

instance : Max (Polytope R X) where
  max P₁ P₂ := ⟨_, P₁.isPolytope.convexHull_union P₂.isPolytope⟩

lemma coe_sup_eq_convexHull_union :
  ((P₁ ⊔ P₂ : Polytope R X) : Set X) = Convexity.convexHull R (P₁ ∪ P₂) := rfl

instance : SemilatticeSup (Polytope R X) where
  sup := max
  le_sup_left _ _ := by
    rw [← SetLike.coe_subset_coe, coe_sup_eq_convexHull_union]
    exact subset_trans Set.subset_union_left subset_convexHull_self
  le_sup_right _ _ := by
    rw [← SetLike.coe_subset_coe, coe_sup_eq_convexHull_union]
    exact subset_trans Set.subset_union_right subset_convexHull_self
  sup_le a b c ha hb := by
    rw [← SetLike.coe_subset_coe, coe_sup_eq_convexHull_union]
    have : IsConvexSet R (c : Set X) := c.isPolytope.isConvexSet
    rw [← convexHull_eq_self.mpr this]
    apply convexHull_mono
    simp_all only [SetLike.coe_subset_coe, Set.union_subset_iff, and_self]

end Semiring

section Field

variable [Field R] [PartialOrder R] [IsStrictOrderedRing R]
variable [ConvexSpace R X]
variable [AddCommGroup V] [Module R V]
variable [AddTorsor V X]

attribute [local instance] AddTorsor.toConvexSpace

/- # Min -/

/-- The infimum of two convex sets is a convex set. -/
instance : Min (Polytope R X) where
  min P₁ P₂ := ⟨_, P₁.isPolytope.inter P₂.isPolytope⟩

instance : IsConcreteMin (Polytope R X) X := ⟨fun _ _ => rfl⟩

instance : SemilatticeInf (Polytope R X) := .ofSetLike ..

instance : Lattice (Polytope R X) where

end Field

section Pointwise

section Semiring

variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [ConvexSpace R X] [AddCommGroup X] [Module R X] [IsModuleConvexSpace R X]

open Pointwise

/-! ### Zero -/

instance : Zero (Polytope R X) where
  zero := ⟨0, .singleton ..⟩

instance : IsConcreteZero (Polytope R X) X := ⟨rfl⟩

/-! ### Negation -/

instance : Neg (Polytope R X) where
  neg K := ⟨_, K.isPolytope.neg⟩

instance : IsConcreteNeg (Polytope R X) X := ⟨fun _ => rfl⟩

instance : InvolutiveNeg (ConvexSet R X) := .ofSetLike ..

end Semiring

section Ring

variable [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [ConvexSpace R X] [AddCommGroup X] [Module R X] [IsModuleConvexSpace R X]

/-! ### Minkowski addition -/

instance : Add (Polytope R X) where
  add P₁ P₂ := ⟨_, P₁.isPolytope.add P₂.isPolytope⟩

instance : IsConcreteAdd (Polytope R X) X := ⟨fun _ _ => rfl⟩

instance : Sub (Polytope R X) where
  sub P₁ P₂ := ⟨_, P₁.isPolytope.sub P₂.isPolytope⟩

instance : IsConcreteSub (Polytope R X) X := ⟨fun _ _ => rfl⟩

instance : SubtractionMonoid (Polytope R X) := .ofSetLike ..

/-! ### Scalar multiplication -/

instance : SMul R (Polytope R X) where
  smul r P := ⟨_, P.isPolytope.smul r⟩

instance : IsConcreteSMulSet R (Polytope R X) X := ⟨fun _ _ => rfl⟩

instance : DistribMulAction R (Polytope R X) := .ofSetLike ..

noncomputable section VAdd

variable [AddTorsor X Y]

noncomputable local instance : ConvexSpace R Y := AddTorsor.toConvexSpace

instance : VAdd X (Polytope R Y) where
  vadd v P := ⟨_, P.isPolytope.translate v⟩

instance : IsConcreteVAddSet X (Polytope R Y) Y := ⟨fun _ _ => rfl⟩

instance : AddAction X (Polytope R Y) := .ofSetLike_set ..

instance : VAdd (Polytope R X) (Polytope R Y) where
  vadd K₁ K₂ := ⟨_, K₁.isPolytope.vadd K₂.isPolytope⟩

instance : IsConcreteVAdd (Polytope R X) X (Polytope R Y) Y := ⟨fun _ _ => rfl⟩

instance : AddAction (Polytope R X) (Polytope R Y) := .ofSetLike ..

end VAdd

end Ring

end Pointwise

end Polytope

end Convexity
