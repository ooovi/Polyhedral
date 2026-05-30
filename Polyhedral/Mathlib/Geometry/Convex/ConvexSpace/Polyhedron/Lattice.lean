
import Mathlib.Algebra.AddTorsor.Defs

import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.Lattice
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polyhedron.Basic

namespace Convexity

open Convexity

-- NOTE: LinearOrder is needed because of the quotient definition of PointedCone.IsPolyhedral.
--  If we can weaken the definition, we can change back to PartialOrder.
variable {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R]
variable {V : Type*} [AddCommGroup V] [Module R V] -- [ConvexSpace R V] [IsModuleConvexSpace R V]
variable {A : Type*} [AddTorsor V A]

noncomputable local instance : ConvexSpace R A := AddTorsor.toConvexSpace

variable (R A) in
structure Polyhedron where
  carrier : Set A
  isPolyhedron : IsPolyhedron R carrier

namespace Polyhedron

instance : SetLike (Polyhedron R A) A where
  coe := Polyhedron.carrier
  coe_injective' P₁ P₂ _ := by cases P₁; cases P₂; congr

variable {P P₁ P₂ : Polyhedron R A}

variable (P) in
@[simp] lemma carrier_eq_coe : P.carrier = P := rfl

@[ext] theorem ext (h : ∀ A, A ∈ P₁ ↔ A ∈ P₂) : P₁ = P₂ := SetLike.ext h

@[simp] theorem mem_mk {s h x} : x ∈ (⟨s, h⟩ : Polyhedron R A) ↔ x ∈ s := .rfl

@[simp] theorem mk_eq {s h} : (⟨s, h⟩ : Polyhedron R A) = s := by ext; simp

instance : PartialOrder (Polyhedron R A) := .ofSetLike ..

@[coe] def toPolytope (P : Polytope R A) : Polyhedron R A := ⟨P, P.isPolytope.isPolyhedron⟩

instance : Coe (Polytope R A) (Polyhedron R A) := ⟨toPolytope⟩

section IsModuleConvexSpace

variable [ConvexSpace R V] [IsModuleConvexSpace R V]

@[coe] def toConvexSet (P : Polyhedron R A) : ConvexSet R A :=
  ⟨P, P.isPolyhedron.isConvexSet⟩

instance : Coe (Polyhedron R A) (ConvexSet R A) := ⟨toConvexSet⟩

end IsModuleConvexSpace

instance : Bot (Polyhedron R A) where
  bot := ⟨∅, IsPolyhedron.empty R A⟩

instance : IsConcreteBot (Polyhedron R A) A := ⟨rfl⟩

instance : Inhabited (Polyhedron R A) := ⟨⊥⟩

instance : Top (Polyhedron R A) where
  top := ⟨Set.univ, IsPolyhedron.univ R A⟩

instance : IsConcreteTop (Polyhedron R A) A := ⟨rfl⟩

end Polyhedron

end Convexity
