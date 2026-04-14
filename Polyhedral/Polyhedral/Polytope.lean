import Mathlib.Analysis.Convex.Basic
import Polyhedral.Mathlib.LinearAlgebra.ConvexSpace
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.LinearAlgebra.ConvexSpace.AffineSpace

import Polyhedral.Mathlib.LinearAlgebra.AffineSpace.Homogenization

import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Face.Lattice

open ConvexSpace

section Polytope

variable (R A : Type*)
variable [PartialOrder R] [Ring R] [IsStrictOrderedRing R]
variable {V : Type*} [AddCommGroup V] [Module R V]
variable [AddTorsor V A]

variable {A} in
/-- A set is a polytope if it is the convex hull of finitely many points. -/
def IsPolytope (s : Set A) : Prop := ∃ t : Finset A, s = ConvexSpace.convexHull R t

structure Polytope where
  carrier : Set A
  FG : IsPolytope R carrier

instance : SetLike (Polytope R A) A where
  coe s := s.carrier
  coe_injective' p q pq := by cases p ; cases q ; cases pq ; rfl

instance : PartialOrder (Polytope R A) := .ofSetLike (Polytope R A) A

namespace Polytope

variable {R A}

def IsFaceOf (F C : Polytope R A) := IsExtreme R C F.carrier

/-- A face of a polytope `P`. Represents the face lattice of `P`. -/
structure Face (P : Polytope R A) extends toPolytope : Polytope R A where
  isFaceOf : IsFaceOf toPolytope P

variable {P : Polytope R A}

instance : SetLike (Face P) A where
  coe F := F.toPolytope
  coe_injective' := SetLike.coe_injective.comp <| by rintro ⟨_, _⟩ ⟨_, _⟩ _; congr

instance : PartialOrder (Face P) := .ofSetLike (Face P) A

section Homogenization

variable {W : Type*} [AddCommGroup W] [Module R W] [hom : Affine.Homogenization R A W]

variable (P W) in
def homogenization := PointedCone.hull R (hom.embed '' P)

def homogenizationHom :
    OrderHom (Face P) (PointedCone.Face (P.homogenization W)) where
  toFun := sorry
  monotone' := sorry

end Homogenization

end Polytope

end Polytope
