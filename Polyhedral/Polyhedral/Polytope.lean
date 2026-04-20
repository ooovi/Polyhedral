import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Hull
import Polyhedral.Mathlib.LinearAlgebra.ConvexSpace
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.LinearAlgebra.ConvexSpace.AffineSpace

import Polyhedral.Mathlib.LinearAlgebra.AffineSpace.Homogenization

import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Face.Lattice

section Polytope

open ConvexSpace

variable {R A : Type*}
variable [PartialOrder R] [Ring R] [IsStrictOrderedRing R]
variable [ConvexSpace R A]

variable (R) in
/-- A set is a polytope if it is the convex hull of finitely many points. -/
def IsPolytope (s : Set A) : Prop := ∃ t : Finset A, s = ConvexSpace.convexHull R t

variable (R A) in
structure Polytope where
  carrier : Set A
  FG : IsPolytope R carrier

theorem carrier_convex {F : Polytope R A} : Convex R F.carrier := by
  rw [F.FG.choose_spec]; exact convexHull_convex R

instance : Coe (Polytope R A) (ConvexSet R A) where
  coe s := ⟨s.carrier, carrier_convex⟩

instance : SetLike (Polytope R A) A where
  coe P := P.carrier
  coe_injective' := sorry

instance : PartialOrder (Polytope R A) := .ofSetLike (Polytope R A) A

instance : Bot (Polytope R A) := ⟨{
  carrier := ∅
  FG := by
    use ∅
    simp only [ConvexSpace.convexHull, Finset.coe_empty, ClosureOperator.ofCompletePred_apply,
      Set.le_eq_subset, Set.iInf_eq_iInter, Eq.symm]; symm
    rw [Set.iInter_eq_empty_iff]
    exact fun i ↦ ⟨⟨∅, ⟨Set.empty_subset ∅, empty_convex _⟩⟩, Set.notMem_empty i⟩
}⟩

end Polytope
