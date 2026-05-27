import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Lattice

section

open Convexity

variable {R A : Type*}
variable [PartialOrder R] [Semiring R] [IsStrictOrderedRing R]
variable [ConvexSpace R A]

variable (R) in
/-- A set is a polytope if it is the convex hull of finitely many points. -/
def IsPolytope (s : Set A) : Prop := ∃ t : Finset A, s = Convexity.convexHull R t

variable (R A) in
structure Polytope where
  carrier : Set A
  FG : IsPolytope R carrier

namespace Polytope

theorem carrier_convex {F : Polytope R A} : IsConvexSet R F.carrier := by
  rw [F.FG.choose_spec]; exact IsConvexSet.convexHull

instance : Coe (Polytope R A) (ConvexSet R A) where
  coe s := ⟨s.carrier, carrier_convex⟩

instance : SetLike (Polytope R A) A where
  coe P := P.carrier
  coe_injective' P Q h := by cases P; cases Q; congr

variable (P : Polytope R A) in
@[simp] lemma carrier_eq_coe : P.carrier = P := rfl

variable (P : Polytope R A) in
@[simp] lemma carrier_eq_coe' : P = P.carrier := rfl

variable (P : Polytope R A) in
@[simp] theorem mem_coe (x : A) : x ∈ P.carrier ↔ x ∈ P := .rfl

instance : PartialOrder (Polytope R A) := .ofSetLike (Polytope R A) A

instance : Bot (Polytope R A) := ⟨{
  carrier := ∅
  FG := by
    use ∅
    simp only [Convexity.convexHull, Finset.coe_empty, ClosureOperator.ofCompletePred_apply,
      Set.le_eq_subset, Set.iInf_eq_iInter, Eq.symm]; symm
    rw [Set.iInter_eq_empty_iff]
    exact fun i ↦ ⟨⟨∅, ⟨Set.empty_subset ∅, IsConvexSet.empty⟩⟩, Set.notMem_empty i⟩
}⟩

end Polytope

end
