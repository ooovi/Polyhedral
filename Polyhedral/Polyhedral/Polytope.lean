import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Finite.Face.Grade
import Polyhedral.Mathlib.LinearAlgebra.AffineSpace.Homogenization
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.AffineSpace
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
import Mathlib.Data.Finset.Lattice.Basic
import Polyhedral.Mathlib.LinearAlgebra.AffineSpace.Defs


section Polytope

open Convexity

variable {R A : Type*}
variable [PartialOrder R] [Ring R] [IsStrictOrderedRing R]
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
  coe_injective' := sorry

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

section Homogenization

open Affine Homogenization

variable {V : Type*} [AddCommGroup V] [Module R V]
variable [AddTorsor V A]
variable {W : Type*} [AddCommGroup W] [Module R W]
variable [IsModuleConvexSpace R W]

variable [hom : Homogenization R A W]

/-- Dehomogenizing a finitely generated salient cone yields a polytope. -/
theorem FG.dehomogenize_isPolytope {C : PointedCone R W} (h : C.FG) (hsal : C.Salient) :
    IsPolytope R (hom.dehomogenize A C : Set A) := by
  choose g fg using h
  use g.preimage _ hom.inj.injOn
  -- rw [Finset.convexHull_eq (g.preimage _ hom.inj.injOn)]
  simp [dehomogenize, ← fg]
  sorry

end Homogenization

section DivisionRing

open Affine

variable {R A : Type*}
variable [LinearOrder R] [Field R] [IsStrictOrderedRing R]
variable {V : Type*} [AddCommGroup V] [Module R V]
variable [AddTorsor V A]
variable {W : Type*} [AddCommGroup W] [Module R W]
variable [IsModuleConvexSpace R W]

variable [hom : Homogenization R A W]

variable {C : ConvexSet R A}

/-- The homogenization cone of a polytope is finitely generated. -/
theorem _root_.IsPolytope.homogenize_FG (hCfg : IsPolytope R (C : Set A)) :
    (Homogenization.homogenize W C).FG := by
  obtain ⟨t, ht⟩ := hCfg
  have : C = ⟨convexHull R t, IsConvexSet.convexHull⟩ := SetLike.ext' ht
  rw [congrArg hom.homogenize this]
  use t.map ⟨_, hom.inj⟩
  simp only [Finset.coe_map, Function.Embedding.coeFn_mk, Homogenization.homogenize,
    PointedCone.hull, ConvexSet.mk_eq]
  rw [hom.isAffineMap.image_convexHull t]
  exact PointedCone.hull_convexHull_eq_hull (hom.embed '' t)

variable (W) in
/-- The face lattice of a polytope is graded by homogenization cone face dimension. -/
@[reducible]
private noncomputable def faceHomogenizationGradeOrder
    (hCfg : IsPolytope R (C : Set A)) : GradeOrder ℕ C.Face := by
  have : PointedCone.FG (hom.homogenize W C) := IsPolytope.homogenize_FG hCfg
  letI := PointedCone.FG.gradeOrder_finrank this
  -- we just lift the grading we have for PointedCone.Face already
  refine GradeOrder.liftRight (β := (hom.homogenize W C).Face) _
    Homogenization.Face.homogenizationIso.strictMono ?_
  exact fun x y ↦ (apply_covBy_apply_iff _).mpr


end DivisionRing

end Polytope
