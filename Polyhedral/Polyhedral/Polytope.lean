import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Finite.Face.Grade
import Polyhedral.Mathlib.LinearAlgebra.AffineSpace.Homogenization
import Polyhedral.Mathlib.Order.Hom.Basic
import Polyhedral.Mathlib.LinearAlgebra.ConvexSpace.AffineSpace
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs

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

namespace Polytope

theorem carrier_convex {F : Polytope R A} : IsConvex R F.carrier := by
  rw [F.FG.choose_spec]; exact isConvex_convexHull

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
    exact fun i ↦ ⟨⟨∅, ⟨Set.empty_subset ∅, isConvex_empty⟩⟩, Set.notMem_empty i⟩
}⟩

section Homogenization

open Affine Homogenization

variable {V : Type*} [AddCommGroup V] [Module R V]
variable [AddTorsor V A]
variable {W : Type*} [AddCommGroup W] [Module R W]

variable [hom : Homogenization R A W]

/-- Dehomogenizing a finitely generated salient cone yields a polytope. -/
theorem FG.dehomogenize_isPolytope {C : PointedCone R W} (h : C.FG) (hsal : C.Salient) :
    IsPolytope R (hom.dehomogenize A C : Set A) := by
  choose g fg using h
  use g.preimage _ hom.inj.injOn
  rw [Finset.convexHull_eq (g.preimage _ hom.inj.injOn)]
  simp [dehomogenize, IsConvex.preimage, ← fg]
  sorry

end Homogenization

section DivisionRing

open Affine

variable {R A : Type*}
variable [LinearOrder R] [Field R] [IsStrictOrderedRing R]
variable {V : Type*} [AddCommGroup V] [Module R V]
variable [AddTorsor V A]
variable {W : Type*} [AddCommGroup W] [Module R W]

variable [hom : Homogenization R A W]

variable {C : ConvexSet R A}

/-- The homogenization cone of a polytope is finitely generated. -/
theorem IsPolytope.homgenize_FG (hCfg : IsPolytope R (C : Set A)) :
    (Homogenization.homogenize W C).FG := by
  obtain ⟨t, ht⟩ := hCfg
  have : C = ⟨convexHull R t, isConvex_convexHull⟩ := SetLike.ext' ht
  rw [congrArg hom.homogenize this]
  use t.map ⟨_, hom.inj⟩
  simp only [Finset.coe_map, Function.Embedding.coeFn_mk, Homogenization.homogenize,
    PointedCone.hull, ConvexSet.coe_carrier]
  rw [← AffineMap.convexHull hom.inj t]
  exact PointedCone.hull_convexHull_eq_hull R (hom.embed '' t)

variable (W) in
/-- The face lattice of a polytope is graded by homogenization cone face dimension. -/
@[reducible]
private noncomputable def faceHomogenizationGradeOrder
    (hCfg : IsPolytope R (C : Set A)) : GradeOrder ℕ C.Face := by
  have : PointedCone.FG (hom.homogenize W C) := IsPolytope.homgenize_FG hCfg
  letI := PointedCone.FG.gradeOrder_finrank this
  -- we just lift the grading we have for PointedCone.Face already
  refine GradeOrder.liftRight (β := (hom.homogenize W C).Face) _
    Homogenization.Face.homogenizationIso.strictMono ?_
  exact fun x y ↦ (OrderIso.covBy_iff_covBy _).mp

variable (W) in
lemma hom_grade_eq_finrank_add_one (hCfg : IsPolytope R (C : Set A)) (F : C.Face) :
    have : PointedCone.FG (hom.homogenize W C) := IsPolytope.homgenize_FG hCfg
    letI := PointedCone.FG.gradeOrder_finrank this
    this.grade (Homogenization.Face.homogenizationIso.toFun F) = F.finrank + 1 := by
  simp [GradeOrder.grade]
  sorry

variable (W) in
lemma finrank_eq_hom_grade_sub_one (hCfg : IsPolytope R (C : Set A)) (F : C.Face) :
    have : PointedCone.FG (hom.homogenize W C) := IsPolytope.homgenize_FG hCfg
    letI := PointedCone.FG.gradeOrder_finrank this
    F.finrank = this.grade (Homogenization.Face.homogenizationIso.toFun F) - 1 := by
  exact Nat.eq_sub_of_add_eq <| (hom_grade_eq_finrank_add_one W hCfg F).symm

open PointedCone

lemma PointedCone.bot_linSpan : (⊥ : PointedCone R W).linSpan = ⊥ := by
  simp [linSpan]

lemma PointedCone.mem_hull_of_mem {s : Set W} {x} (h : x ∈ s) : x ∈ hull R s :=
  Submodule.mem_span_of_mem h

open PointedCone Homogenization in
/-- omogenizin the face of a polytope yields a face of the homogenization cone that has finrank of
at least one. -/
lemma one_le_hom_face_finrank (hCfg : IsPolytope R (C : Set A)) (F : C.Face) (hF : F ≠ ⊥) :
    1 ≤ (Homogenization.Face.homogenizationIso (W := W) F).finrank := by
  simp only [Face.homogenizationIso, RelIso.coe_fn_mk, Equiv.coe_fn_mk]
  haveI : Module.Finite R (Homogenization.homogenize W F.toConvexSet).linSpan := by
    sorry
  apply Submodule.one_le_finrank_iff.mpr
  simp only [ne_eq, Submodule.span_eq_bot, SetLike.mem_coe, Face.mem_coe, not_forall]
  obtain ⟨x, hx⟩ := ConvexSet.Face.nonempty_of_ne_bot hF
  use hom.embed x
  simp only [embed_ne_zero, not_false_eq_true, homogenize, ConvexSet.coe_carrier, exists_prop,
    and_true]
  exact PointedCone.mem_hull_of_mem (Set.mem_image_of_mem hom.embed hx)

open AffineSubspace in
/-- The face lattice of a polytope is graded by the face finrank. -/
noncomputable def finrank_gradeOrder (hCfg : IsPolytope R (C : Set A)) : GradeOrder ℕ C.Face where
  grade F := F.finrank
  grade_strictMono := by
    intro a b hab
    by_cases habot : a = ⊥
    · simp only [habot, Bot.bot, ConvexSet.Face.finrank, ConvexSet.finrank,
      ConvexSet.coe_carrier] at hab ⊢
      unfold Affine.finrank
      rw [AffineSubspace.span_empty, AffineSubspace.direction_bot]
      simp [Module.finrank_eq_zero_of_subsingleton, direction]
      -- apply Module.finrank_pos_iff.mpr
      sorry
    have ha := finrank_eq_hom_grade_sub_one W hCfg a
    have hb := finrank_eq_hom_grade_sub_one W hCfg b
    simp only [ha, Equiv.toFun_as_coe, RelIso.coe_fn_toEquiv, hb, gt_iff_lt]
    apply Nat.sub_lt_sub_right ?_ ((faceHomogenizationGradeOrder W hCfg).grade_strictMono hab)
    simp only [GradeOrder.grade, grade, Face.finrank, Function.comp_apply]
    exact one_le_hom_face_finrank hCfg _ habot
  covBy_grade := by
    intro a b hcov
    by_cases habot : a = ⊥
    · subst habot
      simp [ConvexSet.Face.finrank, ConvexSet.finrank] at hcov ⊢
      sorry
    have := (faceHomogenizationGradeOrder W hCfg).covBy_grade hcov
    have ha := finrank_eq_hom_grade_sub_one W hCfg a
    have hb := finrank_eq_hom_grade_sub_one W hCfg b
    simp only [GradeOrder.grade, grade, Function.comp_apply, Nat.covBy_iff_add_one_eq, ha,
      Equiv.toFun_as_coe, RelIso.coe_fn_toEquiv, hb] at this ⊢
    rw [← this]
    simpa using Nat.sub_add_cancel (one_le_hom_face_finrank hCfg _ habot)


end DivisionRing

end Polytope
