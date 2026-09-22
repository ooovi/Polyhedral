/-
Copyright (c) 2025 Olivia Röhrig, Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Olivia Röhrig, Martin Winter
-/
module

public import Mathlib.Order.Grade
public import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Finite.Face.Basic
public import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.VPolyhedral.Lattice

/-! This file proves that the face lattice of an FG cone is graded.

Main declaration:
* `GradeOrder ℕ (Face C)`

TODO: either provide a version of the grading, or define the grading canonically, using
`finsalrank` instead of `finrank`. Maybe this is easier if we already proved that submodules
form a graded lattice (is this already done?).
-/

@[expose] public section

open Module Submodule

namespace PointedCone.FG

variable {R M : Type*}

section DivisionRing

variable [DivisionRing R] [LinearOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M]

variable {C : PointedCone R M}

/-- The finite rank of a face is a strictly monotone map. -/
lemma finrank_strictMono (hCfg : C.FG) : StrictMono (Face.finrank : Face C → _) := by
  intro G F hFG
  have := (Submodule.fg_iff_finiteDimensional _).mp (FG.span_fg <| F.isFaceOf.fg hCfg)
  apply finrank_lt_finrank_of_lt (lt_of_le_of_ne ?_ ?_)
  · exact span_mono (R := R) hFG.le
  · intro h
    rw [Face.coe_toPointedCone] at h
    have : G.toSubmodule < F.toSubmodule := gt_iff_lt.mp hFG
    rw [← IsFaceOf.inf_span F.isFaceOf, ← IsFaceOf.inf_span G.isFaceOf] at this
    simp [h] at this

/-- Two faces that cover each other in the face lattice have a rank difference of one. -/
lemma finrank_add_one (hCfg : C.FG) {F G : Face C} (hFG : F ⋖ G) :
    G.finrank = F.finrank + 1 := by
  obtain ⟨hfg, hc⟩ := hFG
  -- suffices to show quotient has rank 1
  have hgfg := quot_fg (G.isFaceOf.fg hCfg) F.span
  convert
    finrank_eq_finrank_add_finrank_quot_span (FG.span_fg (G.isFaceOf.fg hCfg)) hfg.le
    -- G/F has a ray
  have FfG : (F : PointedCone R M).IsFaceOf G := (F.isFaceOf.isFaceOf_iff_le G.isFaceOf).mpr hfg.le
  have : ¬(G : PointedCone R M) ≤ F.span := by
    simpa [Face.le_span_iff_le] using not_le_of_gt hfg
  obtain ⟨v, hv0, hvray⟩ :=
    FG.exists_ray hgfg ((PointedCone.quot_eq_bot_iff _ _).not.mpr this) FfG.quot_salient
  set ray : Face (quot G.toSubmodule F.span) := ⟨hull R {v}, hvray⟩
  -- pull ray back to get face of G with F < H
  let H := ray.fiberFace (F := ⟨_, FfG⟩)
  have : F < H := by
    apply lt_of_le_of_ne (ray.le_fiber (F := ⟨_, FfG⟩))
    intro ha
    have ugh : hull R {v} = ⊥ := (Face.fiberFace_eq_iff _).mp ha
    have : v ∈ hull R {v} := Submodule.mem_span_singleton_self v
    rw [ugh] at this
    exact hv0 <| (AddOpposite.op_eq_zero_iff v).mp (congrArg AddOpposite.op this)
  -- must be G = H because of covering
  simp only [← eq_of_le_of_not_lt H.isFaceOf.le <| hc this]
  rw [← PointedCone.finrank_one_of_ray (R := R) hv0]
  congr; ext x; constructor
  · intro hx
    obtain ⟨x', hx', rfl⟩ := hvray.le hx
    exact ⟨x', ⟨hx', hx⟩, rfl⟩
  · rintro ⟨_, ⟨_, hhx'⟩, rfl⟩
    exact mem_toConvexCone.mp hhx'

lemma finrank_covBy (hCfg : C.FG) {F G : Face C} (hFG : F ⋖ G) :
    F.finrank ⋖ G.finrank := by
  obtain ⟨hfg, hc⟩ := hFG
  refine ⟨finrank_strictMono hCfg hfg, ?_⟩
  suffices G.finrank = F.finrank + 1 by omega
  exact (FG.finrank_add_one hCfg ⟨hfg, hc⟩)

lemma covBy_iff_finrank_covBy_of_le (hCfg : C.FG) {F G : Face C} (hfg : F ≤ G) :
    F ⋖ G ↔ F.finrank ⋖ G.finrank := by
  refine ⟨finrank_covBy hCfg, fun h ↦ ⟨?_, ?_⟩⟩
  · exact lt_of_le_of_ne hfg <| fun a => ne_of_lt h.1 (congrArg finrank (by simpa))
  · exact fun H hH hah => h.2 (finrank_strictMono hCfg hH) (finrank_strictMono hCfg hah)

-- TODO: make this use `salfinrank`.
/-- The face lattice of a finitely generated cone is graded by face dimension. -/
@[reducible] noncomputable def gradeOrder_finrank {C : PointedCone R M} (hCfg : C.FG) :
    GradeOrder ℕ (Face C) where
  grade F := F.finrank
  grade_strictMono := finrank_strictMono hCfg
  covBy_grade := fun {_ _} hFG => finrank_covBy hCfg hFG

/- NOTE: the proof below is AI generated. It can likely be much improved once sufficient API is
available for transporting face lattices along quotients. Currently there is a proof of
`Face (C ⧸ ⊥) ≃o Face C`, but the rest of the repository works with `C.salientQuot` instead of
`C ⧸ ⊥`, and translating between them needs work. -/
/-- The face lattice of a polyhedral cone is graded by the dimensions of the corresponding faces
of its salient quotient. -/
noncomputable instance _root_.VPolyhedralCone.gradeOrder_finrank {C : VPolyhedralCone R M} :
    GradeOrder ℕ (Face (C : PointedCone R M)) := by
  let e := Face.salientQuot_orderIso (C : PointedCone R M)
  have hspan : (⊥ : Face (C : PointedCone R M)).span =
      PointedCone.lineal (C : PointedCone R M) := by
    change Submodule.span R (((⊥ : Face (C : PointedCone R M)) : PointedCone R M) : Set M) = _
    rw [Face.lineal_eq_bot]
    exact PointedCone.span_inf_neg_eq_lineal _
  have hfg : (Face.quot (C := (C : PointedCone R M)) ⊥).FG := by
    change (PointedCone.quot (C : PointedCone R M) (⊥ : Face (C : PointedCone R M)).span).FG
    rw [hspan]
    exact C.isVPolyhedral.salientQuot_fg
  letI := PointedCone.FG.gradeOrder_finrank hfg
  exact GradeOrder.liftRight e.symm e.symm.strictMono fun _ _ ↦
    (apply_covBy_apply_iff e.symm).mpr

end DivisionRing

end FG

end PointedCone
