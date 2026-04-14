import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Finite.Face.Basic

open Module

namespace PointedCone

namespace FG

section DivisionRing

variable {R : Type*} [DivisionRing R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {C : PointedCone R M}

open Submodule in
lemma finrank_strictMono (hCfg : C.FG) : StrictMono (fun F : Face C => F.finrank) := by
  intro G F hFG
  haveI := (Submodule.fg_iff_finiteDimensional _).mp (FG.span_fg <| F.isFaceOf.fg hCfg)
  apply finrank_lt_finrank_of_lt (lt_of_le_of_ne ?_ ?_)
  · exact span_mono (R := R) hFG.le
  · intro h
    have : G.toSubmodule < F.toSubmodule := gt_iff_lt.mp hFG
    rw [← IsFaceOf.inf_span F.isFaceOf, ← IsFaceOf.inf_span G.isFaceOf] at this
    simp [h] at this

lemma finrank_add_one (hCfg : C.FG) {F G : Face C} (hFG : F ⋖ G) : G.finrank = F.finrank + 1 := by
  obtain ⟨hfg, hc⟩ := hFG
  -- suffices to show quotient has rank 1
  have hgfg := quot_fg (G.isFaceOf.fg hCfg) F.span
  convert
    finrank_eq_finrank_add_finrank_quot_linSpan (FG.span_fg (G.isFaceOf.fg hCfg)) hfg.le
    -- G/F has a ray
  have FfG : (F : PointedCone R M).IsFaceOf G := (G.isFaceOf.isFaceOf_iff.mpr ⟨hfg.le, F.isFaceOf⟩)
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

lemma finrank_covBy (hCfg : C.FG)
    {F G : Face C} (hFG : F ⋖ G) :
    F.finrank ⋖ G.finrank := by
  obtain ⟨hfg, hc⟩ := hFG
  refine ⟨finrank_strictMono hCfg hfg, ?_⟩
  suffices G.finrank = F.finrank + 1 by omega
  exact (FG.finrank_add_one hCfg ⟨hfg, hc⟩)

lemma covBy_iff_finrank_covBy_of_le (hCfg : C.FG)
    {F G : Face C} (hfg : F ≤ G) : F ⋖ G ↔
    F.finrank ⋖ G.finrank := by
  refine ⟨finrank_covBy hCfg, ?_⟩
  intro h
  constructor
  · exact lt_of_le_of_ne hfg <| fun a => ne_of_lt h.1 (congrArg finrank (by simpa))
  · exact fun H hH hah => h.2 (finrank_strictMono hCfg hH) (finrank_strictMono hCfg hah)

/-- The face lattice of a finitely generated cone is graded by face dimension. -/
noncomputable instance gradeOrder_finrank {C : PointedCone R M}
    (hCfg : C.FG) : GradeOrder ℕ (Face C) where
  grade F := F.finrank
  grade_strictMono := finrank_strictMono hCfg
  covBy_grade := fun {_ _} hFG => finrank_covBy hCfg hFG

end DivisionRing

end FG

-- My impression is someone should first implement the grading for the lattice of submodules.
-- (if not already done). This here is then a simple derivate thereof.

-- lemma salFinrank_strictMono (C : PointedCone R M) : -- (hC : C.IsPolyhedral) :
--     StrictMono fun F : Face C => salFinrank (F : PointedCone R M) := by
--   sorry

-- lemma salFinrank_covBy {C : PointedCone R M} (hC : C.IsPolyhedral) (F G : Face C) (hFG : F ⋖ G) :
--     salFinrank (F : PointedCone R M) ⋖ salFinrank (G : PointedCone R M) := by
--   sorry

-- noncomputable instance {C : PointedCone R M} (hC : C.IsPolyhedral) : GradeOrder ℕ (Face C) where
--   grade F := salFinrank (F : PointedCone R M)
--   grade_strictMono := salFinrank_strictMono C
--   covBy_grade := salFinrank_covBy hC


end PointedCone
