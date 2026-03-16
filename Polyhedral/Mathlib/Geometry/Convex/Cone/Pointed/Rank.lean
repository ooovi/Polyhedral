import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Lineal

/-!
## Rank of Pointed Cones

This file collects rank constructions for pointed cones and the associated dimension formulas.
-/

namespace PointedCone

open Module Cardinal

/-! ### Basic rank notions -/

section Basic

variable {R M : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R] [AddCommMonoid M]
  [Module R M]

noncomputable abbrev rank (C : PointedCone R M) := Module.rank R C.linSpan

noncomputable abbrev finrank (C : PointedCone R M) := Module.finrank R C.linSpan

-- NOTE: this is not the same as Module.Finite or FG!
abbrev FinRank (C : PointedCone R M) := C.linSpan.FG

lemma finRank_of_fg {C : PointedCone R M} (hC : C.FG) : C.FinRank := hC.span

lemma zero_le_rank (C : PointedCone R M) : 0 ≤ C.rank := bot_le

lemma rank_mono {C F : PointedCone R M} (hF : F ≤ C) : F.rank ≤ C.rank :=
  Submodule.rank_mono <| Submodule.span_mono <| IsConcreteLE.coe_subset_coe'.mpr hF

end Basic

/-! ### Rank formulas for quotients -/

section Quotients

variable {R : Type*} [DivisionRing R] [PartialOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

private lemma ker_domRestrict_mkQ_linSpan (F G : PointedCone R M) :
    ((F.linSpan.mkQ).domRestrict G.linSpan).ker =
      Submodule.comap G.linSpan.subtype F.linSpan := by
  simp [LinearMap.ker_domRestrict, Submodule.ker_mkQ]

private lemma linSpan_quot_eq_range_domRestrict_mkQ (F G : PointedCone R M) :
    (G.quot F.linSpan).linSpan = ((F.linSpan.mkQ).domRestrict G.linSpan).range := by
  exact (linSpan_quot (C := G) (S := F.linSpan)).trans
    (LinearMap.range_domRestrict (K := G.linSpan) (f := F.linSpan.mkQ)).symm

/-- Dimension-addition for cone rank along a contained subcone. -/
lemma rank_eq_rank_add_rank_quot_linSpan {F G : PointedCone R M} (hFG : F ≤ G) :
    G.rank = F.rank + (G.quot F.linSpan).rank := by
  let f : G.linSpan →ₗ[R] (M ⧸ F.linSpan) := (F.linSpan.mkQ).domRestrict G.linSpan
  have hker : Module.rank R f.ker = Module.rank R F.linSpan := by
    rw [show f.ker = Submodule.comap G.linSpan.subtype F.linSpan by
      simpa [f] using ker_domRestrict_mkQ_linSpan F G]
    exact (Submodule.comapSubtypeEquivOfLe (Submodule.span_mono hFG)).rank_eq
  have hrange : (G.quot F.linSpan).linSpan = f.range := by
    change (G.quot F.linSpan).linSpan = ((F.linSpan.mkQ).domRestrict G.linSpan).range
    exact linSpan_quot_eq_range_domRestrict_mkQ F G
  have hmain : Module.rank R f.range + Module.rank R f.ker = Module.rank R G.linSpan :=
    LinearMap.rank_range_add_rank_ker f
  calc
    G.rank = Module.rank R G.linSpan := rfl
    _ = Module.rank R f.range + Module.rank R f.ker := hmain.symm
    _ = Module.rank R (G.quot F.linSpan).linSpan + Module.rank R F.linSpan := by
      rw [hrange, hker]
    _ = (G.quot F.linSpan).rank + F.rank := rfl
    _ = F.rank + (G.quot F.linSpan).rank := by simp [add_comm]

/-- Finite rank descends to a contained cone's span. -/
lemma finRank_of_le {F G : PointedCone R M} (hG : G.FinRank) (hFG : F ≤ G) :
    F.FinRank := by
  letI : Module.Finite R G.linSpan := Module.Finite.iff_fg.mpr hG
  exact Module.Finite.iff_fg.mp <|
    Module.Finite.of_injective (Submodule.inclusion (Submodule.span_mono hFG))
      (Submodule.inclusion_injective (Submodule.span_mono hFG))

/-- Finite rank descends to the span of a quotient cone. -/
lemma finRank_quot_linSpan {F G : PointedCone R M} (hG : G.FinRank) :
    (G.quot F.linSpan).FinRank := by
  change (G.quot F.linSpan).linSpan.FG
  simpa [PointedCone.linSpan_quot] using Submodule.FG.map (f := F.linSpan.mkQ) hG

/-- Finite rank descends to the span of a quotient by a submodule. -/
lemma finRank_quot_submodule (G : PointedCone R M) (S : Submodule R M) (hG : G.FinRank) :
    (G.quot S).FinRank := by
  change (G.quot S).linSpan.FG
  simpa [PointedCone.linSpan_quot] using Submodule.FG.map (f := S.mkQ) hG

/-- Dimension-addition for cone finrank along a contained subcone. -/
lemma finrank_eq_finrank_add_finrank_quot_linSpan {F G : PointedCone R M}
    (hG : G.FinRank) (hFG : F ≤ G) :
    G.finrank = F.finrank + (G.quot F.linSpan).finrank := by
  letI : Module.Finite R G.linSpan := Module.Finite.iff_fg.mpr hG
  letI : Module.Finite R F.linSpan := Module.Finite.iff_fg.mpr <|
    PointedCone.finRank_of_le hG hFG
  letI : Module.Finite R (G.quot F.linSpan).linSpan := Module.Finite.iff_fg.mpr <|
    PointedCone.finRank_quot_linSpan hG
  let f : G.linSpan →ₗ[R] (M ⧸ F.linSpan) := (F.linSpan.mkQ).domRestrict G.linSpan
  have hker : Module.finrank R f.ker = Module.finrank R F.linSpan := by
    rw [show f.ker = Submodule.comap G.linSpan.subtype F.linSpan by
      simpa [f] using ker_domRestrict_mkQ_linSpan F G]
    exact (Submodule.comapSubtypeEquivOfLe (Submodule.span_mono hFG)).finrank_eq
  have hrange : (G.quot F.linSpan).linSpan = f.range := by
    change (G.quot F.linSpan).linSpan = ((F.linSpan.mkQ).domRestrict G.linSpan).range
    exact linSpan_quot_eq_range_domRestrict_mkQ F G
  have hmain : Module.finrank R f.range + Module.finrank R f.ker = Module.finrank R G.linSpan :=
    LinearMap.finrank_range_add_finrank_ker f
  calc
    G.finrank = Module.finrank R G.linSpan := rfl
    _ = Module.finrank R f.range + Module.finrank R f.ker := hmain.symm
    _ = Module.finrank R (G.quot F.linSpan).linSpan + Module.finrank R F.linSpan := by
      rw [hrange, hker]
    _ = (G.quot F.linSpan).finrank + F.finrank := rfl
    _ = F.finrank + (G.quot F.linSpan).finrank := by simp [add_comm]

end Quotients

/-! ### Salient rank -/

section Salient

variable {R : Type*} [DivisionRing R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

section Definitions

variable {R : Type*} [Ring R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

/-- Salient rank of a cone. -/
noncomputable def salRank (C : PointedCone R M) := C.salientQuot.rank

/-- Salient finrank of a cone. -/
noncomputable def salFinrank (C : PointedCone R M) := C.salientQuot.finrank

abbrev FinSalRank (C : PointedCone R M) := FinRank C.salientQuot

end Definitions

section Decomposition

variable {R : Type*} [DivisionRing R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

/-- Dimension-addition for rank, split into lineality and salient quotient. -/
lemma rank_eq_rank_lineal_add_salRank (C : PointedCone R M) :
    C.rank = Module.rank R C.lineal + C.salRank := by
  have h := PointedCone.rank_eq_rank_add_rank_quot_linSpan
    (F := ((C.lineal : Submodule R M) : PointedCone R M)) C.lineal_le
  have hlineal :
      (((C.lineal : Submodule R M) : PointedCone R M)).rank = Module.rank R C.lineal := by
    rw [PointedCone.rank, coe_linSpan]
  rw [hlineal, coe_linSpan] at h
  simpa [PointedCone.rank, PointedCone.salRank, PointedCone.salientQuot, add_comm] using h

/-- Dimension-addition for finrank, split into lineality and salient quotient. -/
lemma finrank_eq_finrank_lineal_add_salFinrank (C : PointedCone R M)
    (hC : C.FinRank) :
    C.finrank = Module.finrank R C.lineal + C.salFinrank := by
  letI : Module.Finite R C.linSpan := Module.Finite.iff_fg.mpr hC
  have h := PointedCone.finrank_eq_finrank_add_finrank_quot_linSpan
    (F := ((C.lineal : Submodule R M) : PointedCone R M)) hC C.lineal_le
  have hlineal :
      (((C.lineal : Submodule R M) : PointedCone R M)).finrank = Module.finrank R C.lineal := by
    rw [PointedCone.finrank, coe_linSpan]
  rw [hlineal, coe_linSpan] at h
  simpa [PointedCone.finrank, PointedCone.salFinrank, PointedCone.salientQuot, add_comm] using h

/-- A cone with trivial lineality has salient rank equal to rank. -/
lemma salRank_eq_rank_of_lineal_eq_bot (C : PointedCone R M) (hlineal : C.lineal = ⊥) :
    C.salRank = C.rank := by
  have h := PointedCone.rank_eq_rank_lineal_add_salRank C
  rw [hlineal] at h
  simpa [add_comm] using h.symm

/-- A cone with trivial lineality has salient finrank equal to finrank. -/
lemma salFinrank_eq_finrank_of_lineal_eq_bot (C : PointedCone R M)
    (hC : C.FinRank) (hlineal : C.lineal = ⊥) :
    C.salFinrank = C.finrank := by
  have h := PointedCone.finrank_eq_finrank_lineal_add_salFinrank C hC
  rw [hlineal] at h
  simpa [add_comm] using h.symm

/-- In finite-dimensional span, salient rank is the cardinal cast of salient finrank. -/
lemma salRank_eq_natCast_salFinrank (C : PointedCone R M) (hC : C.FinSalRank) :
    C.salRank = (C.salFinrank : Cardinal) := by
  letI : Module.Finite R (C.salientQuot).linSpan := Module.Finite.iff_fg.mpr hC
  rw [PointedCone.salRank, PointedCone.salFinrank, PointedCone.rank, PointedCone.finrank]
  exact (Module.finrank_eq_rank (R := R) (M := (C.salientQuot).linSpan)).symm

end Decomposition

end Salient

/-! ### Rank-zero cones -/

section RankZero

variable {R : Type*} [Ring R] [PartialOrder R] [IsOrderedRing R] [IsDomain R]
variable {M : Type*} [AddCommGroup M] [Module R M] [Module.IsTorsionFree R M]
variable {C : PointedCone R M}

lemma bot_of_rank_zero (h : C.rank = 0) : C = ⊥ := by
  have hlin : C.linSpan = (⊥ : Submodule R M) :=
    (Submodule.rank_eq_zero).1 (by simpa [PointedCone.rank] using h)
  exact le_bot_iff.mp (by simpa [hlin] using (PointedCone.le_submodule_span C))

lemma bot_iff_rank_zero : C.rank = 0 ↔ C = ⊥ :=
  ⟨bot_of_rank_zero, by rintro rfl; simp [PointedCone.rank]⟩

end RankZero

end PointedCone
