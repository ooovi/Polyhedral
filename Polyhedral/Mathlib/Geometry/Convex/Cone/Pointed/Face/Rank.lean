import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Rank
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Face.Lattice

/-!
## Rank of Faces

This file collects rank constructions for faces and the dimension formulas attached to face
inclusions.
-/

namespace PointedCone

namespace Face
section Basic

variable {R : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {C : PointedCone R M}

noncomputable def rank (F : Face C) := Module.rank R F.span

end Basic

section RankZero

variable {R : Type*} [Ring R] [LinearOrder R] [IsOrderedRing R] [IsDomain R]
variable {M : Type*} [AddCommGroup M] [Module R M] [Module.IsTorsionFree R M]
variable {C : PointedCone R M}

lemma bot_iff_rank_zero {F : Face C} (hC : C.Salient) : F.rank = 0 ↔ F = ⊥ := by
  have hEq : ((F : PointedCone R M) = (⊥ : PointedCone R M)) ↔ F = ⊥ := by
    simpa only [Face.lineal_bot, PointedCone.salient_iff_lineal_bot.mp hC] using
      (Face.toPointedCone_eq_iff (F₁ := F) (F₂ := (⊥ : Face C)))
  simpa [Face.rank, PointedCone.rank] using
    (PointedCone.bot_iff_rank_zero (C := (F : PointedCone R M))).trans hEq

end RankZero

end Face

namespace IsFaceOf

/-! ### Rank formulas along face inclusions -/

section Salient

variable {R : Type*} [DivisionRing R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {C F G : PointedCone R M}

/-- Dimension-addition for salient finrank along a face inclusion. -/
lemma salFinrank_eq_salFinrank_add_finrank_quot_linSpan {F G : PointedCone R M}
    (hF : F.IsFaceOf G) (hG : G.FinRank) :
    G.salFinrank = F.salFinrank + (G.quot F.linSpan).finrank := by
  have hFfin : F.FinRank :=
    PointedCone.finRank_of_le hG hF.le
  have hFG := PointedCone.finrank_eq_finrank_add_finrank_quot_linSpan
      hG hF.le
  rw [PointedCone.finrank_eq_finrank_lineal_add_salFinrank G hG,
    PointedCone.finrank_eq_finrank_lineal_add_salFinrank F hFfin,
    hF.lineal_eq_lineal, Nat.add_assoc] at hFG
  exact Nat.add_left_cancel hFG

/-- Dimension-addition for salient finrank along a face inclusion. -/
lemma salFinrank_eq_salFinrank_add_salFinrank_quot_linSpan {F G : PointedCone R M}
    (hF : F.IsFaceOf G) (hG : G.FinRank) :
    G.salFinrank = F.salFinrank + (G.quot F.linSpan).salFinrank := by
  have hqlineal : (G.quot F.linSpan).lineal = ⊥ :=
    PointedCone.salient_iff_lineal_bot.mp (hF.quot_salient)
  have hqfin : (G.quot F.linSpan).FinRank :=
    PointedCone.finRank_quot_linSpan hG
  have hq : (G.quot F.linSpan).salFinrank = (G.quot F.linSpan).finrank :=
    PointedCone.salFinrank_eq_finrank_of_lineal_eq_bot
      (C := G.quot F.linSpan) hqfin hqlineal
  simpa [hq] using
    salFinrank_eq_salFinrank_add_finrank_quot_linSpan hF hG

/-- Dimension-addition for salient rank along a face inclusion (finite lineality case). -/
lemma salRank_eq_salRank_add_rank_quot_linSpan {F G : PointedCone R M}
    (hF : F.IsFaceOf G) (hlinealG : G.lineal.FG) :
    G.salRank = F.salRank + (G.quot F.linSpan).rank := by
  letI : Module.Finite R G.lineal := Module.Finite.iff_fg.mpr hlinealG
  have hFG := PointedCone.rank_eq_rank_add_rank_quot_linSpan
      hF.le
  have hG := PointedCone.rank_eq_rank_lineal_add_salRank G
  have hlineal : F.lineal = G.lineal := hF.lineal_eq_lineal
  letI : Module.Finite R F.lineal := hlineal.symm ▸ (inferInstance : Module.Finite R G.lineal)
  have hF' := PointedCone.rank_eq_rank_lineal_add_salRank F
  rw [hG, hF', hlineal] at hFG
  exact Cardinal.eq_of_add_eq_add_left (by simpa [add_assoc] using hFG)
    (Module.rank_lt_aleph0 R G.lineal)

/-- Dimension-addition for salient rank along a face inclusion (finite lineality case). -/
lemma salRank_eq_salRank_add_salRank_quot_linSpan {F G : PointedCone R M}
    (hF : F.IsFaceOf G) (hlinealG : G.lineal.FG) :
    G.salRank = F.salRank + (G.quot F.linSpan).salRank := by
  have hqlineal : (G.quot F.linSpan).lineal = ⊥ :=
    PointedCone.salient_iff_lineal_bot.mp (hF.quot_salient)
  have hq : (G.quot F.linSpan).salRank = (G.quot F.linSpan).rank :=
    PointedCone.salRank_eq_rank_of_lineal_eq_bot (C := G.quot F.linSpan) hqlineal
  simpa [hq] using salRank_eq_salRank_add_rank_quot_linSpan hF hlinealG

end Salient

end IsFaceOf

end PointedCone
