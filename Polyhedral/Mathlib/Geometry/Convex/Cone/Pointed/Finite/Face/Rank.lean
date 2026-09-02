/-
Copyright (c) 2025 Olivia Röhrig, Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Olivia Röhrig, Martin Winter
-/
module

public import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Rank
public import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Face.Lattice

/-!
## Rank of Faces

This file collects rank constructions for faces and the dimension formulas attached to face
inclusions.
-/

public section

open Submodule (span)

namespace PointedCone

namespace Face
section Basic

variable {R : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {C : PointedCone R M}

end Basic

section RankZero

variable {R : Type*} [Ring R] [LinearOrder R] [IsOrderedRing R] [IsDomain R]
variable {M : Type*} [AddCommGroup M] [Module R M] [Module.IsTorsionFree R M]
variable {C : PointedCone R M}

lemma bot_iff_rank_zero {F : Face C} (hC : C.Salient) : F.rank = 0 ↔ F = ⊥ := by
  have hEq : ((F : PointedCone R M) = (⊥ : PointedCone R M)) ↔ F = ⊥ := by
    sorry
    -- simpa only [Face.lineal_bot, PointedCone.salient_iff_lineal_bot.mp hC] using
    --   (Face.toPointedCone_eq_iff (F₁ := F) (F₂ := (⊥ : Face C)))
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
lemma salFinrank_eq_salFinrank_add_finrank_quot_span {F G : PointedCone R M}
    (hF : F.IsFaceOf G) (hG : G.FinRank) :
    G.salFinrank = F.salFinrank + (G.quot (span R F)).finrank := by
  have hFfin : F.FinRank :=
    PointedCone.finRank_of_le hG hF.le
  have hFG := PointedCone.finrank_eq_finrank_add_finrank_quot_span
      hG hF.le
  rw [PointedCone.finrank_eq_finrank_lineal_add_salFinrank G hG,
    PointedCone.finrank_eq_finrank_lineal_add_salFinrank F hFfin,
    hF.lineal_congr, Nat.add_assoc] at hFG
  exact Nat.add_left_cancel hFG

/-- Dimension-addition for salient finrank along a face inclusion. -/
lemma salFinrank_eq_salFinrank_add_salFinrank_quot_span {F G : PointedCone R M}
    (hF : F.IsFaceOf G) (hG : G.FinRank) :
    G.salFinrank = F.salFinrank + (G.quot (span R F)).salFinrank := by
  have hqlineal : (G.quot (span R F)).lineal = ⊥ :=
    PointedCone.salient_iff_lineal_bot.mp (hF.quot_salient)
  have hqfin : (G.quot (span R F)).FinRank :=
    PointedCone.finRank_quot_span hG
  have hq : (G.quot (span R F)).salFinrank = (G.quot (span R F)).finrank :=
    PointedCone.salFinrank_eq_finrank_of_lineal_eq_bot
      (C := G.quot (span R F)) hqfin hqlineal
  simpa [hq] using
    salFinrank_eq_salFinrank_add_finrank_quot_span hF hG

/-- Dimension-addition for salient rank along a face inclusion (finite lineality case). -/
lemma salRank_eq_salRank_add_rank_quot_span {F G : PointedCone R M}
    (hF : F.IsFaceOf G) (hlinealG : G.lineal.FG) :
    G.salRank = F.salRank + (G.quot (span R F)).rank := by
  let := Module.Finite.iff_fg.mpr hlinealG
  have hlineal := hF.lineal_congr
  let := hlineal.symm ▸ (inferInstance : Module.Finite R G.lineal)
  have hFG := rank_eq_rank_add_rank_quot_span hF.le
  rw [rank_eq_rank_lineal_add_salRank F, rank_eq_rank_lineal_add_salRank G, hlineal] at hFG
  exact Cardinal.eq_of_add_eq_add_left (by simpa [add_assoc] using hFG)
    (Module.rank_lt_aleph0 R G.lineal)

/-- Dimension-addition for salient rank along a face inclusion (finite lineality case). -/
lemma salRank_eq_salRank_add_salRank_quot_span {F G : PointedCone R M}
    (hF : F.IsFaceOf G) (hlinealG : G.lineal.FG) :
    G.salRank = F.salRank + (G.quot (span R F)).salRank := by
  have hqlineal : (G.quot (span R F)).lineal = ⊥ :=
    PointedCone.salient_iff_lineal_bot.mp (hF.quot_salient)
  have hq : (G.quot (span R F)).salRank = (G.quot (span R F)).rank :=
    PointedCone.salRank_eq_rank_of_lineal_eq_bot (C := G.quot (span R F)) hqlineal
  simpa [hq] using salRank_eq_salRank_add_rank_quot_span hF hlinealG

end Salient

end IsFaceOf

end PointedCone
