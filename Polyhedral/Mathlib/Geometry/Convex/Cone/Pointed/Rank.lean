/-
Copyright (c) 2025 Olivia Röhig, Kilian Rueß, Mrtin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Olivia Röhig, Kilian Rueß, Mrtin Winter
-/

import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Lineal
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Dual
import Polyhedral.Mathlib.Algebra.Module.Submodule.Dual.Field

/-!
## Rank of Pointed Cones

This file collects rank constructions for pointed cones and the associated dimension formulas.

Ranks:
* `PointedCone.rank` is the rank of the span of the cone.
* `PointedCone.finrank` is the finrank of the span of the cone.
* `PointedCone.salRank` is the salient rank of the span of the cone, that is, the rank of the
  span after factoring by the lineality space.
* `PointedCone.salFinrank` is the salient finrank of the span of the cone.

Predicates:
* `PointedCone.FinRank` states that the cone has a finite rank.
* `PointedCone.FinSalRank` states that the cone has a finite salient rank.
-/

namespace PointedCone

open Module Cardinal
open Submodule (span)

/-! ### Basic rank notions -/

section Semiring

variable {R M : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R] [AddCommMonoid M]
  [Module R M]

noncomputable abbrev rank (C : PointedCone R M) := Module.rank R (span R (C : Set M))

noncomputable abbrev finrank (C : PointedCone R M) := Module.finrank R (span R (C : Set M))

-- NOTE: this is not the same as Module.Finite or FG!
abbrev FinRank (C : PointedCone R M) := (span R (C : Set M)).FG

@[simp] lemma finRank_of_isNoetherian [IsNoetherian R M] (C : PointedCone R M) : C.FinRank :=
  IsNoetherian.noetherian (span R (C : Set M))

lemma FG.finRank {C : PointedCone R M} (hC : C.FG) : C.FinRank := hC.span

alias finRank_of_fg := FG.finRank

lemma zero_le_rank (C : PointedCone R M) : 0 ≤ C.rank := bot_le

lemma rank_mono {C F : PointedCone R M} (hF : F ≤ C) : F.rank ≤ C.rank :=
  Submodule.rank_mono <| Submodule.span_mono <| IsConcreteLE.coe_subset_coe'.mpr hF

end Semiring

section Ring

variable {R : Type*} [Ring R] [PartialOrder R] [IsOrderedRing R] [IsDomain R]
variable {M : Type*} [AddCommGroup M] [Module R M] [Module.IsTorsionFree R M]
variable {C : PointedCone R M}

lemma bot_of_rank_zero (h : C.rank = 0) : C = ⊥ := by
  have hlin : span R C = (⊥ : Submodule R M) :=
    (Submodule.rank_eq_zero).1 (by simpa [PointedCone.rank] using h)
  exact le_bot_iff.mp (by simpa [hlin] using (PointedCone.le_span (C := C)))

lemma bot_iff_rank_zero : C.rank = 0 ↔ C = ⊥ :=
  ⟨bot_of_rank_zero, by rintro rfl; simp [PointedCone.rank]⟩

@[simp] lemma rank_bot_eq_zero : (⊥ : PointedCone R M).rank = 0 := by rw [bot_iff_rank_zero]

end Ring

/-! ### Rank formulas for quotients -/

section Quotients

variable {R : Type*} [DivisionRing R] [PartialOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

private lemma ker_domRestrict_mkQ_span (F G : PointedCone R M) :
    (((span R (F : Set M)).mkQ).domRestrict (span R (G : Set M))).ker =
      Submodule.comap (span R (G : Set M)).subtype (span R (F : Set M)) := by
  simp [LinearMap.ker_domRestrict, Submodule.ker_mkQ]

private lemma span_quot_eq_range_domRestrict_mkQ (F G : PointedCone R M) :
    span R (G.quot (span R (F : Set M))) =
      (((span R (F : Set M)).mkQ).domRestrict (span R (G : Set M))).range := by
  exact (span_quot (C := G) (S := span R (F : Set M))).trans
    (LinearMap.range_domRestrict
      (K := span R (G : Set M)) (f := (span R (F : Set M)).mkQ)).symm

/-- Dimension-addition for cone rank along a contained subcone. -/
lemma rank_eq_rank_add_rank_quot_span {F G : PointedCone R M} (hFG : F ≤ G) :
    G.rank = F.rank + (G.quot (span R (F : Set M))).rank := by
  let f : span R (G : Set M) →ₗ[R] (M ⧸ span R (F : Set M)) :=
    (span R (F : Set M)).mkQ.domRestrict (span R (G : Set M))
  have hker : Module.rank R f.ker = Module.rank R (span R (F : Set M)) := by
    rw [show f.ker = Submodule.comap (span R (G : Set M)).subtype
        (span R (F : Set M)) by
      simpa [f] using ker_domRestrict_mkQ_span F G]
    exact (Submodule.comapSubtypeEquivOfLe (Submodule.span_mono hFG)).rank_eq
  have hrange : span R (G.quot (span R (F : Set M))) = f.range := by
    change span R (G.quot (span R (F : Set M))) =
      ((span R (F : Set M)).mkQ.domRestrict (span R (G : Set M))).range
    exact span_quot_eq_range_domRestrict_mkQ F G
  have hmain : Module.rank R f.range + Module.rank R f.ker =
      Module.rank R (span R (G : Set M)) :=
    LinearMap.rank_range_add_rank_ker f
  calc
    G.rank = Module.rank R (span R (G : Set M)) := rfl
    _ = Module.rank R f.range + Module.rank R f.ker := hmain.symm
    _ = Module.rank R (span R (G.quot (span R (F : Set M)) :
        Set (M ⧸ span R (F : Set M)))) +
        Module.rank R (span R (F : Set M)) := by
      rw [hrange, hker]
    _ = (G.quot (span R (F : Set M))).rank + F.rank := rfl
    _ = F.rank + (G.quot (span R (F : Set M))).rank := by simp [add_comm]

/-- Finite rank descends to a contained cone's span. -/
lemma finRank_of_le {F G : PointedCone R M} (hG : G.FinRank) (hFG : F ≤ G) :
    F.FinRank := by
  let : Module.Finite R (span R (G : Set M)) := Module.Finite.iff_fg.mpr hG
  exact Module.Finite.iff_fg.mp <|
    Module.Finite.of_injective (Submodule.inclusion (Submodule.span_mono hFG))
      (Submodule.inclusion_injective (Submodule.span_mono hFG))

/-- Finite rank descends to the span of a quotient cone. -/
lemma finRank_quot_span {F G : PointedCone R M} (hG : G.FinRank) :
    (G.quot (span R (F : Set M))).FinRank := by
  change (span R (G.quot (span R (F : Set M)) :
    Set (M ⧸ span R (F : Set M)))).FG
  simpa only [span_quot] using
    Submodule.FG.map (f := (span R (F : Set M)).mkQ) hG

/-- Finite rank descends to the span of a quotient by a submodule. -/
lemma finRank_quot_submodule (G : PointedCone R M) (S : Submodule R M) (hG : G.FinRank) :
    (G.quot S).FinRank := by
  change (span R (G.quot S : Set (M ⧸ S))).FG
  simpa only [span_quot] using Submodule.FG.map (f := S.mkQ) hG

/-- Dimension-addition for cone finrank along a contained subcone. -/
lemma finrank_eq_finrank_add_finrank_quot_span {F G : PointedCone R M}
    (hG : G.FinRank) (hFG : F ≤ G) :
    G.finrank = F.finrank + (G.quot (span R (F : Set M))).finrank := by
  let : Module.Finite R (span R (G : Set M)) := Module.Finite.iff_fg.mpr hG
  let : Module.Finite R (span R (F : Set M)) := Module.Finite.iff_fg.mpr <|
    PointedCone.finRank_of_le hG hFG
  let : Module.Finite R (span R (G.quot (span R (F : Set M)) :
      Set (M ⧸ span R (F : Set M)))) := Module.Finite.iff_fg.mpr <|
    PointedCone.finRank_quot_span hG
  let f : span R (G : Set M) →ₗ[R] (M ⧸ span R (F : Set M)) :=
    (span R (F : Set M)).mkQ.domRestrict (span R (G : Set M))
  have hker : Module.finrank R f.ker = Module.finrank R (span R (F : Set M)) := by
    rw [show f.ker = Submodule.comap (span R (G : Set M)).subtype
        (span R (F : Set M)) by
      simpa [f] using ker_domRestrict_mkQ_span F G]
    exact (Submodule.comapSubtypeEquivOfLe (Submodule.span_mono hFG)).finrank_eq
  have hrange : span R (G.quot (span R (F : Set M))) = f.range := by
    change span R (G.quot (span R (F : Set M))) =
      ((span R (F : Set M)).mkQ.domRestrict (span R (G : Set M))).range
    exact span_quot_eq_range_domRestrict_mkQ F G
  have hmain : Module.finrank R f.range + Module.finrank R f.ker =
      Module.finrank R (span R (G : Set M)) :=
    LinearMap.finrank_range_add_finrank_ker f
  calc
    G.finrank = Module.finrank R (span R (G : Set M)) := rfl
    _ = Module.finrank R f.range + Module.finrank R f.ker := hmain.symm
    _ = Module.finrank R (span R (G.quot (span R (F : Set M)) :
        Set (M ⧸ span R (F : Set M)))) +
        Module.finrank R (span R (F : Set M)) := by
      rw [hrange, hker]
    _ = (G.quot (span R (F : Set M))).finrank + F.finrank := rfl
    _ = F.finrank + (G.quot (span R (F : Set M))).finrank := by simp [add_comm]

end Quotients

/-! ### Salient rank -/

section Salient

variable {R : Type*} [DivisionRing R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

section Definitions

variable {R : Type*} [Ring R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {C : PointedCone R M}

/-- Salient rank of a cone. -/
noncomputable def salRank (C : PointedCone R M) := C.salientQuot.rank

/-- Salient finrank of a cone. -/
noncomputable def salFinrank (C : PointedCone R M) := C.salientQuot.finrank

/-- A cone is of finite salient rank if its salient quotient is of finite rank. It means that
  the non-trivial structure of the cone only spans finitely many dimensions. -/
abbrev FinSalRank (C : PointedCone R M) := FinRank C.salientQuot

lemma FinRank.finSalRank (h : C.FinRank) : C.FinSalRank := by
  unfold FinSalRank FinRank
  simpa only [span_quot] using Submodule.FG.map C.lineal.mkQ h

lemma FG.finSalRank (h : C.FG) : C.FinSalRank := h.finRank.finSalRank

lemma FinSalRank.finRank_of_fg_lineal (h : C.FinSalRank) (hlin : C.lineal.FG) :
    C.FinRank := by
  apply Submodule.fg_of_fg_map_of_fg_inf_ker C.lineal.mkQ
  · simpa only [← span_quot, salientQuot_eq_quot_lineal] using h
  · simpa [Submodule.ker_mkQ, inf_eq_right.mpr (lineal_le_span C)] using hlin

end Definitions

section Field

variable {R : Type*} [Field R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {C : PointedCone R M}
variable {p : M →ₗ[R] N →ₗ[R] R}

/-
NOTE: The proof of `FinSalRank.dual_finSalRank` is AI generated and very messy. There is
a cleaner approach.
* prove that salRank is the rank of the quotient module span / lineal
* prove that if A / B is FG, then B* / A* is also FG.
-/

variable (p) in
/-- The dual of a cone with finite salient rank also has finite salient rank. -/
lemma FinSalRank.dual_finSalRank (hC : C.FinSalRank) : (dual p C).FinSalRank := by
  classical
  let T := span R (dual p C : Set N)
  let L := (dual p C).lineal
  obtain ⟨D, hDT, hDL, hsup⟩ := Submodule.exists_le_disjoint_sup_self T L
  have hLT : L ≤ T := lineal_le_span (dual p C)
  have hDLT : D ⊔ L = T := by simpa [sup_eq_left.mpr hLT] using hsup
  let Q := span R (C.salientQuot : Set (M ⧸ C.lineal))
  have hDdual : D ≤ Submodule.dual p C.lineal :=
    hDT.trans span_dual_le_dual_lineal
  let f : D →ₗ[R] Dual R Q :=
    Q.subtype.dualMap.comp
      ((Submodule.dual_linearMap_dual_quot (p := p) C.lineal).comp
        (Submodule.inclusion hDdual))
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot]
    ext y
    simp only [Submodule.mem_bot, LinearMap.mem_ker]
    constructor
    · intro hy
      apply Subtype.ext
      have hyL : (y : N) ∈ L := by
        change (y : N) ∈ (dual p C).lineal
        rw [← submodule_dual_span_eq_dual_lineal]
        rw [Submodule.dual_span, Submodule.mem_dual]
        intro x hx
        have hqx : C.lineal.mkQ x ∈ Q := Submodule.subset_span ⟨x, hx, rfl⟩
        have he := LinearMap.congr_fun hy ⟨C.lineal.mkQ x, hqx⟩
        change p x y = 0 at he
        exact he.symm
      exact (hDL.le_bot ⟨y.2, hyL⟩)
    · rintro rfl
      simp
  have hQ : Q.FG := hC
  have hD : D.FG := by
    let _ : Module.Finite R (Dual R Q) :=
      (Module.finite_dual_iff R).2 (Module.Finite.iff_fg.2 hQ)
    exact Module.Finite.iff_fg.1 (Module.Finite.of_injective f hf)
  change (span R ((dual p C).quot L : Set (N ⧸ L))).FG
  rw [span_quot]
  change (Submodule.map L.mkQ T).FG
  rw [← hDLT, Submodule.map_sup]
  simpa using hD.map L.mkQ

end Field

section Decomposition

variable {R : Type*} [DivisionRing R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

/-- Dimension-addition for rank, split into lineality and salient quotient. -/
lemma rank_eq_rank_lineal_add_salRank (C : PointedCone R M) :
    C.rank = Module.rank R C.lineal + C.salRank := by
  have h := PointedCone.rank_eq_rank_add_rank_quot_span
    (F := ((C.lineal : Submodule R M) : PointedCone R M)) C.lineal_le
  change C.rank = Module.rank R (span R (C.lineal : Set M)) +
    (C.quot (span R (C.lineal : Set M))).rank at h
  rw [Submodule.span_eq] at h
  simpa [PointedCone.rank, PointedCone.salRank, PointedCone.salientQuot, add_comm] using h

/-- Dimension-addition for finrank, split into lineality and salient quotient. -/
lemma finrank_eq_finrank_lineal_add_salFinrank (C : PointedCone R M)
    (hC : C.FinRank) :
    C.finrank = Module.finrank R C.lineal + C.salFinrank := by
  let : Module.Finite R (span R (C : Set M)) := Module.Finite.iff_fg.mpr hC
  have h := PointedCone.finrank_eq_finrank_add_finrank_quot_span
    (F := ((C.lineal : Submodule R M) : PointedCone R M)) hC C.lineal_le
  change C.finrank = Module.finrank R (span R (C.lineal : Set M)) +
    (C.quot (span R (C.lineal : Set M))).finrank at h
  rw [Submodule.span_eq] at h
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
  let : Module.Finite R (span R (C.salientQuot : Set (M ⧸ C.lineal))) :=
    Module.Finite.iff_fg.mpr hC
  rw [PointedCone.salRank, PointedCone.salFinrank, PointedCone.rank, PointedCone.finrank]
  exact (Module.finrank_eq_rank
    (R := R) (M := span R (C.salientQuot : Set (M ⧸ C.lineal)))).symm

end Decomposition

end Salient

end PointedCone
