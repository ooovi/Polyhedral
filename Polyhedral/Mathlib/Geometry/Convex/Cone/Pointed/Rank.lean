/-
Copyright (c) 2025 Olivia Röhig, Kilian Rueß, Mrtin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Olivia Röhig, Kilian Rueß, Mrtin Winter
-/
module

public import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Lineal
public import Polyhedral.Mathlib.Algebra.Module.Submodule.Dual.Field

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

Eventually we aim to prove most results of finite dimensional cones by assuming `FinSalRank`.
The reason is that this does not assume that the cone is embedded in finite dimensions, and
this class is closed under duality.
-/

@[expose] public section

namespace PointedCone

variable {R M : Type*}

open Module Cardinal
open Submodule (span)

/-! ### Basic rank notions -/

section Semiring

variable [Semiring R] [PartialOrder R] [IsOrderedRing R]
variable [AddCommMonoid M] [Module R M]

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

lemma rank_monotone : Monotone (rank : PointedCone R M → Cardinal) :=
  fun _ _ => rank_mono

end Semiring

section Ring

variable [Ring R] [PartialOrder R] [IsOrderedRing R] [IsDomain R]
variable [AddCommGroup M] [Module R M] [Module.IsTorsionFree R M]

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

section DivisionRing

variable [DivisionRing R] [PartialOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M]

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

end DivisionRing

/-! ### Salient rank -/

section Ring

variable {R : Type*} [Ring R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

variable {C : PointedCone R M}

/-- Salient rank of a cone. -/
noncomputable def salRank (C : PointedCone R M) := C.salientQuot.rank

/-- Salient finrank of a cone. -/
noncomputable def salFinrank (C : PointedCone R M) := C.salientQuot.finrank

/- NOTE: there is a way to define `FinSalRank` on `Semiring` by avoiding quotients: define it as
the cones that are the sum of a FinRank cone and a submodule. This reduces to the current
definition over a `Ring`. -/
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

lemma FinSalRank.inf_finRank_of_isCompl (hC : C.FinSalRank) {S : Submodule R M}
    (hS : IsCompl C.lineal S) : (C ⊓ S).FinRank := by
  rw [FinRank, span_inf_of_codisjoint_lineal hS.codisjoint]
  refine Submodule.FG.linearEquiv (Submodule.IsCompl.map_mkQ_equiv_inf hS (lineal_le_span C)) ?_
  simpa only [LinearMap.restrictScalars_self, ← span_quot, salientQuot_eq_quot_lineal] using hC

end Ring

section DivisionRing

variable {R : Type*} [DivisionRing R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

variable {C : PointedCone R M}

lemma FinSalRank.exists_finRank_sup_lineal (hC : C.FinSalRank) :
    ∃ D : PointedCone R M, D.FinRank ∧ C = D ⊔ C.lineal := by
  let ⟨S, hS⟩ := exists_isCompl C.lineal
  refine ⟨C ⊓ S, hC.inf_finRank_of_isCompl hS, ?_⟩
  rw [inf_sup_assoc_of_le_of_submodule_le _ (lineal_le C)]
  rw [← coe_sup, hS.codisjoint.symm.eq_top]
  simp

-- # DECOMPOSITIONS

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

end DivisionRing

end PointedCone
