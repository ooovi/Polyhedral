/-
Copyright (c) 2025 Olivia Röhrig, Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Olivia Röhrig, Martin Winter
-/
module

public import Mathlib.Geometry.Convex.Cone.Face.Basic
public import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Lineal
public import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Rank

/-!
# Faces of pointed cones

This file proves additional lemmas for faces of pointed cones, mostly related to quotients required
to prove the order iso between a face's face lattice and the cone's lattice below the face.

-/

public section

open Submodule

@[expose] public section

variable {R M N : Type*}

namespace PointedCone

namespace IsFaceOf

section Ring

variable [Ring R] [PartialOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M]

variable {C C₁ C₂ F F₁ F₂ G : PointedCone R M}

theorem salient {C F : PointedCone R M} (hC : C.Salient) (hF : F.IsFaceOf C) : F.Salient :=
  hC.of_le_salient hF.le

lemma inf_isFaceOf_inf (h : F₁.IsFaceOf C₁) (C₂ : PointedCone R M) : (F₁ ⊓ C₂).IsFaceOf (C₁ ⊓ C₂) :=
  IsFaceOf.inf h (IsFaceOf.refl C₂)

lemma hull_nonneg_lc_mem {ι : Type*} [Fintype ι] {c : ι → R} {s : Set M} (hcc : ∀ i, 0 ≤ c i)
    {f : ι → s} {i : ι} (hF : F.IsFaceOf (hull R s)) (h : ∑ i, c i • (f i).val ∈ F)
    (cpos : 0 < c i) : (f i).val ∈ F := by
  refine mem_of_sum_smul_mem hF ?_ hcc h i cpos
  simpa [Submodule.mem_span] using fun i _ su => su (Subtype.coe_prop (f i))

-- ## Restrict / Embed

lemma restrict (S : Submodule R M) (hF : F.IsFaceOf C) :
    (restrict S F).IsFaceOf (restrict S C) := ⟨restrict_mono S hF.1, hF.2⟩

lemma embed {S : Submodule R M} {C F : PointedCone R S} (hF : F.IsFaceOf C) :
    (embed F).IsFaceOf (embed C) := hF.map _ (S.subtype_injective)

-- ## Quotients

variable {S : Submodule R M} {H : PointedCone R (M ⧸ S)}

/-- Pulling back a face of `G.quot S` gives a face of `G`. -/
lemma inf_comap_mkQ (hH : H.IsFaceOf (G.quot S)) : (G ⊓ PointedCone.comap S.mkQ H).IsFaceOf G := by
  refine ⟨inf_le_left, ?_⟩
  intro x y a hxG hyG ha hxy
  refine ⟨hxG, ?_⟩
  change S.mkQ x ∈ H
  exact hH.mem_of_smul_add_mem
    ((PointedCone.mem_map).2 ⟨x, hxG, rfl⟩)
    ((PointedCone.mem_map).2 ⟨y, hyG, rfl⟩)
    ha
    (by simpa [PointedCone.comap, LinearMap.map_smul, LinearMap.map_add] using hxy.2)

end Ring

section DirectedOrderRing

variable [Ring R] [PartialOrder R] [IsOrderedRing R] [IsDirectedOrder R]
variable [AddCommGroup M] [Module R M]

variable {C C₁ C₂ F F₁ F₂ : PointedCone R M}

lemma mem_span_iff_mem (hF : F.IsFaceOf C) {x : M} (hx : x ∈ C) : x ∈ span R F ↔ x ∈ F := by
  constructor <;> intro hxF
  · obtain ⟨_, hyF, _, hzF, h⟩ := F.mem_span.mp hxF
    rw [Eq.comm, sub_eq_iff_eq_add] at h
    exact hF.mem_of_add_mem_left hx (hF.le hzF) (h ▸ hyF)
  · exact Submodule.subset_span hxF

/- This fails for a merely partial order.
Let R = ℝ[X] with the coefficientwise order, M = R.
Let C be the cone of polynomials with all coefficients ≥ 0,
and F the face of nonnegative constant polynomials.
Then F is a face of C, but 1 ∈ F, so F.linSpan = ⊤.
Hence C ⊓ F.linSpan = C ≠ F. -/
lemma inf_span (hF : F.IsFaceOf C) : C ⊓ span R (F : Set M) = F := by
  apply le_antisymm <;> intro _ hx
  · exact (hF.mem_span_iff_mem hx.1).mp hx.2
  · exact ⟨hF.le hx, Submodule.subset_span hx⟩

lemma le_span_iff_le (hD : C₁ ≤ C) (hG : F.IsFaceOf C) : C₁ ≤ span R (F : Set M) ↔ C₁ ≤ F := by
  nth_rw 2 [← hG.inf_span]
  simpa using fun _ => hD

-- ## Quotients

/-- The quotient of a cone by the linear span of a face is a salient cone. -/
lemma quot_salient (hF : F.IsFaceOf C) :
    (C.quot (span R F)).Salient := by
  intro z hzC w hwC hzw
  rcases (PointedCone.mem_map).1 hzC with ⟨x, hxC, rfl⟩
  rcases (PointedCone.mem_map).1 hwC with ⟨y, hyC, rfl⟩
  have hxySpan : x + y ∈ span R F := by
    rw [← Submodule.ker_mkQ (span R (F : Set M))]
    exact LinearMap.mem_ker.mpr (by simpa [map_add] using hzw)
  have hxyF : x + y ∈ F := by
    rw [← hF.inf_span]
    exact ⟨C.add_mem hxC hyC, hxySpan⟩
  have hxF : x ∈ F := hF.mem_of_add_mem_left hxC hyC hxyF
  have hx0 : (span R F).mkQ x = 0 := by
    simpa [Submodule.mkQ_apply] using
      (Submodule.Quotient.mk_eq_zero (p := span R F) (x := x)).2
        (Submodule.subset_span hxF)
  simpa only [mkQ_apply] using hx0

/-- If `F` is a face of `C` and `S` is a submodule contained in the span of `F`, then
`F ⧸ S` is a face of `C ⧸ S`. -/
lemma quot {S : Submodule R M} (hF : F.IsFaceOf C) (hS : S ≤ span R F) :
    (F.quot S).IsFaceOf (C.quot S) := by
  refine ⟨map_mono hF.le, ?_⟩
  intro x y a hx hy ha hxy
  rcases PointedCone.mem_map.mp hx with ⟨x', hx'C, rfl⟩
  rcases PointedCone.mem_map.mp hy with ⟨y', hy'C, rfl⟩
  rcases PointedCone.mem_map.mp hxy with ⟨z, hzF₁, hzq⟩
  have hzsub : z - (a • x' + y') ∈ S := by
    rw [← Submodule.ker_mkQ S]
    change S.mkQ (z - (a • x' + y')) = 0
    simp [map_sub, hzq]
  have hxy_lin : a • x' + y' ∈ span R F := by
    have hz_lin : z ∈ span R F := Submodule.subset_span hzF₁
    exact ((span R (F : Set M)).sub_mem_iff_right hz_lin).mp (hS hzsub)
  have hxy_F : a • x' + y' ∈ F := by
    have hxy_C : a • x' + y' ∈ C := C.add_mem (C.smul_mem (le_of_lt ha) hx'C) hy'C
    simpa [hF.inf_span] using show a • x' + y' ∈ C ⊓ (span R (F : Set M)) from ⟨hxy_C, hxy_lin⟩
  exact PointedCone.mem_map.mpr ⟨x', hF.mem_of_smul_add_mem hx'C hy'C ha hxy_F, rfl⟩

end DirectedOrderRing

section LinearOrder

variable [Ring R] [LinearOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M]

variable {C F : PointedCone R M}

lemma sup_span_lineal_eq_span (hF : F.IsFaceOf C) :
    (C ⊔ span R (F : Set M)).lineal = span R F :=
  Eq.symm <| lineal_eq_of_quot_salient le_sup_right (by simpa using hF.quot_salient)

/-- If `F` is a face of the cone generated by `s`, then `F ∩ s` generates `F`. -/
lemma hull_inter_face_hull_inf_face {s : Set M} (hF : F.IsFaceOf (hull R s)) :
    hull R (s ∩ F) = F := by
  ext x; constructor
  · simpa only [Submodule.mem_span] using fun h => h F Set.inter_subset_right
  · intro h
    obtain ⟨n, c, g, xfg⟩ := mem_span_set'.mp (hF.le h)
    subst xfg
    apply sum_mem
    intro i _
    by_cases hh : 0 < c i
    · refine smul_mem _ (le_of_lt hh) ?_
      apply subset_hull (E := M)
      exact Set.mem_inter (Subtype.coe_prop (g i)) (hF.hull_nonneg_lc_mem (fun i => (c i).2) h hh)
    · push Not at hh
      rw [le_antisymm hh (c i).property]
      simp

end LinearOrder

section DivisionRing

variable [DivisionRing R] [LinearOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M]

variable {C F : PointedCone R M}

-- TODO: `lineal_congr` can be proven already with `Semiring`.

lemma isFaceOf_submodule_iff_lineal (S : Submodule R M) :
    IsFaceOf S C ↔ S = C.lineal := by
  constructor
  · intro hS
    simpa using hS.lineal_congr
  · rintro rfl
    exact IsFaceOf.lineal C

lemma finRank (hC : C.FinRank) (hF : F.IsFaceOf C) : F.FinRank := by
  exact Submodule.FG.of_le hC (Submodule.span_mono hF.le)

lemma finSalRank (hC : C.FinSalRank) (hF : F.IsFaceOf C) : F.FinSalRank := by
  rw [FinSalRank, salientQuot_eq_quot_lineal, hF.lineal_congr]
  exact finRank hC (hF.quot <| hF.lineal_congr ▸ lineal_le_span F)

end DivisionRing

end IsFaceOf

end PointedCone

end
