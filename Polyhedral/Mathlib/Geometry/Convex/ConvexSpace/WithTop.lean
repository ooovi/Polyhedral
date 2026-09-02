/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Polyhedral.Mathlib.Data.Finsupp.Basic
public import Polyhedral.Mathlib.Data.Finsupp.Option
public import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Order

/-!
# Adjoining a top or bottom element to a convex space

Adjoining a top/bottom element to a convex space `X` again gives a convex space, by setting
any convex combination that puts positive weight on `⊤`/`⊥` to `⊤`/`⊥`.

Although this construction is also valid for `Option`, we refrain from adding it as we have no
application in mind. The `WithTop` and `WithBot` versions are useful to talk about convex functions
taking extended values.
-/

public noncomputable section

namespace Convexity
variable {R X : Type*} [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]

namespace StdSimplex

/-- Turn a distribution on `WithTop X` putting no weight on `⊤` into a distribution on `X`. -/
@[expose, to_dual (dont_translate := R) (attr := simps)
/-- Turn a distribution on `WithBot X` putting no weight on `⊥` into a distribution on `X`. -/]
def untop (w : StdSimplex R (WithTop X)) (hw : w.weights ⊤ = 0) : StdSimplex R X where
  weights := w.weights.withTopSome
  nonneg x := w.weights_nonneg (x : WithTop X)
  total := by rw [Finsupp.sum_withTopSome hw (g := fun _ r ↦ r)]; exact w.total

@[to_dual (attr := simp) (dont_translate := R)]
lemma map_untop_some (w : StdSimplex R (WithTop X)) (hw : w.weights ⊤ = 0) :
    (w.untop hw).map WithTop.some = w := by
  ext b
  induction b with
  | top => rw [weights_map, Finsupp.mapDomain_of_notMem_range _ _ (by simp), hw]
  | coe x =>
    rw [weights_map, Finsupp.mapDomain_apply_of_injective WithTop.coe_injective]
    rfl

@[to_dual (attr := simp) (dont_translate := R)]
lemma untop_map_some (w : StdSimplex R X) (hw) : (w.map WithTop.some).untop hw = w := by
  ext x
  change (w.map WithTop.some).weights (x : WithTop X) = w.weights x
  rw [weights_map, Finsupp.mapDomain_apply_of_injective WithTop.coe_injective]

@[to_dual (dont_translate := R)]
lemma mem_range_map_withTopSome {w : StdSimplex R (WithTop X)} :
    w ∈ Set.range (map WithTop.some) ↔ w.weights ⊤ = 0 where
  mp := by rintro ⟨v, rfl⟩; rw [weights_map, Finsupp.mapDomain_of_notMem_range _ _ (by simp)]
  mpr hw := ⟨w.untop hw, map_untop_some w hw⟩

end StdSimplex

open StdSimplex

section ConvexSpace
variable [ConvexSpace R X] {w : StdSimplex R (WithTop X)}

/-- Adjoining a top element to a convex space gives a convex space in which `⊤` is absorbing:
a convex combination putting positive weight on `⊤` is equal to `⊤`. -/
@[to_dual (dont_translate := R)
/-- Adjoining a bottom element to a convex space gives a convex space in which `⊥` is absorbing:
a convex combination putting positive weight on `⊥` is equal to `⊥`. -/]
instance : ConvexSpace R (WithTop X) :=
  let c (w : StdSimplex R (WithTop X)) : WithTop X :=
    open scoped Classical in if hw : w.weights ⊤ = 0 then ↑(w.untop hw).sConvexComb else ⊤
  have hcoe (w : StdSimplex R X) : c (w.map WithTop.some) = ↑w.sConvexComb := by
    simp [c, dite_eq_left <| mem_range_map_withTopSome.1 ⟨w, rfl⟩]
  have htop (w : StdSimplex R (WithTop X)) : c w = ⊤ ↔ w.weights ⊤ ≠ 0 := by
    classical exact Ne.dite_eq_right_iff <| by simp
  .mk
    (sConvexComb := c)
    (single := fun x ↦ by
      induction x with
      | top => simp [htop]
      | coe a => rw [← map_single, hcoe, sConvexComb_single])
    (assoc := fun F ↦ by
      classical
      by_cases hF : ∀ v ∈ F.weights.support, v.weights (⊤ : WithTop X) = 0
      · obtain ⟨G, rfl⟩ : F ∈ Set.range (map (map WithTop.some)) := by
          refine mem_range_map_iff .. |>.2 fun w hw ↦ ?_
          by_contra hw0
          exact hw ⟨w.untop (hF w (Finsupp.mem_support_iff.2 hw0)), map_untop_some ..⟩
        simp only [map_map, hcoe]
        rw [← map_map, hcoe, ← map_sConvexComb, hcoe, sConvexComb_sConvexComb]
      · have hc : ∃ v ∈ F.weights.support, v.weights (⊤ : WithTop X) ≠ 0 := by
          by_contra hc
          exact hF fun v hv ↦ not_not.1 fun h ↦ hc ⟨v, hv, h⟩
        have h₁ : c (F.map c) = ⊤ := by simpa [htop, ← Finsupp.mem_support_iff] using hc
        have h₂ : c F.sConvexComb = ⊤ := by
          simp only [htop, weights_sConvexComb, Finsupp.sum, Finsupp.coe_finsetSum,
            Finsupp.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ne_eq]
          obtain ⟨v₀, hv₀, hv₀'⟩ := hc
          exact (Finset.sum_pos' (fun d _ ↦ mul_nonneg (F.weights_nonneg d) (d.weights_nonneg ⊤))
            ⟨v₀, hv₀, mul_pos ((F.weights_nonneg v₀).lt_of_ne' (Finsupp.mem_support_iff.1 hv₀))
              ((v₀.weights_nonneg ⊤).lt_of_ne' hv₀')⟩).ne'
        rw [h₁, h₂])

@[to_dual (dont_translate := R)]
lemma sConvexComb_withTop_eq_some (hw : w.weights ⊤ = 0) :
    sConvexComb w = ↑(w.untop hw).sConvexComb := dite_eq_left hw

@[to_dual (attr := simp) (dont_translate := R)]
lemma sConvexComb_withTop_eq_top : sConvexComb w = ⊤ ↔ w.weights ⊤ ≠ 0 := by
  by_cases hw : w.weights ⊤ = 0
  · simp [sConvexComb_withTop_eq_some hw, hw]
  · simp [show sConvexComb w = ⊤ from dite_eq_right hw, hw]

@[to_dual (attr := simp) (dont_translate := R)]
lemma sConvexComb_map_withTopSome (v : StdSimplex R X) :
    sConvexComb (v.map WithTop.some) = ↑v.sConvexComb := by
  rw [sConvexComb_withTop_eq_some (mem_range_map_withTopSome.1 ⟨v, rfl⟩), untop_map_some]

@[to_dual (attr := fun_prop) (dont_translate := R)]
lemma isAffineMap_withTopSome : IsAffineMap R (.some : X → WithTop X) :=
  ⟨fun v ↦ (sConvexComb_map_withTopSome v).symm⟩

end ConvexSpace

/-! ### Ordered convex space structure -/

section IsOrderedConvexSpace
variable [LinearOrder X]

namespace StdSimplex

@[simp] lemma upperMass_untop (w : StdSimplex R (WithTop X)) (hw : w.weights ⊤ = 0) (x : X) :
    (w.untop hw).upperMass x = w.upperMass (x : WithTop X) := by
  conv_rhs => rw [← map_untop_some w hw]
  rw [upperMass_map, upperMass_eq_finsuppSum]
  simp only [WithTop.coe_le_coe]

@[simp] lemma upperMass_unbot (w : StdSimplex R (WithBot X)) (hw : w.weights ⊥ = 0) (x : X) :
    (w.unbot hw).upperMass x = w.upperMass (x : WithBot X) := by
  conv_rhs => rw [← map_unbot_some w hw]
  rw [upperMass_map, upperMass_eq_finsuppSum]
  simp only [WithBot.coe_le_coe]

end StdSimplex

variable [ConvexSpace R X] [IsOrderedConvexSpace R X]

/-- Adjoining a top element to an ordered convex space gives an ordered convex space. -/
instance : IsOrderedConvexSpace R (WithTop X) where
  monotone_sConvexComb w₁ w₂ h := by
    by_cases h₂ : w₂.weights ⊤ = 0
    · -- `w₂` puts no weight on `⊤`, hence neither does the smaller `w₁`.
      have h₁ : w₁.weights ⊤ = 0 := by
        have hle := StdSimplex.upperMass_le_upperMass h (⊤ : WithTop X)
        rw [StdSimplex.upperMass_top, StdSimplex.upperMass_top, h₂] at hle
        exact le_antisymm hle (w₁.weights_nonneg ⊤)
      rw [sConvexComb_withTop_eq_some h₁, sConvexComb_withTop_eq_some h₂, WithTop.coe_le_coe]
      exact monotone_sConvexComb <| StdSimplex.le_def.2 fun x ↦ by
        simpa using StdSimplex.upperMass_le_upperMass h (x : WithTop X)
    · rw [sConvexComb_withTop_eq_top.2 h₂]
      exact le_top

/-- Adjoining a bottom element to an ordered convex space gives an ordered convex space. -/
instance : IsOrderedConvexSpace R (WithBot X) where
  monotone_sConvexComb w₁ w₂ h := by
    by_cases h₁ : w₁.weights ⊥ = 0
    · -- `w₁` puts no weight on `⊥`; since its support lies above its minimum, which is not `⊥`,
      -- neither does the larger `w₂`.
      have h₂ : w₂.weights ⊥ = 0 := by
        by_contra hbot
        have hmin := StdSimplex.forall_le_of_le h
          (x := w₁.weights.support.min' w₁.support_weights_nonempty)
          fun y hy ↦ Finset.min'_le _ _ (Finsupp.mem_support_iff.2 hy)
        have hmem := Finset.min'_mem _ w₁.support_weights_nonempty
        rw [le_bot_iff.1 (hmin hbot)] at hmem
        exact Finsupp.mem_support_iff.1 hmem h₁
      rw [sConvexComb_withBot_eq_some h₁, sConvexComb_withBot_eq_some h₂, WithBot.coe_le_coe]
      exact monotone_sConvexComb <| StdSimplex.le_def.2 fun x ↦ by
        simpa using StdSimplex.upperMass_le_upperMass h (x : WithBot X)
    · rw [sConvexComb_withBot_eq_bot.2 h₁]
      exact bot_le

end IsOrderedConvexSpace
end Convexity
