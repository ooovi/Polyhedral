/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Grade
public import Mathlib.Order.LatticeIntervals

/-!
# Abstract polytopes
-/

public section

-- #45582
section PartialOrder
variable {α : Type*} [PartialOrder α] [OrderBot α] [PredOrder α]
  [∀ a : α, Decidable (Order.pred a = a)]

@[simp]
theorem WithBot.succ_pred_coe [SuccOrder α] (a : α) :
    WithBot.succ (Order.pred (a : WithBot α)) = a := by
  by_cases ha : IsMin a
  · rw [WithBot.pred_coe_of_isMin ha, WithBot.succ_bot, ha.eq_bot]
  · rw [WithBot.pred_coe_of_not_isMin ha, WithBot.succ_coe, Order.succ_pred_of_not_isMin ha]

@[simp]
theorem WithBot.pred_coe_eq_bot_iff {a : α} : Order.pred (a : WithBot α) = ⊥ ↔ a = (⊥ : α) := by
  by_cases ha : IsMin a
  · rw [WithBot.pred_coe_of_isMin ha, ha.eq_bot]
    tauto
  · rw [WithBot.pred_coe_of_not_isMin ha]
    aesop

end PartialOrder

section GradeOrder
variable {𝕆 α : Type*} [Preorder 𝕆] [PartialOrder α] [GradeOrder 𝕆 α] [OrderTop α]

@[simp]
theorem grade_eq_grade_top {a : α} : grade 𝕆 a = grade 𝕆 (⊤ : α) ↔ a = ⊤ := by
  obtain rfl | ha := eq_top_or_lt_top a
  · simp
  · simpa [ha.ne] using (grade_strictMono ha).ne

end GradeOrder

section GradeMinOrder
variable {𝕆 α : Type*} [PartialOrder 𝕆] [PartialOrder α] [GradeMinOrder 𝕆 α]
  [OrderBot 𝕆] [OrderBot α]

@[simp]
theorem grade_eq_bot_iff {a : α} : grade 𝕆 a = ⊥ ↔ a = ⊥ := by
  rw [← isMin_iff_eq_bot, isMin_grade_iff, isMin_iff_eq_bot]

end GradeMinOrder

theorem Subtype.coe_covBy_coe {α : Type*} [Preorder α] {s : Set α} (hs : s.OrdConnected)
    {x y : s} (h : x ⋖ y) : (x : α) ⋖ y :=
  h.image (.subtype _) (by simpa)

open Set

/-- An abstract pre-polytope is a `ℕ`-graded bounded order satisfying the diamond property: for
any `x < y` with `grade y = grade x + 2`, the interval `Ioo x y` has exactly 2 elements.

Note that we set `grade ⊥ = 0`, whereas the literature more often sets `grade ⊥ = -1`. To recover
the latter convention, we define the `WithBot ℕ`-valued `AbstractPrepolytope.gradeBot`. -/
class AbstractPrepolytope (α : Type*) extends
    PartialOrder α, BoundedOrder α, GradeMinOrder ℕ α where
  /-- Do not use this, use `AbstractPrepolytope.card_Ioo_of_grade_add_two_eq` instead. -/
  ncard_Ioo_of_grade_add_two_eq' {x y : α} (hxy : x < y) (h : grade x + 2 = grade y) :
    (Ioo x y).ncard = 2

namespace AbstractPrepolytope
variable {α : Type*} [AbstractPrepolytope α]

@[simp]
theorem grade_eq_zero_iff {a : α} : grade ℕ a = 0 ↔ a = ⊥ :=
  grade_eq_bot_iff

theorem grade_bot : grade ℕ (⊥ : α) = 0 := by
  simp

/-- The grade or rank of a face of an abstract polytope, as a `WithBot ℕ`. -/
def gradeBot (x : α) : WithBot ℕ :=
  Order.pred (grade ℕ x)

@[simp]
theorem succ_gradeBot (x : α) : (gradeBot x).succ = grade ℕ x :=
  WithBot.succ_pred_coe _

@[simp]
theorem gradeBot_eq_bot {x : α} : gradeBot x = ⊥ ↔ x = ⊥ := by
  apply WithBot.pred_coe_eq_bot_iff.trans
  simp

@[simp]
theorem gradeBot_bot : gradeBot (⊥ : α) = ⊥ :=
  gradeBot_eq_bot.2 rfl

variable (α) in
/-- The rank of a polytope equals the grade of the top element. -/
abbrev rank : ℕ :=
  grade ℕ (⊤ : α)

theorem grade_eq_rank {x : α} : grade ℕ x = rank α ↔ x = ⊤ := by
  simp

/-- The diamond property: for any `x < y` with `grade y = grade x + 2`, the interval `Ioo x y` has
exactly 2 elements. -/
theorem ncard_Ioo_of_grade_add_two_eq {x y : α} (hxy : x < y) (h : grade ℕ x + 2 = grade ℕ y) :
    (Ioo x y).ncard = 2 :=
  ncard_Ioo_of_grade_add_two_eq' hxy h

theorem finite_Ioo_of_grade_add_two_eq {x y : α} (hxy : x < y) (h : grade ℕ x + 2 = grade ℕ y) :
    (Ioo x y).Finite := by
  apply finite_of_ncard_ne_zero
  simp [ncard_Ioo_of_grade_add_two_eq hxy h]

theorem ncard_Ico_of_grade_add_two_eq {x y : α} (hxy : x < y) (h : grade ℕ x + 2 = grade ℕ y) :
    (Ico x y).ncard = 3 := by
  rw [← Ioo_insert_left hxy,
    ncard_insert_of_notMem left_notMem_Ioo (finite_Ioo_of_grade_add_two_eq hxy h),
    ncard_Ioo_of_grade_add_two_eq hxy h]

theorem finite_Ico_of_grade_add_two_eq {x y : α} (hxy : x < y) (h : grade ℕ x + 2 = grade ℕ y) :
    (Ico x y).Finite := by
  apply finite_of_ncard_ne_zero
  simp [ncard_Ico_of_grade_add_two_eq hxy h]

theorem ncard_Ioc_of_grade_add_two_eq {x y : α} (hxy : x < y) (h : grade ℕ x + 2 = grade ℕ y) :
    (Ioc x y).ncard = 3 := by
  rw [← Ioo_insert_right hxy,
    ncard_insert_of_notMem right_notMem_Ioo (finite_Ioo_of_grade_add_two_eq hxy h),
    ncard_Ioo_of_grade_add_two_eq hxy h]

theorem finite_Ioc_of_grade_add_two_eq {x y : α} (hxy : x < y) (h : grade ℕ x + 2 = grade ℕ y) :
    (Ioc x y).Finite := by
  apply finite_of_ncard_ne_zero
  simp [ncard_Ioc_of_grade_add_two_eq hxy h]

theorem ncard_Icc_of_grade_add_two_eq {x y : α} (hxy : x < y) (h : grade ℕ x + 2 = grade ℕ y) :
    (Icc x y).ncard = 4 := by
  rw [← Ico_insert_right hxy.le,
    ncard_insert_of_notMem right_notMem_Ico (finite_Ico_of_grade_add_two_eq hxy h),
    ncard_Ico_of_grade_add_two_eq hxy h]

theorem finite_Icc_of_grade_add_two_eq {x y : α} (hxy : x < y) (h : grade ℕ x + 2 = grade ℕ y) :
    (Icc x y).Finite := by
  apply finite_of_ncard_ne_zero
  simp [ncard_Icc_of_grade_add_two_eq hxy h]

/-- Every closed interval of a pre-polytope (called a section in the literature) is also a
pre-polytope. -/
instance toIcc (x y : α) [Fact (x ≤ y)] : AbstractPrepolytope (Icc x y) where
  grade z := grade ℕ z.1 - grade ℕ x
  isMin_grade := by simp
  grade_strictMono z w hzw :=
    Nat.sub_lt_sub_right (grade_mono z.2.1) (grade_strictMono (Subtype.strictMono_coe _ hzw))
  covBy_grade := by
    intro z w hzw
    have := (Subtype.coe_covBy_coe ordConnected_Icc hzw).grade ℕ
    rw [Nat.covBy_iff_add_one_eq] at this ⊢
    rw [← this, Nat.sub_add_comm]
    exact grade_mono z.2.1
  ncard_Ioo_of_grade_add_two_eq' {z w} hzw h := by
    rw [← ncard_image_of_injective _ Subtype.coe_injective, Set.image_subtype_val_Ioo,
      ncard_Ioo_of_grade_add_two_eq (Subtype.strictMono_coe _ hzw)]
    have := grade_mono (𝕆 := ℕ) z.2.1
    lia

/-- Every flag of `α` is order-isomorphic to the interval `Iic (rank α)`. -/
def flagIsoIic (f : Flag α) : f ≃o Iic (rank α) where
  toFun x := ⟨grade ℕ x, sorry⟩
  invFun := sorry
  map_rel_iff' := sorry
  left_inv := sorry
  right_inv := sorry

/-- The unique element of a flag with a given grade. Will never be the minimal nor the maximal
element. -/
def flagEnum (f : Flag α) (i : Fin (rank α)) : α :=
  (flagIsoIic f).symm ⟨i + 1, sorry⟩

/-- The unique flag which shares all elements save for the one with `gradeBot` equal to `i`. -/
def adjFlag (f : Flag α) (i : Fin (rank α)) : Flag α := sorry

variable (α) in
/-- The adjacency graph of flags. -/
def flagGraph : SimpleGraph (Flag α) where
  Adj f₁ f₂ := ∃ i, adjFlag f₁ i = f₂
  symm := sorry
  loopless := sorry

variable (α) in
/-- A pre-polytope is said to be flag-connected when its flag graph is connected. -/
def IsFlagConnected : Prop :=
  (flagGraph α).Preconnected

theorem IsFlagConnected.connected (h : IsFlagConnected α) : (flagGraph α).Connected where
  preconnected := h

end AbstractPrepolytope

/-- An abstract polytope is a strongly connected pre-polytope, meaning that every interval `Icc x y`
with `x ≤ y` is flag-connected. -/
class AbstractPolytope (α : Type*) extends AbstractPrepolytope α where
  /-- Strong connectedness: every interval `Icc x y` with `x ≤ y` is flag-connected. -/
  isFlagConnected_Icc (x y : α) [Fact (x ≤ y)] : AbstractPrepolytope.IsFlagConnected (Icc x y)
