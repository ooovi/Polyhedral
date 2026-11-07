/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Geometry.Convex.Hull
public import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Defs
public import Polyhedral.Mathlib.Geometry.Convex.Segment
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination


/-!
# Convex join

This file defines the convex join of two sets. The convex join of `s` and `t` is the union of the
Iccs with one end in `s` and the other in `t`. This is notably a useful gadget to deal with
convex hulls of finite sets.
-/

@[expose] public section

open Set

namespace Convexity

variable {ι : Sort*} {𝕜 E : Type*}

section OrderedSemiring

variable (𝕜) [Semiring 𝕜] [PartialOrder 𝕜] [IsStrictOrderedRing 𝕜] [ConvexSpace 𝕜 E]
 {x y : E} {s t s₁ s₂ t₁ t₂ u : Set E}

/-- The join of two sets is the union of the Iccs joining them. This can be interpreted as the
topological join, but within the original space. -/
def convexJoin (s t : Set E) : Set E :=
  ⋃ (x ∈ s) (y ∈ t), Icc 𝕜 x y

variable {𝕜}

theorem mem_convexJoin : x ∈ convexJoin 𝕜 s t ↔ ∃ a ∈ s, ∃ b ∈ t, x ∈ Icc 𝕜 a b := by
  simp [convexJoin]

theorem convexJoin_comm (s t : Set E) : convexJoin 𝕜 s t = convexJoin 𝕜 t s :=
  (iUnion₂_comm _).trans <| by simp_rw [convexJoin, Icc_symm]

theorem convexJoin_mono (hs : s₁ ⊆ s₂) (ht : t₁ ⊆ t₂) : convexJoin 𝕜 s₁ t₁ ⊆ convexJoin 𝕜 s₂ t₂ :=
  biUnion_mono hs fun _ _ => biUnion_subset_biUnion_left ht

theorem convexJoin_mono_left (hs : s₁ ⊆ s₂) : convexJoin 𝕜 s₁ t ⊆ convexJoin 𝕜 s₂ t :=
  convexJoin_mono hs Subset.rfl

theorem convexJoin_mono_right (ht : t₁ ⊆ t₂) : convexJoin 𝕜 s t₁ ⊆ convexJoin 𝕜 s t₂ :=
  convexJoin_mono Subset.rfl ht

@[simp]
theorem convexJoin_empty_left (t : Set E) : convexJoin 𝕜 ∅ t = ∅ := by simp [convexJoin]

@[simp]
theorem convexJoin_empty_right (s : Set E) : convexJoin 𝕜 s ∅ = ∅ := by simp [convexJoin]

@[simp]
theorem convexJoin_singleton_left (t : Set E) (x : E) :
    convexJoin 𝕜 {x} t = ⋃ y ∈ t, Icc 𝕜 x y := by simp [convexJoin]

@[simp]
theorem convexJoin_singleton_right (s : Set E) (y : E) :
    convexJoin 𝕜 s {y} = ⋃ x ∈ s, Icc 𝕜 x y := by simp [convexJoin]

theorem convexJoin_singletons (x : E) : convexJoin 𝕜 {x} {y} = Icc 𝕜 x y := by simp

@[simp]
theorem convexJoin_union_left (s₁ s₂ t : Set E) :
    convexJoin 𝕜 (s₁ ∪ s₂) t = convexJoin 𝕜 s₁ t ∪ convexJoin 𝕜 s₂ t := by
  simp_rw [convexJoin, mem_union, iUnion_or, iUnion_union_distrib]

@[simp]
theorem convexJoin_union_right (s t₁ t₂ : Set E) :
    convexJoin 𝕜 s (t₁ ∪ t₂) = convexJoin 𝕜 s t₁ ∪ convexJoin 𝕜 s t₂ := by
  simp_rw [convexJoin_comm s, convexJoin_union_left]

@[simp]
theorem convexJoin_iUnion_left (s : ι → Set E) (t : Set E) :
    convexJoin 𝕜 (⋃ i, s i) t = ⋃ i, convexJoin 𝕜 (s i) t := by
  simp_rw [convexJoin, mem_iUnion, iUnion_exists]
  exact iUnion_comm _

@[simp]
theorem convexJoin_iUnion_right (s : Set E) (t : ι → Set E) :
    convexJoin 𝕜 s (⋃ i, t i) = ⋃ i, convexJoin 𝕜 s (t i) := by
  simp_rw [convexJoin_comm s, convexJoin_iUnion_left]

theorem Icc_subset_convexJoin (hx : x ∈ s) (hy : y ∈ t) : Icc 𝕜 x y ⊆ convexJoin 𝕜 s t :=
  subset_iUnion₂_of_subset x hx <| subset_iUnion₂ (s := fun y _ ↦ Icc 𝕜 x y) y hy

theorem subset_convexJoin_left (h : t.Nonempty) : s ⊆ convexJoin 𝕜 s t := fun _x hx =>
  let ⟨_y, hy⟩ := h
  Icc_subset_convexJoin hx hy <| left_mem_Icc _ _ _

theorem subset_convexJoin_right (h : s.Nonempty) : t ⊆ convexJoin 𝕜 s t :=
  convexJoin_comm (𝕜 := 𝕜) t s ▸ subset_convexJoin_left h

theorem convexJoin_subset (hs : s ⊆ u) (ht : t ⊆ u) (hu : IsConvexSet 𝕜 u) : convexJoin 𝕜 s t ⊆ u :=
  iUnion₂_subset fun _x hx => iUnion₂_subset fun _y hy => Convexity.Icc_subset_iff.mpr
    (hu.convexCombPair_mem (hs hx) (ht hy))

theorem convexJoin_subset_convexHull (s t : Set E) : convexJoin 𝕜 s t ⊆ convexHull 𝕜 (s ∪ t) :=
  convexJoin_subset (subset_union_left.trans <| subset_convexHull_self ..)
      (subset_union_right.trans <| subset_convexHull_self ..) <|
    IsConvexSet.convexHull

end OrderedSemiring

section LinearOrderedField

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [ConvexSpace 𝕜 E]
  {s t : Set E} {x : E}

theorem convexJoin_assoc_aux (s t u : Set E) :
    convexJoin 𝕜 (convexJoin 𝕜 s t) u ⊆ convexJoin 𝕜 s (convexJoin 𝕜 t u) := by
  simp_rw [subset_def, mem_convexJoin]
  rintro _ ⟨z, ⟨x, hx, y, hy, a₁, b₁, ha₁, hb₁, hab₁, rfl⟩, z, hz, a₂, b₂, ha₂, hb₂, hab₂, rfl⟩
  rcases hb₂.eq_or_lt with rfl | hh
  · refine ⟨x, hx, y, ⟨y, hy, z, hz, left_mem_Icc 𝕜 _ _⟩, a₁, b₁, ha₁, hb₁, hab₁, ?_⟩
    simp only [add_zero] at hab₂
    subst hab₂
    rw [convexCombPair_symm ha₂, convexCombPair_zero]
  · simp only [Icc, mem_ofPred_eq, ↓existsAndEq, and_true, exists_and_left]
    have hD : 0 < a₂ * b₁ + b₂ := add_pos_of_nonneg_of_pos (mul_nonneg ha₂ hb₁) hh
    have h'' : a₂ * b₁ / (a₂ * b₁ + b₂) + b₂ / (a₂ * b₁ + b₂) = 1 := by
      rw [← add_div, div_self hD.ne']
    refine ⟨x, hx, y, z, ⟨hy, hz⟩, _, _, ?_, div_nonneg hb₂ hD.le, h'',
      a₂ * a₁, a₂ * b₁ + b₂, mul_nonneg ha₂ ha₁, hD.le, (by grind), ?_⟩
    · exact div_nonneg (mul_nonneg ha₂ hb₁) hD.le
    · apply (convexCombPair_convexCombPair_assoc_left ..).symm
      grind

theorem convexJoin_assoc (s t u : Set E) :
    convexJoin 𝕜 (convexJoin 𝕜 s t) u = convexJoin 𝕜 s (convexJoin 𝕜 t u) := by
  refine (convexJoin_assoc_aux _ _ _).antisymm ?_
  simp_rw [convexJoin_comm s, convexJoin_comm _ u]
  exact convexJoin_assoc_aux _ _ _

theorem convexJoin_left_comm (s t u : Set E) :
    convexJoin 𝕜 s (convexJoin 𝕜 t u) = convexJoin 𝕜 t (convexJoin 𝕜 s u) := by
  simp_rw [← convexJoin_assoc, convexJoin_comm]

theorem convexJoin_right_comm (s t u : Set E) :
    convexJoin 𝕜 (convexJoin 𝕜 s t) u = convexJoin 𝕜 (convexJoin 𝕜 s u) t := by
  simp_rw [convexJoin_assoc, convexJoin_comm]

theorem convexJoin_convexJoin_convexJoin_comm (s t u v : Set E) :
    convexJoin 𝕜 (convexJoin 𝕜 s t) (convexJoin 𝕜 u v) =
      convexJoin 𝕜 (convexJoin 𝕜 s u) (convexJoin 𝕜 t v) := by
  simp_rw [← convexJoin_assoc, convexJoin_right_comm]

protected theorem IsConvexSet.convexJoin (hs : IsConvexSet 𝕜 s) (ht : IsConvexSet 𝕜 t) :
    IsConvexSet 𝕜 (convexJoin 𝕜 s t) := by
  refine IsConvexSet.of_convexCombPair_mem fun a b ha hb hab z₁ hz₁ z₂ hz₂ => ?_
  simp only [convexJoin, mem_iUnion, exists_prop] at hz₁ hz₂ ⊢
  obtain ⟨x₁, hx₁, y₁, hy₁, ⟨a₁, b₁, ha₁, hb₁, hab₁, rfl⟩⟩ := hz₁
  obtain ⟨x₂, hx₂, y₂ , hy₂, ⟨a₂, b₂, ha₂, hb₂, hab₂, rfl⟩⟩ := hz₂
  rw [convexCombPair_convexCombPair_convexCombPair_comm ha hb hab ha₁ hb₁ hab₁ ha₂ hb₂ hab₂]
  exact ⟨_, hs.iConvexComb_mem (by simp [hx₁, hx₂]),
    _, ht.iConvexComb_mem (by simp [hy₁, hy₂]),
    convexCombPair_mem_Icc (by positivity) (by positivity) (by grind)⟩

protected theorem IsConvexSet.convexHull_union (hs : IsConvexSet 𝕜 s) (ht : IsConvexSet 𝕜 t)
    (hs₀ : s.Nonempty) (ht₀ : t.Nonempty) : convexHull 𝕜 (s ∪ t) = convexJoin 𝕜 s t :=
  (convexHull_min (union_subset (subset_convexJoin_left ht₀) <| subset_convexJoin_right hs₀) <|
        hs.convexJoin ht).antisymm <|
    convexJoin_subset_convexHull _ _

theorem convexHull_union (hs : s.Nonempty) (ht : t.Nonempty) :
    convexHull 𝕜 (s ∪ t) = convexJoin 𝕜 (convexHull 𝕜 s) (convexHull 𝕜 t) := by
  rw [← convexHull_convexHull_union, ← convexHull_union_convexHull]
  apply IsConvexSet.convexHull.convexHull_union IsConvexSet.convexHull (convexHull_nonempty.mpr hs)
  exact (convexHull_nonempty.mpr ht)

theorem convexHull_insert (hs : s.Nonempty) :
    convexHull 𝕜 (insert x s) = convexJoin 𝕜 {x} (convexHull 𝕜 s) := by
  rw [insert_eq, convexHull_union (singleton_nonempty _) hs, convexHull_singleton]

theorem convexJoin_Iccs (a b c d : E) :
    convexJoin 𝕜 (Icc 𝕜 a b) (Icc 𝕜 c d) = convexHull 𝕜 {a, b, c, d} := by
  simp_rw [convexHull_insert (insert_nonempty _ _), convexHull_insert (singleton_nonempty _),
    convexHull_singleton, convexJoin_singletons, ← convexJoin_assoc,convexJoin_singletons]

theorem convexJoin_Icc_singleton (a b c : E) :
    convexJoin 𝕜 (Icc 𝕜 a b) {c} = convexHull 𝕜 {a, b, c} := by
  rw [← pair_eq_singleton, ← convexJoin_Iccs, Icc_self, pair_eq_singleton]

theorem convexJoin_singleton_Icc (a b c : E) :
    convexJoin 𝕜 {a} (Icc 𝕜 b c) = convexHull 𝕜 {a, b, c} := by
  rw [← Icc_self 𝕜, convexJoin_Iccs, insert_idem]

end LinearOrderedField

end Convexity
