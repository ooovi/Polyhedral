/-
Copyright (c) 2026 Vlad Tsyrklevich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vlad Tsyrklevich
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.Dimension
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-! Finite-dimensional affine space lemmas -/

@[expose] public section

open Affine

section AffineSpace'

variable (k : Type*) {V : Type*} {P : Type*}

open AffineSubspace Module

variable [DivisionRing k] [AddCommGroup V] [Module k V] [AffineSpace V P]

variable {k}

theorem AffineIndepOn.ncard_eq_succ_finDim_affineSpan {s : Set P} (hai : AffineIndepOn k id s)
    [hf : FiniteDimensional k (vectorSpan k s)] : s.ncard = (affineSpan k s).finDim.succ := by
  rcases Set.eq_empty_or_nonempty s with rfl | hs
  · simp
  rw [← Subtype.range_coe (s := s)] at hf
  have := finiteDimensional_iff_setFinite k hai |>.mp hf
  have := hai.finrank_vectorSpan this hs
  rw [finDim_eq_finrank (by simp [Set.nonempty_iff_ne_empty.mp hs]), direction_affineSpan,
    WithBot.succ_natCast, this]
  grind only [Set.ncard_eq_zero, Set.not_nonempty_empty]

theorem AffineIndependent.ncard_eq_succ_finDim_affineSpan {s : Set P}
    (hai : AffineIndependent k ((↑) : s → P)) [hf : FiniteDimensional k (vectorSpan k s)] :
    s.ncard = (affineSpan k s).finDim.succ :=
  AffineIndepOn.ncard_eq_succ_finDim_affineSpan ((affineIndependent_subtype_iff _).mp hai)

variable (k)

variable (V) in
theorem exists_affineIndependent_of_finiteDimensional (s : Set P)
    [F : FiniteDimensional k (vectorSpan k s)] :
    ∃ t ⊆ s, affineSpan k t = affineSpan k s ∧ AffineIndependent k ((↑) : t → P) ∧
      t.ncard = (affineSpan k s).finDim.succ := by
  obtain ⟨t, ht₁, ht₂, ht₃⟩ := exists_affineIndependent k V s
  refine ⟨t, ht₁, ht₂, ht₃, ?_⟩
  rw [← direction_affineSpan, ← ht₂, direction_affineSpan] at F
  exact ht₂ ▸ ht₃.ncard_eq_succ_finDim_affineSpan

variable (V) in
theorem exists_affineIndepOn_of_finiteDimensional (s : Set P)
    [F : FiniteDimensional k (vectorSpan k s)] :
    ∃ t ⊆ s, affineSpan k t = affineSpan k s ∧ AffineIndepOn k id t ∧
      t.ncard = (affineSpan k s).finDim.succ :=
  exists_affineIndependent_of_finiteDimensional k V s

end AffineSpace'
