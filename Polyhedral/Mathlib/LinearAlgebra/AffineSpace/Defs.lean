/-
Copyright (c) 2026 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/

import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! This file proves results about affine spans. -/

namespace Affine

section Ring

variable (R : Type*) [Ring R]
variable {V : Type*} [AddCommGroup V] [Module R V]
variable {A : Type*} [AddTorsor V A]

lemma spanPoints_empty : spanPoints R (∅ : Set A) = ∅ := by simp [spanPoints]

@[gcongr]
lemma spanPoints_mono {F G : Set A} (hFG : G ⊆ F) : spanPoints R G ⊆ spanPoints R F :=
  fun _p ⟨p₁, hp₁, v, hv, hp⟩ =>
    ⟨p₁, hFG hp₁, v, Submodule.span_mono (Set.vsub_subset_vsub hFG hFG) hv, hp⟩

lemma spanPoints_monotone : Monotone (spanPoints R : Set A → Set A) :=
  fun _ _ => spanPoints_mono R

noncomputable def rank (s : Set A) := Module.rank R (affineSpan R s).direction

noncomputable def finrank (s : Set A) := Module.finrank R (affineSpan R s).direction

lemma finrank_empty : finrank R (A := A) ∅ = 0 := by
  simp [finrank, affineSpan, AffineSubspace.direction]
  have : vectorSpan R (spanPoints R ∅ : Set V) = ⊥ := sorry
  sorry

end Ring

end Affine
