import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

namespace Affine

section Ring

variable (R : Type*) [Ring R]
variable {V : Type*} [AddCommGroup V] [Module R V]
variable {A : Type*} [AddTorsor V A]

lemma spanPoints_empty : spanPoints R (∅ : Set A) = ∅ := by simp [spanPoints]

@[gcongr]
lemma spanPoints_mono (F G : Set A) (hFG : G < F) : spanPoints R G ⊆ spanPoints R F := by
    exact fun p ⟨p₁, hp₁, v, hv, hp⟩ =>
      ⟨p₁, hFG.le hp₁, v, Submodule.span_mono (Set.vsub_subset_vsub hFG.le hFG.le) hv, hp⟩

noncomputable def rank (s : Set A) := Module.rank R (affineSpan R s).direction

noncomputable def finrank (s : Set A) := Module.finrank R (affineSpan R s).direction

lemma finrank_empty : finrank R (A := A) ∅ = 0 := by
  simp [finrank, affineSpan, AffineSubspace.direction]
  have : vectorSpan R (spanPoints R ∅ : Set V) = ⊥ := sorry
  sorry

end Ring

end Affine
