import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

namespace Affine

section Ring

variable (R : Type*) [Ring R]
variable {V : Type*} [AddCommGroup V] [Module R V]
variable {A : Type*} [AddTorsor V A]

noncomputable def rank (s : Set A) := Module.rank R (affineSpan R s).direction

noncomputable def finrank (s : Set A) := Module.finrank R (affineSpan R s).direction

@[gcongr]
lemma spanPoints_mono (F G : Set A) (hFG : G < F) : spanPoints R G ⊆ spanPoints R F := by
    exact fun p ⟨p₁, hp₁, v, hv, hp⟩ =>
      ⟨p₁, hFG.le hp₁, v, Submodule.span_mono (Set.vsub_subset_vsub hFG.le hFG.le) hv, hp⟩

end Ring

end Affine
