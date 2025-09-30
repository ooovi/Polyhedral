import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.RingTheory.Finiteness.Basic

namespace Submodule

lemma restrictedScalars_FG_of_FG {E S R : Type*} [Semiring R] [Semiring S]
  [AddCommMonoid E] [Module R S] [Module R E] [Module S E] [IsScalarTower R S E]
  [Module.Finite R S] {s : Submodule S E} (hfin : s.FG) : (s.restrictScalars R).FG := by
  rw [← Module.Finite.iff_fg] at *
  exact Module.Finite.trans S s

end Submodule

namespace PointedCone
variable {𝕜 E : Type*} [Semiring 𝕜] [PartialOrder 𝕜] [IsOrderedRing 𝕜] [AddCommMonoid E]
  [Module 𝕜 E] {S : Set E}

variable (𝕜 S) in
/-- The span of a set `S` is the smallest pointed cone that contains `S`.

Pointed cones being defined as submodules over nonnegative scalars, this is exactly the
submodule span of `S` w.r.t. nonnegative scalars. -/
abbrev span : PointedCone 𝕜 E := Submodule.span _ S

lemma subset_span : S ⊆ PointedCone.span 𝕜 S := Submodule.subset_span

abbrev ofSubmodule (S : Submodule 𝕜 E) : PointedCone 𝕜 E := S.restrictScalars _

instance : Coe (Submodule 𝕜 E) (PointedCone 𝕜 E) := ⟨ ofSubmodule ⟩

lemma ofSubmodule.carrier_eq (S : Submodule 𝕜 E) : (ofSubmodule S : Set E) = S :=
  Submodule.coe_restrictScalars 𝕜 S

variable {𝕜 E : Type*} [Ring 𝕜] [LinearOrder 𝕜] [IsOrderedRing 𝕜] [AddCommGroup E]
  [Module 𝕜 E]

lemma ofSubmodule.FG_of_FG {S : Submodule 𝕜 E} (hS : S.FG) : (S : PointedCone 𝕜 E).FG
    := Submodule.restrictedScalars_FG_of_FG hS

end PointedCone
