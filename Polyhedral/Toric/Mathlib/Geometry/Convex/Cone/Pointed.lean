
import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.Geometry.Convex.Cone.Dual
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.LinearAlgebra.PerfectPairing.Basic

import Polyhedral.Toric.Mathlib.Geometry.Convex.Cone.Submodule

namespace PointedCone

variable {R E : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R] [AddCommMonoid E]
  [Module R E] {S : Set E}

variable (R S) in
/-- The span of a set `S` is the smallest pointed cone that contains `S`.

Pointed cones being defined as submodules over nonnegative scalars, this is exactly the
submodule span of `S` w.r.t. nonnegative scalars. -/
abbrev span : PointedCone R E := Submodule.span _ S

lemma subset_span : S ⊆ PointedCone.span R S := Submodule.subset_span

abbrev ofSubmodule (S : Submodule R E) : PointedCone R E := S.restrictScalars _

instance : Coe (Submodule R E) (PointedCone R E) := ⟨ ofSubmodule ⟩

lemma ofSubmodule.carrier_eq (S : Submodule R E) : (ofSubmodule S : Set E) = S :=
  Submodule.coe_restrictScalars R S

variable {R E : Type*} [Ring R] [LinearOrder R] [IsOrderedRing R] [AddCommGroup E]
  [Module R E]

lemma ofSubmodule.FG_of_FG {S : Submodule R E} (hS : S.FG) : (S : PointedCone R E).FG
    := Submodule.restrictedScalars_FG_of_FG hS

lemma fg_top [Module.Finite R E] : (⊤ : PointedCone R E).FG :=
  ofSubmodule.FG_of_FG Module.Finite.fg_top

/- Duality -/

variable {R F : Type*} [CommRing R] [PartialOrder R] [IsOrderedRing R]
  [Module R E] [AddCommGroup F] [Module R F] {p : E →ₗ[R] F →ₗ[R] R}

alias dual_bot := dual_zero

-- TODO: are there instances missing that should make this automatic?
-- TODO: 0 in `dual_univ` simplifies to ⊥, so maybe it is not the best statement?
lemma dual_top [p.IsPerfPair] : dual p .univ = ⊥
  := dual_univ (LinearMap.IsPerfPair.bijective_right p).1

#check dual_union

-- lemma span_sup (C C' : PointedCone R E) :
--     span (C ⊔ C' : PointedCone R E) = span (C ∪ C') := sorry

lemma dual_coe (C C' : PointedCone R E) :
    dual p (C ⊔ C' : PointedCone R E) = dual p (C ∪ C') := sorry

lemma dual_sup (C C' : PointedCone R E) :
    PointedCone.dual p (C ⊔ C' : PointedCone R E)
      = PointedCone.dual p C ⊓ PointedCone.dual p C' := by

  -- dual_union _ _
  sorry

example (C C' : PointedCone R E) :
    PointedCone.dual p (C ⊔ C') = PointedCone.dual p (C ∪ C') := rfl

-- lemma span_sup (C C' : PointedCone R E) :
--     span (C ⊔ C' : PointedCone R E) = span (C ∪ C') := sorry

-- lemma dual_sup (C C' : PointedCone R E) :
--     PointedCone.dual p (C ⊔ C') = PointedCone.dual p C ⊓ PointedCone.dual p C'
--   := dual_union _ _

end PointedCone
