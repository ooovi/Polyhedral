
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

/-- Polar duality on cones. -/
alias polar := dual

variable {R F : Type*} [CommRing R] [PartialOrder R] [IsOrderedRing R]
  [Module R E] [AddCommGroup F] [Module R F] {p : E →ₗ[R] F →ₗ[R] R}

@[simp]
lemma polar_eq_dual (S : Submodule R E) : polar p S = Submodule.dual p S := by
  ext x; constructor
  · intro h _ ha
    have h' := h (neg_mem_iff.mpr ha)
    simp at h'
    exact le_antisymm (h ha) h'
  · intro h _ ha
    rw [h ha]

def CoFG (N : PointedCone R E) : Prop :=
  ∃ S : Finset (Module.Dual R E), dual .id S = N

alias dual_bot := dual_zero

-- TODO: are there instances missing that should make the proof automatic?
-- TODO: 0 in `dual_univ` simplifies to ⊥, so maybe it is not the best statement?
@[simp] lemma dual_top [p.IsPerfPair] : dual p .univ = ⊥
  := dual_univ (LinearMap.IsPerfPair.bijective_right p).1

example /- dual_inf -/ (C C' : PointedCone R E) :
    dual p (C ⊓ C' : PointedCone R E) = dual p (C ∩ C') := rfl
example (C C' : PointedCone R E) : dual p (C ⊔ C') = dual p (C ∪ C') := rfl

lemma dual_sup (C C' : PointedCone R E) : dual p (C ⊔ C' : PointedCone R E) = dual p (C ∪ C')
  := by nth_rw 2 [←dual_span]; rw [Submodule.span_union']

-- TODO: simp lemma?
lemma dual_sup_dual_inf_dual (C C' : PointedCone R E) :
    dual p (C ⊔ C' : PointedCone R E) = dual p C ⊓ dual p C' := by rw [dual_sup, dual_union]

-- TODO: Does this even hold in general? Certainly if C and C' are CoFG.
-- @[simp] lemma dual_flip_dual_union
example {C C' : PointedCone R E} : -- (hC : C.FG) (hC' : C'.FG) :
    dual p.flip (dual p (C ∪ C')) = C ⊔ C' := by
  sorry

/-- The linearlity space of a cone. -/
def lineal (C : PointedCone R E) := sSup {S : Submodule R E | S ≤ C }

/-- A pointy cone has trivial lineality space. -/
def IsPointy (C : PointedCone R E) := C.lineal = ⊥

/-- A cone is a sum of a pointed cone and its lineality space. -/
lemma exists_pointy_sup_lineal (C : PointedCone R E) :
    ∃ D : PointedCone R E, D.IsPointy ∧ D ⊔ C.lineal = C := by
  sorry

end PointedCone
