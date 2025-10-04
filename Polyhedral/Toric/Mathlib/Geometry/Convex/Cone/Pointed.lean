
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

section Map

variable {E' : Type*} [AddCommMonoid E'] [Module R E']

lemma map_span (f : E →ₗ[R] E') (s : Set E) : map f (span R s) = span R (f '' s) := by
  -- use `Submodule.map_span f s`
  sorry

open Module

variable {R : Type*} [CommRing R] [PartialOrder R] [IsOrderedRing R]
variable {E F E' F' : Type*}
  [AddCommGroup E] [Module R E]
  [AddCommGroup F] [Module R F]
  [AddCommGroup E'] [Module R E']
  [AddCommGroup F'] [Module R F']
  -- {p' : E' →ₗ[R] F' →ₗ[R] R}

variable (f : E →ₗ[R] E')

lemma map_dual (C : PointedCone R E) :
    dual (Dual.eval R E') (map f C) = comap f.dualMap (dual (Dual.eval R E) C) := by
  ext x; simp

end Map


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

lemma cofg_inter (C D : PointedCone R E) (hC : C.CoFG) (hD : D.CoFG) : (C ⊓ D).CoFG := by
  classical
  obtain ⟨S, rfl⟩ := hC
  obtain ⟨T, rfl⟩ := hD
  use S ∪ T
  rw [Finset.coe_union, dual_union]

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

/-- The lineality space of a cone. -/
def lineal (C : PointedCone R E) := sSup {S : Submodule R E | S ≤ C }

/-- A pointy cone has trivial lineality space. -/
def IsPointy (C : PointedCone R E) := C.lineal = ⊥

lemma foo {C : PointedCone R E} {x y : E} (hx : x ∈ C.lineal) (hy : y ∉ C.lineal) :
    x + y ∉ C.lineal := by
  sorry

lemma span_inter_lineal_eq_lineal {C : PointedCone R E} {s : Set E} (h : span R s = C) :
    span R (s ∩ C.lineal) = C.lineal := by
  rw [← antisymm_iff (r := LE.le)]
  constructor
  · rw [← Submodule.span_eq (C.lineal : PointedCone R E)]
    exact Submodule.span_mono (by simp)
  · rw [← SetLike.coe_subset_coe]
    rw [Set.subset_def]
    intro x hx
    let S:= s ∩ C.lineal
    let S' := s \ C.lineal
    have hS : S ∪ S' = s := by simp [S, S']
    have hS' : S ∩ S' = ∅ := by aesop

    --have hs : s = (s ∩ C.lineal) ∪ ()
    -- rw [Submodule.mem_span_finite_of_mem_span] at h
    sorry

lemma span_diff_lineal_pointy {C : PointedCone R E} {s : Set E} (h : span R s = C) :
    (span R (s \ C.lineal)).IsPointy := by
  sorry

open Module

/-- A cone is a sum of a pointed cone and its lineality space. -/
-- NOTE: I just realzed that this is true in a boring sense: let D := span C \ C.lineal ∪ {0}
lemma exists_pointy_sup_lineal (C : PointedCone R E) :
    ∃ D : PointedCone R E, D.IsPointy ∧ D ⊔ C.lineal = C := by
  have hT : ∃ T : Submodule R E, IsCompl C.lineal T := sorry
    -- Submodule.exists_isCompl (K := R) (V := E) C.lineal
  obtain ⟨CoLin, h⟩ := hT
  use (C ⊓ CoLin)
  constructor
  · sorry
  · sorry

/-- A cone is a sum of a pointed cone and its lineality space. -/
-- NOTE: I just realzed that this is true in a boring sense: let D := span C \ C.lineal ∪ {0}
lemma exists_pointy_sup_lineal' (C : PointedCone R E) :
    ∃ D : PointedCone R E, (Submodule.span R D) ⊓ C.lineal = ⊥ ∧ D ⊔ C.lineal = C := by

  sorry

end PointedCone
