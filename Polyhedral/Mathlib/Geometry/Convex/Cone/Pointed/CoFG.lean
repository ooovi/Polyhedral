
import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.Geometry.Convex.Cone.Dual
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Mathlib.Algebra.Module.Submodule.Pointwise

import Polyhedral.Mathlib.Algebra.Module.Submodule.Basic
import Polyhedral.Mathlib.Algebra.Module.Submodule.CoFG
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Basic

namespace PointedCone

open Module

variable {R M N : Type*}
variable [CommRing R] [PartialOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R} -- bilinear pairing

def CoFG (C : PointedCone R M) : Prop :=
  ∃ s : Finset (Dual R M), dual .id s = C

variable (p)

/-- The dual of a `Finset` is co-FG. -/
lemma cofg_of_finset (s : Finset M) : (dual p s).CoFG := by
  classical
  use Finset.image p s
  simp [dual_bilin_dual_id]

/-- The dual of a finite set is co-FG. -/
lemma cofg_of_finite {s : Set M} (hs : s.Finite) : (dual p s).CoFG := by
  classical
  use Finset.image p hs.toFinset
  simp [dual_bilin_dual_id]

/-- The dual of an FG-cone is co-FG. -/
lemma cofg_of_fg {C : PointedCone R M} (hC : C.FG) : (dual p C).CoFG := by
  obtain ⟨s, hs⟩ := hC
  rw [← hs, dual_span]
  exact cofg_of_finset p _

section IsPerfPair

variable {R M F : Type*}
variable [CommRing R] [PartialOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup F] [Module R F]
variable {p : M →ₗ[R] F →ₗ[R] R} [p.IsPerfPair]

open Function

variable (p)

/- TODO: all theorems in this section only need that `p.flip` is surjective
  rather than full `p.IsPerfPair`. Perhaps implement this when typeclasses are
  available ? -/

lemma CoFG.exists_finset_dual {C : PointedCone R M} (hC : C.CoFG) :
    ∃ s : Finset F, dual p.flip s = C := by
  classical
  obtain ⟨s, rfl⟩ := hC
  use s.image <| surjInv (LinearMap.IsPerfPair.bijective_right p).surjective
  rw [Finset.coe_image, dual_bilin_dual_id, ← Set.image_comp, comp_surjInv, Set.image_id]

lemma CoFG.exists_finite_dual {C : PointedCone R M} (hC : C.CoFG) :
    ∃ s : Set F, s.Finite ∧ dual p.flip s = C := by
  obtain ⟨s, rfl⟩ := exists_finset_dual (p := p) hC
  use s; simp

lemma CoFG.exists_fg_dual {C : PointedCone R M} (hC : C.CoFG) :
    ∃ S : PointedCone R F, S.FG ∧ dual p.flip S = C := by
  obtain ⟨s, rfl⟩ := exists_finset_dual (p := p) hC
  use span R s; simp; use s

end IsPerfPair

----------

lemma cofg_inf {C D : PointedCone R M} (hC : C.CoFG) (hD : D.CoFG) : (C ⊓ D).CoFG := by
  classical
  obtain ⟨S, rfl⟩ := hC
  obtain ⟨T, rfl⟩ := hD
  use S ∪ T
  rw [Finset.coe_union, dual_union]

@[simp]
lemma coe_cofg {S : Submodule R M} :
    (S : PointedCone R M).CoFG ↔ S.CoFG := by
  classical
  unfold CoFG Submodule.CoFG
  -- obtain ⟨A, hA⟩ := hcofg
  -- use (A.toSet ∪ -A.toSet).toFinset _
  sorry

end PointedCone
