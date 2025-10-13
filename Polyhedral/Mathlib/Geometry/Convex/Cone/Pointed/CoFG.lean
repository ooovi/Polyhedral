
import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.Geometry.Convex.Cone.Dual
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Mathlib.Algebra.Module.Submodule.Pointwise

import Polyhedral.Mathlib.Algebra.Module.Submodule.Basic
import Polyhedral.Mathlib.Algebra.Module.Submodule.CoFG
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Basic
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Dual

namespace PointedCone

open Module Function

variable {R M N : Type*}
variable [CommRing R] [PartialOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R} -- bilinear pairing

/-- A cone is `CoFG` (co-finitely generated) if it is the dual of a finite set.
  This is in analogy to `FG` (finitely generated) which is the span of afinite set. -/
def CoFG (C : PointedCone R M) : Prop := ∃ s : Finset (Dual R M), dual .id s = C

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

section Surjective

variable {R M N : Type*}
variable [CommRing R] [PartialOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}

-- NOTE: Most theory of CoFG relies on the fact that `p.flip` is surjective. This is the
--  case, for example, if `p.IsPerfPair`, or if `p := Dual.eval R M`.

instance : Fact (Surjective (.id : M →ₗ[R] M)) := ⟨surjective_id⟩

instance : Fact (Surjective (Dual.eval R M).flip) := ⟨surjective_id⟩

instance [p.IsPerfPair] : Fact (Surjective p)
    := ⟨(LinearMap.IsPerfPair.bijective_left p).surjective⟩

instance [p.IsPerfPair] : Fact (Surjective p.flip)
    := ⟨(LinearMap.IsPerfPair.bijective_right p).surjective⟩

instance [inst : Fact (Surjective p)] : Fact (Surjective p.flip.flip)
    := ⟨by rw [LinearMap.flip_flip]; exact inst.elim⟩

variable (p) [Fact (Surjective p.flip)]

lemma CoFG.exists_finset_dual {C : PointedCone R M} (hC : C.CoFG) :
    ∃ s : Finset N, dual p.flip s = C := by classical
  obtain ⟨s, rfl⟩ := hC
  use s.image <| surjInv <| Fact.elim <| inferInstanceAs <| Fact (Surjective p.flip)
  rw [Finset.coe_image, dual_bilin_dual_id, ← Set.image_comp, comp_surjInv, Set.image_id]

lemma CoFG.exists_finite_dual {C : PointedCone R M} (hC : C.CoFG) :
    ∃ s : Set N, s.Finite ∧ dual p.flip s = C := by
  obtain ⟨s, rfl⟩ := exists_finset_dual (p := p) hC
  use s; simp

lemma CoFG.exists_fg_dual {C : PointedCone R M} (hC : C.CoFG) :
    ∃ S : PointedCone R N, S.FG ∧ dual p.flip S = C := by
  obtain ⟨s, rfl⟩ := exists_finset_dual (p := p) hC
  use span R s; simp; use s

end Surjective

lemma cofg_inf {C D : PointedCone R M} (hC : C.CoFG) (hD : D.CoFG) :
    (C ⊓ D).CoFG := by classical
  obtain ⟨S, rfl⟩ := hC
  obtain ⟨T, rfl⟩ := hD
  use S ∪ T; rw [Finset.coe_union, dual_union]

@[simp]
lemma coe_cofg {S : Submodule R M} :
    (S : PointedCone R M).CoFG ↔ S.CoFG := by -- classical
  -- unfold CoFG Submodule.CoFG
  constructor
  · intro hcofg
    obtain ⟨s, hs⟩ := hcofg
    use s
    sorry
  · intro hcofg
    obtain ⟨s, hs⟩ := hcofg
    use s
    sorry

end PointedCone
