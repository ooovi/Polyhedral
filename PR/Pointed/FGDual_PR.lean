
import Mathlib.Algebra.Module.Submodule.Pointwise
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.Geometry.Convex.Cone.Dual

import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.Geometry.Convex.Cone.Dual
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Mathlib.Algebra.Module.Submodule.Pointwise
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.SetTheory.Cardinal.Defs

-- import Polyhedral.PR.DualFG.FGDual_PR
-- import Polyhedral.PR.Pointed.Dual_PR

namespace PointedCone

open Module Function

variable {R M N : Type*}
variable [CommRing R] [PartialOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R} -- bilinear pairing

-- TODO: rename `DualFG` to `DualFG` everywhere

variable (p) in
/-- A cone is `DualFG` if it is the dual of a finite set.
  This is in analogy to `FG` (finitely generated) which is the span of a finite set. -/
def DualFG (C : PointedCone R N) : Prop := ∃ s : Finset M, dual p s = C

lemma DualFG.top : DualFG p ⊤ := ⟨∅, by simp⟩

section

variable {R M N : Type*}
variable [CommRing R] [LinearOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R} -- bilinear pairing

variable [Module.Finite R M] [Fact p.SeparatingLeft] in
lemma DualFG.bot : DualFG p ⊥ := by
  have h := Module.Finite.fg_top (R := R) (M := M)
  have h := coe_fg h
  obtain ⟨s, hs⟩ := h
  use s
  rw [← dual_span, span, hs]
  -- exact dual_univ
  sorry

end

/-- A DualFG cone is the dual of a finite set. -/
lemma DualFG.exists_finset_dual {C : PointedCone R N} (hC : C.DualFG p) :
    ∃ s : Finset M, dual p s = C := by
  obtain ⟨s, hs⟩ := hC; use s

/-- A DualFG cone is the dual of a finite set. -/
lemma DualFG.exists_finite_dual {C : PointedCone R N} (hC : C.DualFG p) :
    ∃ s : Set M, s.Finite ∧ dual p s = C := by
  obtain ⟨s, hs⟩ := hC; exact ⟨s, s.finite_toSet, hs⟩

/-- A DualFG cone is the dual of an FG cone. -/
lemma DualFG.exists_fg_dual {C : PointedCone R N} (hC : C.DualFG p) :
    ∃ D : PointedCone R M, D.FG ∧ dual p D = C := by
  obtain ⟨s, hs⟩ := hC; exact ⟨_, Submodule.fg_span s.finite_toSet, by simp [hs]⟩

/-- A DualFG cone is DualFG w.r.t. the standard pairing. -/
lemma DualFG.to_id {C : PointedCone R N} (hC : C.DualFG p) : C.DualFG .id
    := by classical
  obtain ⟨s, hs⟩ := hC
  use Finset.image p s
  simp [← dual_id, hs]

variable (p) in
/-- The dual of a `Finset` is co-FG. -/
lemma dualfg_of_finset (s : Finset M) : (dual p s).DualFG p := by use s

variable (p) in
/-- The dual of a finite set is co-FG. -/
lemma dualfg_of_finite {s : Set M} (hs : s.Finite) : (dual p s).DualFG p := by
  use hs.toFinset; simp

variable (p) in
/-- The dual of an FG-cone is co-FG. -/
lemma dual_of_fg {C : PointedCone R M} (hC : C.FG) : (dual p C).DualFG p := by
  obtain ⟨s, rfl⟩ := hC
  use s; rw [← dual_span]

alias FG.dual_dualfg := dual_of_fg

/-- The intersection of two DualFG cones i DualFG. -/
lemma inf_dualfg {C D : PointedCone R N} (hC : C.DualFG p) (hD : D.DualFG p) :
    (C ⊓ D).DualFG p := by classical
  obtain ⟨S, rfl⟩ := hC; obtain ⟨T, rfl⟩ := hD
  use S ∪ T; rw [Finset.coe_union, dual_union]

/-- The double dual of a DualFG cone is the cone itself. -/
@[simp]
lemma DualFG.dual_dual_flip {C : PointedCone R N} (hC : C.DualFG p) :
    dual p (dual p.flip C) = C := by
  obtain ⟨D, hdualfg, rfl⟩ := exists_fg_dual hC
  exact dual_dual_flip_dual (p := p) D

/-- The double dual of a DualFG cone is the cone itself. -/
@[simp]
lemma DualFG.dual_flip_dual {C : PointedCone R M} (hC : C.DualFG p.flip) :
    dual p.flip (dual p C) = C := hC.dual_dual_flip

lemma DualFG.dualClosed {C : PointedCone R M} (hC : C.DualFG p.flip) :
    C.DualClosed p := hC.dual_flip_dual

lemma DualFG.dualClosed_flip {C : PointedCone R N} (hC : C.DualFG p) :
    C.DualClosed p.flip := hC.dual_dual_flip

-----

section LinearOrder

variable {R M N : Type*}
variable [CommRing R] [LinearOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R} -- bilinear pairing

lemma DualFG.coe {S : Submodule R N} (hS : S.DualFG p) : (S : PointedCone R N).DualFG p := by
  obtain ⟨T, hfg, rfl⟩ := hS.exists_fg_dual
  rw [← coe_dual]
  exact dual_of_fg p (coe_fg hfg)

alias coe_dualfg := DualFG.coe

-- Q: is this problematic?
instance {S : Submodule R N} : Coe (S.DualFG p) (DualFG p (S : PointedCone R N)) := ⟨coe_dualfg⟩

@[simp] lemma coe_dualfg_iff {S : Submodule R N} :
    (S : PointedCone R N).DualFG p ↔ S.DualFG p := by -- classical
  -- unfold DualFG Submodule.DualFG
  constructor
  · intro hdualfg
    obtain ⟨s, hs⟩ := hdualfg
    use s
    sorry
  · exact coe_dualfg

lemma DualFG.lineal_dualfg {C : PointedCone R N} (hC : C.DualFG p) : C.lineal.DualFG p := by
  obtain ⟨D, hfg, rfl⟩ := hC.exists_fg_dual
  rw [dual_span_lineal_dual, ← Submodule.dual_span]
  exact Submodule.dual_of_fg p (submodule_span_fg hfg)

end LinearOrder

@[deprecated]
lemma DualFG.dual_inf_dual_sup_dual' {C D : PointedCone R N} (hC : C.DualFG p) (hD : D.DualFG p) :
    dual p.flip (C ⊓ D : PointedCone R N) = (dual p.flip C) ⊔ (dual p.flip D) := by
  have ⟨C', hCfg, hC'⟩ := DualFG.exists_fg_dual hC
  have ⟨D', hDfg, hD'⟩ := DualFG.exists_fg_dual hD
  rw [← hC', ← hD', ← dual_sup_dual_inf_dual]
  rw [dual_flip_dual (by sorry)] -- not true
  rw [dual_flip_dual (by sorry)] -- not true
  rw [dual_flip_dual (by sorry)] -- not true
  -- Maybe we can prove this only with Field (need dual_dual for FG; need p.IsFaithfulPair?)

end PointedCone
