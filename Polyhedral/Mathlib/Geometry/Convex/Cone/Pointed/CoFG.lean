import Polyhedral.Mathlib.Algebra.Module.Submodule.CoFG
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Dual

namespace PointedCone

open Module Function

variable {R M N : Type*}
variable [CommRing R] [PartialOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R} -- bilinear pairing

variable (p) in
/-- A cone is `CoFG` (co-finitely generated) if it is the dual of a finite set.
  This is in analogy to `FG` (finitely generated) which is the span of a finite set. -/
def CoFG (C : PointedCone R N) : Prop := ∃ s : Finset M, dual p s = C

/-- A CoFG cone is the dual of a finite set. -/
lemma CoFG.exists_finset_dual {C : PointedCone R N} (hC : C.CoFG p) :
    ∃ s : Finset M, dual p s = C := by
  obtain ⟨s, hs⟩ := hC; use s

/-- A CoFG cone is the dual of a finite set. -/
lemma CoFG.exists_finite_dual {C : PointedCone R N} (hC : C.CoFG p) :
    ∃ s : Set M, s.Finite ∧ dual p s = C := by
  obtain ⟨s, hs⟩ := hC; exact ⟨s, s.finite_toSet, hs⟩

/-- A CoFG cone is the dual of an FG cone. -/
lemma CoFG.exists_fg_dual {C : PointedCone R N} (hC : C.CoFG p) :
    ∃ D : PointedCone R M, D.FG ∧ dual p D = C := by
  obtain ⟨s, hs⟩ := hC; exact ⟨_, Submodule.fg_span s.finite_toSet, by simp [hs]⟩

/-- A CoFG cone is CoFG w.r.t. the standard pairing. -/
lemma CoFG.to_id {C : PointedCone R N} (hC : C.CoFG p) : C.CoFG .id
    := by classical
  obtain ⟨s, hs⟩ := hC
  use Finset.image p s
  simp [← dual_id, hs]

variable (p) in
/-- The dual of a `Finset` is co-FG. -/
lemma cofg_of_finset (s : Finset M) : (dual p s).CoFG p := by use s

variable (p) in
/-- The dual of a finite set is co-FG. -/
lemma cofg_of_finite {s : Set M} (hs : s.Finite) : (dual p s).CoFG p := by
  use hs.toFinset; simp

variable (p) in
/-- The dual of an FG-cone is co-FG. -/
lemma cofg_of_fg {C : PointedCone R M} (hC : C.FG) : (dual p C).CoFG p := by
  obtain ⟨s, rfl⟩ := hC
  use s; rw [← dual_span]

alias FG.dual_cofg := cofg_of_fg

/-- The intersection of two CoFG cones i CoFG. -/
lemma inf_cofg {C D : PointedCone R N} (hC : C.CoFG p) (hD : D.CoFG p) :
    (C ⊓ D).CoFG p := by classical
  obtain ⟨S, rfl⟩ := hC
  obtain ⟨T, rfl⟩ := hD
  use S ∪ T; rw [Finset.coe_union, dual_union]

/-- The double dual of a CoFG cone is the cone itself. -/
@[simp]
lemma CoFG.dual_dual_flip {C : PointedCone R N} (hC : C.CoFG p) :
    dual p (dual p.flip C) = C := by
  obtain ⟨D, hcofg, rfl⟩ := exists_fg_dual hC
  exact dual_dual_flip_dual (p := p) D

/-- The double dual of a CoFG cone is the cone itself. -/
@[simp]
lemma CoFG.dual_flip_dual {C : PointedCone R M} (hC : C.CoFG p.flip) :
    dual p.flip (dual p C) = C := hC.dual_dual_flip

lemma CoFG.isDualClosed {C : PointedCone R M} (hC : C.CoFG p.flip) :
    C.IsDualClosed p := hC.dual_flip_dual

lemma CoFG.isDualClosed_flip {C : PointedCone R N} (hC : C.CoFG p) :
    C.IsDualClosed p.flip := hC.dual_dual_flip

-----

section LinearOrder

variable {R M N : Type*}
variable [CommRing R] [LinearOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R} -- bilinear pairing

lemma CoFG.coe {S : Submodule R N} (hS : S.CoFG p) : (S : PointedCone R N).CoFG p := by
  obtain ⟨T, hfg, rfl⟩ := hS.exists_fg_dual
  rw [← coe_dual]
  exact cofg_of_fg p (coe_fg hfg)

alias coe_cofg := CoFG.coe

-- Q: is this problematic?
instance {S : Submodule R N} : Coe (S.CoFG p) (CoFG p (S : PointedCone R N)) := ⟨coe_cofg⟩

@[simp] lemma coe_cofg_iff {S : Submodule R N} :
    (S : PointedCone R N).CoFG p ↔ S.CoFG p := by -- classical
  -- unfold CoFG Submodule.CoFG
  constructor
  · intro hcofg
    obtain ⟨s, hs⟩ := hcofg
    use s
    sorry
  · exact coe_cofg

end LinearOrder

-- ### HIGH PRIORITY! This is needed in the Field theory!
lemma CoFG.lineal_cofg {C : PointedCone R N} (hC : C.CoFG p) : C.lineal.CoFG p := by
  sorry

@[deprecated]
lemma CoFG.dual_inf_dual_sup_dual {C D : PointedCone R N} (hC : C.CoFG p) (hD : D.CoFG p) :
    dual p.flip (C ⊓ D : PointedCone R N) = (dual p.flip C) ⊔ (dual p.flip D) := by
  have ⟨C', hCfg, hC'⟩ := CoFG.exists_fg_dual hC
  have ⟨D', hDfg, hD'⟩ := CoFG.exists_fg_dual hD
  rw [← hC', ← hD', ← dual_sup_dual_inf_dual]
  rw [dual_flip_dual (by sorry)] -- not true
  rw [dual_flip_dual (by sorry)] -- not true
  rw [dual_flip_dual (by sorry)] -- not true
  -- Maybe we can prove this only with Field (need dual_dual for FG; need p.IsFaithfulPair?)

end PointedCone
