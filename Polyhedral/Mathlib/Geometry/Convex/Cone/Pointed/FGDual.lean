
import Polyhedral.Mathlib.Algebra.Module.Submodule.FGDual
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Dual

namespace PointedCone

open Module Function

variable {R M N : Type*}
variable [CommRing R] [PartialOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R} -- bilinear pairing

-- TODO: rename `FGDual` to `FGDual` everywhere

variable (p) in
/-- A cone is `FGDual` if it is the dual of a finite set.
  This is in analogy to `FG` (finitely generated) which is the span of a finite set. -/
def FGDual (C : PointedCone R N) : Prop := ∃ s : Finset M, dual p s = C

/-- A FGDual cone is the dual of a finite set. -/
lemma FGDual.exists_finset_dual {C : PointedCone R N} (hC : C.FGDual p) :
    ∃ s : Finset M, dual p s = C := by
  obtain ⟨s, hs⟩ := hC; use s

/-- A FGDual cone is the dual of a finite set. -/
lemma FGDual.exists_finite_dual {C : PointedCone R N} (hC : C.FGDual p) :
    ∃ s : Set M, s.Finite ∧ dual p s = C := by
  obtain ⟨s, hs⟩ := hC; exact ⟨s, s.finite_toSet, hs⟩

/-- A FGDual cone is the dual of an FG cone. -/
lemma FGDual.exists_fg_dual {C : PointedCone R N} (hC : C.FGDual p) :
    ∃ D : PointedCone R M, D.FG ∧ dual p D = C := by
  obtain ⟨s, hs⟩ := hC; exact ⟨_, Submodule.fg_span s.finite_toSet, by simp [hs]⟩

/-- A FGDual cone is FGDual w.r.t. the standard pairing. -/
lemma FGDual.to_id {C : PointedCone R N} (hC : C.FGDual p) : C.FGDual .id
    := by classical
  obtain ⟨s, hs⟩ := hC
  use Finset.image p s
  simp [← dual_id, hs]

variable (p) in
/-- The dual of a `Finset` is co-FG. -/
lemma fgdual_of_finset (s : Finset M) : (dual p s).FGDual p := by use s

variable (p) in
/-- The dual of a finite set is co-FG. -/
lemma fgdual_of_finite {s : Set M} (hs : s.Finite) : (dual p s).FGDual p := by
  use hs.toFinset; simp

variable (p) in
/-- The dual of an FG-cone is co-FG. -/
lemma fgdual_of_fg {C : PointedCone R M} (hC : C.FG) : (dual p C).FGDual p := by
  obtain ⟨s, rfl⟩ := hC
  use s; rw [← dual_span]

alias FG.dual_fgdual := fgdual_of_fg

/-- The intersection of two FGDual cones i FGDual. -/
lemma inf_fgdual {C D : PointedCone R N} (hC : C.FGDual p) (hD : D.FGDual p) :
    (C ⊓ D).FGDual p := by classical
  obtain ⟨S, rfl⟩ := hC; obtain ⟨T, rfl⟩ := hD
  use S ∪ T; rw [Finset.coe_union, dual_union]

/-- The double dual of a FGDual cone is the cone itself. -/
@[simp]
lemma FGDual.dual_dual_flip {C : PointedCone R N} (hC : C.FGDual p) :
    dual p (dual p.flip C) = C := by
  obtain ⟨D, hfgdual, rfl⟩ := exists_fg_dual hC
  exact dual_dual_flip_dual (p := p) D

/-- The double dual of a FGDual cone is the cone itself. -/
@[simp]
lemma FGDual.dual_flip_dual {C : PointedCone R M} (hC : C.FGDual p.flip) :
    dual p.flip (dual p C) = C := hC.dual_dual_flip

lemma FGDual.isDualClosed {C : PointedCone R M} (hC : C.FGDual p.flip) :
    C.IsDualClosed p := hC.dual_flip_dual

lemma FGDual.isDualClosed_flip {C : PointedCone R N} (hC : C.FGDual p) :
    C.IsDualClosed p.flip := hC.dual_dual_flip

-----

section LinearOrder

variable {R M N : Type*}
variable [CommRing R] [LinearOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R} -- bilinear pairing

lemma FGDual.coe {S : Submodule R N} (hS : S.FGDual p) : (S : PointedCone R N).FGDual p := by
  obtain ⟨T, hfg, rfl⟩ := hS.exists_fg_dual
  rw [← coe_dual]
  exact fgdual_of_fg p (coe_fg hfg)

alias coe_fgdual := FGDual.coe

-- Q: is this problematic?
instance {S : Submodule R N} : Coe (S.FGDual p) (FGDual p (S : PointedCone R N)) := ⟨coe_fgdual⟩

@[simp] lemma coe_fgdual_iff {S : Submodule R N} :
    (S : PointedCone R N).FGDual p ↔ S.FGDual p := by -- classical
  -- unfold FGDual Submodule.FGDual
  constructor
  · intro hfgdual
    obtain ⟨s, hs⟩ := hfgdual
    use s
    sorry
  · exact coe_fgdual

lemma FGDual.lineal_fgdual {C : PointedCone R N} (hC : C.FGDual p) : C.lineal.FGDual p := by
  obtain ⟨D, hfg, rfl⟩ := hC.exists_fg_dual
  rw [dual_span_lineal_dual, ← Submodule.dual_span]
  exact Submodule.fgdual_of_fg p (submodule_span_fg hfg)

end LinearOrder

@[deprecated]
lemma FGDual.dual_inf_dual_sup_dual' {C D : PointedCone R N} (hC : C.FGDual p) (hD : D.FGDual p) :
    dual p.flip (C ⊓ D : PointedCone R N) = (dual p.flip C) ⊔ (dual p.flip D) := by
  have ⟨C', hCfg, hC'⟩ := FGDual.exists_fg_dual hC
  have ⟨D', hDfg, hD'⟩ := FGDual.exists_fg_dual hD
  rw [← hC', ← hD', ← dual_sup_dual_inf_dual]
  rw [dual_flip_dual (by sorry)] -- not true
  rw [dual_flip_dual (by sorry)] -- not true
  rw [dual_flip_dual (by sorry)] -- not true
  -- Maybe we can prove this only with Field (need dual_dual for FG; need p.IsFaithfulPair?)

end PointedCone
