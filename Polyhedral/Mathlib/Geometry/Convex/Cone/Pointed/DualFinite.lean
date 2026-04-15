import Mathlib.Geometry.Convex.Cone.DualFinite

import Polyhedral.Mathlib.Algebra.Module.Submodule.DualFinite
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Dual
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Finite.Basic

variable {R M N : Type*}

namespace PointedCone

open Module Function

variable [CommRing R]

section PartialOrder

variable [PartialOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}

lemma DualFG.dualClosed {C : PointedCone R M} (hC : C.DualFG p.flip) :
    C.DualClosed p := hC.dual_flip_dual

lemma DualFG.dualClosed_flip {C : PointedCone R N} (hC : C.DualFG p) :
    C.DualClosed p.flip := hC.dual_dual_flip

-- @[deprecated "Not proven"]
-- lemma DualFG.dual_inf_dual_sup_dual' {C D : PointedCone R N} (hC : C.DualFG p) (hD : D.DualFG p):
--     dual p.flip (C ⊓ D : PointedCone R N) = (dual p.flip C) ⊔ (dual p.flip D) := by
--   have ⟨C', hCfg, hC'⟩ := DualFG.exists_fg_dual hC
--   have ⟨D', hDfg, hD'⟩ := DualFG.exists_fg_dual hD
--   rw [← hC', ← hD', ← dual_sup_dual_inf_dual]
--   rw [dual_flip_dual (by sorry)] -- not true
--   rw [dual_flip_dual (by sorry)] -- not true
--   rw [dual_flip_dual (by sorry)] -- not true
--   -- Maybe we can prove this only with Field (need dual_dual for FG; need p.IsFaithfulPair?)

end PartialOrder

section LinearOrder

variable [LinearOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R} -- bilinear pairing

variable [Module.Finite R M] [Fact p.SeparatingRight] in
lemma DualFG.bot : DualFG p ⊥ := by
  obtain ⟨s, hs⟩ := FG.coe_fg <| Module.Finite.fg_top (R := R) (M := M)
  use s
  rw [← dual_hull]
  simp [hs]

lemma DualFG.coe {S : Submodule R N} (hS : S.DualFG p) : (S : PointedCone R N).DualFG p := by
  obtain ⟨T, hfg, rfl⟩ := hS.exists_fg_dual
  rw [← coe_dual]
  exact dual_of_fg p (FG.coe_fg hfg)

alias coe_dualfg := DualFG.coe

-- Q: is this problematic?
instance {S : Submodule R N} : Coe (S.DualFG p) (DualFG p (S : PointedCone R N)) := ⟨coe_dualfg⟩

@[simp] lemma coe_dualfg_iff {S : Submodule R N} :
    (S : PointedCone R N).DualFG p ↔ S.DualFG p := by
  constructor
  · rintro ⟨s, hs⟩
    use s
    rw [← dual_span_lineal_dual, ← submodule_lineal S]
    congr
  · exact coe_dualfg

lemma DualFG.lineal_dualfg {C : PointedCone R N} (hC : C.DualFG p) : C.lineal.DualFG p := by
  obtain ⟨D, hfg, rfl⟩ := hC.exists_fg_dual
  rw [dual_span_lineal_dual, ← Submodule.dual_span]
  exact Submodule.dual_of_fg p (FG.span_fg hfg)

end LinearOrder

end PointedCone
