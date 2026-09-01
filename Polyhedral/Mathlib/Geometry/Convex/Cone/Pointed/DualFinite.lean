/-
Copyright (c) 2025 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/
module

public import Mathlib.Geometry.Convex.Cone.DualFinite
public import Polyhedral.Mathlib.Algebra.Module.Submodule.Dual.DualFinite
public import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.DualClosed
public import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Finite.Basic

/-! This file proves results about duals of FG cones. -/

public section

variable {R M N L : Type*}

namespace PointedCone

open Module Function

variable [CommRing R]

section PartialOrder

variable [PartialOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]
variable [AddCommGroup L] [Module R L]
variable {p : M →ₗ[R] N →ₗ[R] R}

/-- The preimage of a DualFG cone under a linear map is DualFG. -/
lemma DualFG.comap {C : PointedCone R N} (hC : C.DualFG p) (f : L →ₗ[R] N) :
    (C.comap f).DualFG (f.dualMap.comp p) := by
  obtain ⟨s, hs⟩ := hC
  refine ⟨s, ?_⟩
  rw [← hs]
  ext x
  simp

/-- The restriction of a DualFG cone to a submodule is DualFG. -/
lemma DualFG.restrict {C : PointedCone R N} (hC : C.DualFG p) (S : Submodule R N) :
    (C.restrict S).DualFG (S.dualRestrict.comp p) := by
  simp only [PointedCone.restrict]; exact DualFG.comap hC S.subtype

lemma DualFG.restrict_id {C : PointedCone R M} (hC : C.DualFG .id) (S : Submodule R M) :
    (C.restrict S).DualFG .id := (DualFG.restrict hC S).id

lemma DualFG.dualClosed {C : PointedCone R M} (hC : C.DualFG p.flip) :
    C.DualClosed p := hC.dual_flip_dual

lemma DualFG.dualClosed_flip {C : PointedCone R N} (hC : C.DualFG p) :
    C.DualClosed p.flip := hC.dual_dual_flip

end PartialOrder

section LinearOrder

variable [LinearOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]

variable {p : M →ₗ[R] N →ₗ[R] R}

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
    rw [← dual_lineal_eq_submodule_dual, ← submodule_lineal S]
    congr
  · exact coe_dualfg

lemma DualFG.lineal_dualfg {C : PointedCone R N} (hC : C.DualFG p) : C.lineal.DualFG p := by
  obtain ⟨D, hfg, rfl⟩ := hC.exists_fg_dual
  rw [dual_lineal_eq_submodule_dual, ← Submodule.dual_span]
  exact Submodule.dual_of_fg p (FG.span_fg hfg)

end LinearOrder

end PointedCone
