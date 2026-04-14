/-
Copyright (c) 2025 Justus Springer, Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer, Martin Winter
-/
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.LinearAlgebra.SesquilinearForm.Basic

import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.DualFG

/-!
# Polyhedral cones

Given a bilinear pairing `p` between two `R`-modules `M` and `N`, we define
polyhedral cones to be pointed cones in `N` that are the dual of a finite set
in `M` (this means they are the intersection of finitely many halfspaces).

The main statement is that if both `M` and `N` are finite and the pairing is injective
in both arguments, then polyhedral cones are precisely the finitely generated cones, see
`isPolyhedral_iff_fg`. Moreover, we obtain that the dual of a polyhedral cone is again polyhedral
(`IsPolyhedral.dual`) and that the double dual of a polyhedral cone is the cone itself
(`IsPolyhedral.dual_dual_flip`, `IsPolyhedral.dual_flip_dual`).
-/

open Function Module LinearMap
open Submodule hiding span dual
open Set

variable {𝕜 M N : Type*}
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsOrderedRing 𝕜]
variable {M : Type*} [AddCommGroup M] [Module 𝕜 M]
variable {N : Type*} [AddCommGroup N] [Module 𝕜 N]
variable {p : M →ₗ[𝕜] N →ₗ[𝕜] 𝕜}
variable {C D : PointedCone 𝕜 M}

namespace PointedCone

theorem FG.dual_inf (hC : C.FG) (hD : FG D) :
    dual p (C ⊓ D) = dual p C ⊔ dual p D := sorry

theorem FG.dual_inf_dualfg {C D : PointedCone 𝕜 N} (hC : C.FG) (hD : DualFG p D) :
    dual p.flip (C ⊓ D) = dual p.flip C ⊔ dual p.flip D := sorry

theorem DualFG.dual_inf_fg {C D : PointedCone 𝕜 N} (hC : DualFG p C) (hD : D.FG) :
    dual p.flip (C ⊓ D) = dual p.flip C ⊔ dual p.flip D := sorry

theorem DualFG.dual_inf {C D : PointedCone 𝕜 N} (hC : DualFG p C) (hD : D.DualFG p) :
    dual p.flip (C ⊓ D) = dual p.flip C ⊔ dual p.flip D := sorry

@[simp]
theorem FG.dual_dual (hC : C.FG) : dual p.flip (dual p C) = C := sorry

theorem DualFG.dual_fg {C : PointedCone 𝕜 N} (hC : C.DualFG p) : FG (dual p.flip C) := by
  obtain ⟨D, hfg, rfl⟩ := DualFG.exists_fg_dual hC
  simp [FG.dual_dual, hfg]

theorem FG.inf (hC : C.FG) (hD : D.FG) : FG (C ⊓ D) := sorry

theorem FG.inf_submodule {S : Submodule 𝕜 M} (hC : C.FG) : FG (C ⊓ S) := sorry
theorem FG.submodule_inf {S : Submodule 𝕜 M} (hC : C.FG) : FG (S ⊓ C : PointedCone 𝕜 M) := sorry

theorem DualFG.sup {C D : PointedCone 𝕜 N} (hC : C.DualFG p) (hD : D.DualFG p) : FG (C ⊔ D) := sorry

theorem DualFG.sup_submodule {C : PointedCone 𝕜 N} {S : Submodule 𝕜 N} (hC : C.DualFG p) :
    DualFG p (C ⊔ S) := sorry
theorem DualFG.submodule_sup {C : PointedCone 𝕜 N} {S : Submodule 𝕜 N} (hC : C.DualFG p) :
    DualFG p (S ⊔ C) := sorry

theorem FG.inf_dualfg {C D : PointedCone 𝕜 N} (hC : C.FG) (hD : D.DualFG p) : FG (C ⊓ D) := sorry

theorem DualFG.inf_fg {C D : PointedCone 𝕜 N} (hC : C.DualFG p) (hD : D.FG) : FG (C ⊓ D) := sorry

theorem FG.sup_dualfg {C D : PointedCone 𝕜 N} (hC : C.FG) (hD : D.DualFG p) :
    DualFG p (C ⊔ D) := sorry

theorem DualFG.sup_fg {C D : PointedCone 𝕜 N} (hC : C.DualFG p) (hD : D.FG) :
    DualFG p (C ⊔ D) := sorry

section Finite

variable {C : PointedCone 𝕜 N}

variable [Module.Finite 𝕜 N] in
theorem DualFG.fg (hC : C.DualFG p) : FG C := by simpa using hC.inf_fg fg_top

variable [Module.Finite 𝕜 M] [Fact p.SeparatingLeft] in
theorem FG.dualfg (hC : C.FG) : DualFG p C := by simpa using FG.sup_dualfg hC DualFG.bot

variable [Module.Finite 𝕜 N] [Module.Finite 𝕜 M] [Fact p.SeparatingLeft] in
  -- this is IsPerfPair, no?
theorem fg_iff_dualfg : FG C ↔ DualFG p C := ⟨FG.dualfg, DualFG.fg⟩

variable [Module.Finite 𝕜 N] in
theorem FG.dual_fg {C : PointedCone 𝕜 M} (hC : FG C) : FG (dual p C) := (dual_of_fg p hC).fg

end Finite

end PointedCone
