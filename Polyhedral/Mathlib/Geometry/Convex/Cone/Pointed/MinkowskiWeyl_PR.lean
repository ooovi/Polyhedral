/-
Copyright (c) 2025 Justus Springer, Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer, Martin Winter
-/
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.LinearAlgebra.SesquilinearForm.Basic

import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.FGDual

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

theorem FGDual.dual_fg {C : PointedCone 𝕜 N} (hC : C.FGDual p) : FG (dual p.flip C) := sorry

theorem FG.dual_inf (hC : C.FG) (hD : FG D) :
    dual p (C ⊓ D) = dual p C ⊔ dual p D := sorry

theorem FG.dual_inf_fgdual {C D : PointedCone 𝕜 N} (hC : C.FG) (hD : FGDual p D) :
    dual p.flip (C ⊓ D) = dual p.flip C ⊔ dual p.flip D := sorry

theorem FGDual.dual_inf_fg {C D : PointedCone 𝕜 N} (hC : FGDual p C) (hD : D.FG) :
    dual p.flip (C ⊓ D) = dual p.flip C ⊔ dual p.flip D := sorry

theorem FGDual.dual_inf {C D : PointedCone 𝕜 N} (hC : FGDual p C) (hD : D.FGDual p) :
    dual p.flip (C ⊓ D) = dual p.flip C ⊔ dual p.flip D := sorry

theorem FG.dual_dual (hC : C.FG) : dual p.flip (dual p C) = C := sorry

theorem FG.inf (hC : C.FG) (hD : D.FG) : FG (C ⊓ D) := sorry

theorem FG.inf_submodule {S : Submodule 𝕜 M} (hC : C.FG) : FG (C ⊓ S) := sorry
theorem FG.submodule_inf {S : Submodule 𝕜 M} (hC : C.FG) : FG (S ⊓ C : PointedCone 𝕜 M) := sorry

theorem FGDual.sup {C D : PointedCone 𝕜 N} (hC : C.FGDual p) (hD : D.FGDual p) : FG (C ⊔ D) := sorry

theorem FGDual.sup_submodule {C : PointedCone 𝕜 N} {S : Submodule 𝕜 N} (hC : C.FGDual p) :
    FGDual p (C ⊔ S) := sorry
theorem FGDual.submodule_sup {C : PointedCone 𝕜 N} {S : Submodule 𝕜 N} (hC : C.FGDual p) :
    FGDual p (S ⊔ C) := sorry

theorem FG.inf_fgdual {C D : PointedCone 𝕜 N} (hC : C.FG) (hD : D.FGDual p) : FG (C ⊓ D) := sorry

theorem FGDual.inf_fg {C D : PointedCone 𝕜 N} (hC : C.FGDual p) (hD : D.FG) : FG (C ⊓ D) := sorry

section Finite

variable [Module.Finite 𝕜 M]

theorem FG.fgdual {C : PointedCone 𝕜 N} (hC : C.FG) : FGDual p C := sorry

theorem FGDual.fg {C : PointedCone 𝕜 N} (hC : C.FGDual p) : FG C := sorry

theorem fg_iff_fgdual {C : PointedCone 𝕜 N} : FG C ↔ FGDual p C := ⟨FG.fgdual, FGDual.fg⟩

end Finite

end PointedCone
