/-
Copyright (c) 2025 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Order.Partition.Basic

import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.MinkowskiWeyl
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Face.Lattice
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Face.Exposed
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Face.Faces2
import Polyhedral.Hyperplane
import Polyhedral.Halfspace

open Module

-- ## PREDICATE

namespace PointedCone

variable {R : Type*} [Field R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}
variable {C F F₁ F₂ : PointedCone R M}

def FaciallyExposed (C : PointedCone R M) :=
    ∀ ⦃F : PointedCone R M⦄, F.IsFaceOf C → F.IsExposedFaceOf C

-- TODO: can we reduce assumptions?
variable (p) [Fact (Function.Surjective p.flip)] in
@[simp] lemma IsFaceOf.DualClosed.subdual_subdual (hC : C.DualClosed p) (hF : F.IsFaceOf C) :
    subdual p.flip (dual p C) (subdual p C F) = F := by
  repeat rw [subdual_def]
  rw [hC]
  rw [← dual_span_lineal_dual]
  rw [Submodule.coe_inf, Submodule.coe_restrictScalars]
  nth_rw 3 [← PointedCone.ofSubmodule_coe]
  rw [FGDual.dual_inf_dual_sup_dual ?_ ?_]
  · rw [Submodule.coe_restrictScalars, dual_eq_submodule_dual]
    rw [hC]
    nth_rw 2 [← Submodule.dual_span]
    rw [Submodule.dual_flip_dual p]
    have H : (C ⊔ Submodule.span R (F : Set M)).lineal = Submodule.span R F := by
      sorry
    rw [H]
    exact IsFaceOf.inf_submodule hF
  · simpa using FG.dual_fgdual _ hC
  · rw [LinearMap.flip_flip, coe_fgdual_iff, ← Submodule.dual_span]
    exact Submodule.FG.dual_fgdual _ (submodule_span_fg <| hF.fg_of_fg hC)

end PointedCone








-- ## BUNDLES STRUCTURE

namespace PointedCone

variable {R : Type*} [Field R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}
variable {C F F₁ F₂ : PointedCone R M}

def FaciallyExposed.Face.dual_orderHom (hC : C.FaciallyExposed) (hC' : (dual p C).FaciallyExposed) :
    Face (dual p C) ≃o OrderDual (Face C) := sorry

end PointedCone
