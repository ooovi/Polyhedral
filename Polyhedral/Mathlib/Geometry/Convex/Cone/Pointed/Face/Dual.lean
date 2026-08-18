/-
Copyright (c) 2025 Olivia Röhrig, Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Olivia Röhrig, Martin Winter
-/

import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Subdual

/-!
This file proves results about the interaction of faces of cones and duals of cones.
-/

namespace PointedCone

variable {R M N : Type*}

section Field

variable [Field R] [LinearOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]

variable (p : M →ₗ[R] N →ₗ[R] R) {C F F₁ F₂ : PointedCone R M}

/-- The subdual of a face is a face of the dual. -/
lemma IsFaceOf.subdual_dual (hF : F.IsFaceOf C) :
    (subdual p C F).IsFaceOf (dual p C) := by
  unfold subdual
  refine of_mem_of_add_mem_left (by simp) ?_
  intro x y hxC
  simp only [mem_dual, SetLike.mem_coe, Submodule.mem_inf, map_add, Submodule.restrictScalars_mem,
    Submodule.mem_dual, hxC, true_and, and_imp]
  intro hy _ h _ hxF
  refine eq_of_le_of_ge (hxC (hF.le hxF)) ?_
  rw [h hxF]
  exact (le_add_iff_nonneg_right _).mpr <| hy (hF.le hxF)

end Field

end PointedCone
