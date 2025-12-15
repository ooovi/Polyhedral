import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.Geometry.Convex.Cone.Dual
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Mathlib.Algebra.Module.Submodule.Pointwise

import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Lineal
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Face.Basic

variable {R M N : Type*}

namespace PointedCone
open Module

namespace IsFaceOf

section Field

variable [Field R] [LinearOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] {C F : PointedCone R M}

/-- The lineality space of a cone `C` is a face of `C`. -/
lemma lineal (C : PointedCone R M) : IsFaceOf (M := M) (R := R) C.lineal C := by
  apply iff_mem_of_add_mem.mpr
  simp only [lineal_le, Submodule.restrictScalars_mem, true_and]
  intro _ _ xc yc xyf
  simp only [lineal_mem, neg_add_rev, xc, true_and] at xyf ⊢
  simpa [neg_add_cancel_comm] using add_mem xyf.2 yc

lemma lineal_le {C F : PointedCone R M} (hF : F.IsFaceOf C) :
    C.lineal ≤ F := by
  intro x hx
  apply lineal_mem.mp at hx
  exact (IsFaceOf.iff_mem_of_add_mem.mp hF).2 hx.1 hx.2 (by simp)

lemma lineal_eq {C F : PointedCone R M} (hF : F.IsFaceOf C) : F.lineal = C.lineal := by
  sorry

end Field

end IsFaceOf

end PointedCone
