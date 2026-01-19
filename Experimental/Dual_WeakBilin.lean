import Mathlib.Algebra.Module.Submodule.Pointwise
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.Geometry.Convex.Cone.Dual

import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Algebra.Module.WeakBilin

import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Dual

namespace PointedCone

open Module LinearMap TopologicalSpace

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [TopologicalSpace R] [OrderTopology R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}

lemma foo (S : Submodule R M) :
    S.IsDualClosed p ↔ IsClosed (X := WeakBilin p) (SetLike.coe S) := by sorry

end PointedCone
