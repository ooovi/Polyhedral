import Mathlib.Algebra.Module.Submodule.Pointwise
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.Geometry.Convex.Cone.Dual

import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Basic

namespace PointedCone

open Module

variable {R M N : Type*} [CommRing R] [PartialOrder R] [IsOrderedRing R] [AddCommGroup M]
  [AddCommGroup N] [Module R M] [Module R N] {p : M →ₗ[R] N →ₗ[R] R}

@[simp] lemma coe_dual (S : Submodule R M) : dual p S = Submodule.dual p S := by
  ext x; simp

-- TODO: Replace `dual_span`
@[simp] lemma dual_span' (s : Set M) : dual p (span R s) = dual p s := dual_span ..

@[simp low + 1] lemma mem_dual'_singleton {x : M} {y : N} : y ∈ dual p {x} ↔ 0 ≤ p x y := by simp

section Map

open Module

variable {M' N' : Type*}
  [AddCommGroup M'] [Module R M']
  [AddCommGroup N'] [Module R N']

-- TODO: generalize to arbitrary pairings
lemma dual_map (f : M →ₗ[R] M') (s : Set M) :
    comap f.dualMap (dual (Dual.eval R M) s) = dual (Dual.eval R M') (f '' s) := by
  ext x; simp

-- TODO: generalize to arbitrary pairings
-- lemma dual_map' (f : M →ₗ[R] M') (hf : Function.Injective f) (s : Set M) :
--     map f.dualMap.inverse (dual (Dual.eval R M) s) = dual (Dual.eval R M') (f '' s) := by
--   ext x; simp

end Map

@[simp]
lemma neg_dual {s : Set M} : -(dual p s) = dual p (-s) := by
  ext x -- TODO: make this proof an application of `map_dual`
  simp
  constructor
  · intro hy y hy'
    specialize hy hy'
    simp_all only [map_neg, LinearMap.neg_apply, Left.neg_nonpos_iff]
  · intro hy y hy'
    rw [← _root_.neg_neg y] at hy'
    specialize hy hy'
    simp_all only [_root_.neg_neg, map_neg, LinearMap.neg_apply, Left.nonneg_neg_iff]

end PointedCone
