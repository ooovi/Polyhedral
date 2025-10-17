import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Dual

namespace PointedCone

open Module LinearMap ClosureOperator

variable {R M N : Type*} [CommRing R] [PartialOrder R] [IsOrderedRing R] [AddCommGroup M]
  [AddCommGroup N] [Module R M] [Module R N] {p : M →ₗ[R] N →ₗ[R] R}

/-
 What should be implemented
  * `PreDualityOperator`. Is this the `GaloisConnection` (should it be called differently?)
  * An automatic closure operator by applying it twice.
  * `DualityOperator`.
  * An automatic instance on the `Closeds` of the closure operator of `PreDualityOperator`.
-/

#check GaloisConnection

/- Q: should there be a `DualityOperator` that automatically comes with a `ClosureOperator`?-/

variable (p) in
/-- The operation that maps a cone to its double dual. -/
def dualClosure : ClosureOperator (PointedCone R M) where
  toFun C := dual p.flip (dual p C)
  monotone' _ _ hCD := dual_le_dual (dual_le_dual hCD)
  le_closure' _ := SetLike.coe_subset_coe.mp subset_dual_dual
  idempotent' _ := by rw [dual_flip_dual_dual_flip]
  isClosed_iff := by simp

variable (p) in
/-- The operation that maps a cone to its double dual. -/
def dualClosure_flip : ClosureOperator (PointedCone R N) where
  toFun C := dual p (dual p.flip C)
  monotone' _ _ hCD := dual_le_dual (dual_le_dual hCD)
  le_closure' _ := SetLike.coe_subset_coe.mp subset_dual_dual
  idempotent' _ := by rw [dual_flip_dual_dual_flip]
  isClosed_iff := by simp

variable (p) in
lemma dualClosure_flip_eq : dualClosure p.flip = dualClosure_flip p := by sorry

variable (p) in
@[simp] lemma dualClosure_eq_flip : dualClosure_flip p.flip = dualClosure p := by sorry

@[simp] lemma dualClosure_def (C : PointedCone R M) :
  -- dualClosure p C = dual p.flip (dual p C) := by rfl
  (dualClosure p).toFun C = dual p.flip (dual p C) := by rfl


variable (p) in
abbrev dualClosed (C : PointedCone R M) := IsClosed (dualClosure p) C

-- variable (p) in
-- abbrev dualClosed_flip (C : PointedCone R N) := IsClosed (dualClosure_flip p) C

lemma dual_dualClosed {C : PointedCone R M} : (dual p C).dualClosed p.flip := by
  rw [dualClosed, isClosed_iff]; simp

abbrev DualClosedCone := Closeds (dualClosure p)

end PointedCone
