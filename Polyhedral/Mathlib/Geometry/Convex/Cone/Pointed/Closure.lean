import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Dual

namespace PointedCone

open Module LinearMap ClosureOperator

variable {R M N : Type*} [CommRing R] [PartialOrder R] [IsOrderedRing R] [AddCommGroup M]
  [AddCommGroup N] [Module R M] [Module R N] {p : M →ₗ[R] N →ₗ[R] R}

/-
 What should be implemented:
  * `PreDualityOperator` (his is *not* `GaloisConnection`)
  * `dual` as a `PreDualityOperator`
  * An automatic `ClosureOperator` obtain by applying the `PreDualityOperator` twice.
  * `DualityOperator`
  * An automatic instance on the `Closeds` of the closure operator of the `PreDualityOperator`.
-/

/- Q: should there be a `DualityOperator` that automatically comes with a `ClosureOperator`?-/

variable (p) in
/-- The operation that maps a cone to its double dual. -/
def dualClosure : ClosureOperator (PointedCone R M) where
  toFun C := dual p.flip (dual p C)
  monotone' _ _ hCD := dual_antimono (dual_antimono hCD)
  le_closure' _ := SetLike.coe_subset_coe.mp subset_dual_dual
  idempotent' _ := by rw [dual_flip_dual_dual_flip]
  isClosed_iff := by simp

variable (p) in
/-- The operation that maps a cone to its double dual. -/
def dualClosure_flip : ClosureOperator (PointedCone R N) where
  toFun C := dual p (dual p.flip C)
  monotone' _ _ hCD := dual_antimono (dual_antimono hCD)
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

@[simp] lemma dual_dual_eq_dual_of_dualClosed {C : PointedCone R M} (hC : C.dualClosed p):
    dual p.flip (dual p C) = C := IsClosed.closure_eq hC

lemma dual_dualClosed {C : PointedCone R M} : (dual p C).dualClosed p.flip := by
  rw [dualClosed, isClosed_iff]; simp

lemma dual_inf_dual_sup_dual_of_dualClosed {C D : PointedCone R M}
    (hC : C.dualClosed p) (hD : D.dualClosed p) :
      dual p (C ⊓ D : PointedCone R M) = (dual p C) ⊔ (dual p D) := by
  rw [← dual_dual_eq_dual_of_dualClosed hC]
  rw [← dual_dual_eq_dual_of_dualClosed hD]

  sorry

abbrev DualClosedCone := Closeds (dualClosure p)

end PointedCone
