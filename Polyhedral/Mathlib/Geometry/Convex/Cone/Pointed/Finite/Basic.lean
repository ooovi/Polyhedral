import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Lineal

open Submodule (span)

namespace PointedCone

namespace FG

section LinearOrderRing

-- we have LinearOrder because then Module.Finite { c // 0 ≤ c } R
variable {R M : Type*} [Ring R] [LinearOrder R] [IsOrderedRing R] [AddCommMonoid M]
  [Module R M]

set_option backward.isDefEq.respectTransparency false in
lemma coe_fg {S : Submodule R M} (hS : S.FG) : (S : PointedCone R M).FG
    := Submodule.FG.restrictScalars hS

-- Q: is this problematic?
-- instance {S : Submodule R M} : Coe S.FG (S : PointedCone R M).FG := ⟨coe_fg⟩

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma coe_fg_iff {S : Submodule R M} : (S : PointedCone R M).FG ↔ S.FG :=
  ⟨Submodule.FG.of_restrictScalars _, coe_fg⟩

set_option backward.isDefEq.respectTransparency false in
/-- The submodule span of a finitely generated pointed cone is finitely generated. -/
lemma span_fg {C : PointedCone R M} (hC : C.FG) : (span R (C : Set M)).FG := hC.span

lemma top [Module.Finite R M] : (⊤ : PointedCone R M).FG := coe_fg Module.Finite.fg_top

end LinearOrderRing

section DivisionRing

variable {R : Type*} [DivisionRing R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

end DivisionRing

section LinearOrderGroup

variable {R : Type*} [Ring R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

lemma salientQuot_fg {C : PointedCone R M} (hC : C.FG) : C.salientQuot.FG := quot_fg hC _

end LinearOrderGroup

end FG

end PointedCone
