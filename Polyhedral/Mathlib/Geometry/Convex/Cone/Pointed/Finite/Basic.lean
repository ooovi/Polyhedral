import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Lineal

namespace PointedCone

namespace FG

section LinearOrderMonoid

-- we have LinearOrder because then Module.Finite { c // 0 ≤ c } R
variable {R M : Type*} [Ring R] [LinearOrder R] [IsOrderedRing R] [AddCommMonoid M]
  [Module R M]

set_option backward.isDefEq.respectTransparency false in
lemma ofSubmodule_fg_of_fg {S : Submodule R M} (hS : S.FG) : (S : PointedCone R M).FG
    := Submodule.FG.restrictScalars hS

/- We current struggle to implement the converse, see `FG.of_restrictScalars`. -/
alias coe_fg := ofSubmodule_fg_of_fg

-- Q: is this problematic?
-- instance {S : Submodule R M} : Coe S.FG (S : PointedCone R M).FG := ⟨coe_fg⟩

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma coe_fg_iff {S : Submodule R M} : (S : PointedCone R M).FG ↔ S.FG :=
  ⟨Submodule.FG.of_restrictScalars _, coe_fg⟩

set_option backward.isDefEq.respectTransparency false in
/-- The submodule span of a finitely generated pointed cone is finitely generated. -/
lemma FG.linSpan_fg {C : PointedCone R M} (hC : C.FG) : C.linSpan.FG :=
  hC.span

lemma fg_top [Module.Finite R M] : (⊤ : PointedCone R M).FG :=
  ofSubmodule_fg_of_fg Module.Finite.fg_top

end LinearOrderMonoid

section DivisionRing

variable {R : Type*} [DivisionRing R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

lemma lineal_fg {C : PointedCone R M} (hC : C.FG) : C.lineal.FG := by classical
  obtain ⟨s, hs⟩ := hC
  use (s.finite_toSet.inter_of_left C.lineal).toFinset -- means {x ∈ s | x ∈ C.lineal}
  rw [submodule_span_of_span]
  simpa [← hs] using span_inter_lineal_eq_lineal R (s : Set M)

end DivisionRing

section LinearOrderGroup

variable {R : Type*} [Ring R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

lemma salientQuot_fg {C : PointedCone R M} (hC : C.FG) : C.salientQuot.FG := quot_fg hC _

end LinearOrderGroup

end FG

end PointedCone
