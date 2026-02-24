import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.RingTheory.Finiteness.Basic


import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.MinkowskiWeyl
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Face.Basic
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Face.Exposed

import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Face.Lattice

/-!
# Ray

...
-/

namespace PointedCone

variable {R : Type*} [Field R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}

variable {C F F₁ F₂ : PointedCone R M}

lemma zero_le_rank (C : PointedCone R M) : 0 ≤ C.rank := sorry

lemma bot_of_rank_zero (h : C.rank = 0) : C = ⊥ := sorry

lemma bot_iff_rank_zero : C.rank = 0 ↔ C = ⊥ := sorry


lemma ray_of_rank_one (hS : C.Salient) (h : C.rank = 1) : ∃ x : M, C = span R {x} := by
  have : C ≠ ⊥ := fun h' ↦ by simp [bot_iff_rank_zero.mpr h'] at h
  obtain ⟨x, hxC, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot this
  refine ⟨x, le_antisymm ?_ (by simp [hxC]) ⟩
  intro y hy
  by_cases! ha : ∃ a : R, y = a • x
  · obtain ⟨a, rfl⟩ := ha
    by_cases! ha : a ≥ 0
    · exact smul_mem ({ c // 0 ≤ c } ∙ x) ha <| Submodule.mem_span_singleton_self x
    exfalso
    apply hS x hxC hx0
    have : -x = (-a⁻¹) • (a • x) := by
      rw [smul_smul]
      field_simp [ne_of_lt ha]
      rw [neg_smul, one_smul]
    rw [this]
    exact smul_mem C (le_of_lt <| neg_pos.2 <| inv_lt_zero.mpr ha) hy
  let f := ![(⟨x, Submodule.mem_span_of_mem hxC⟩ : C.linSpan), ⟨y, Submodule.mem_span_of_mem hy⟩]
  have : LinearIndependent R f := by
    apply (LinearIndependent.pair_iff' (Subtype.coe_ne_coe.mp hx0)).2
    exact fun a ↦ Subtype.coe_ne_coe.mp fun a_1 ↦ ha a  (Eq.symm a_1)
  have : C.rank ≥ 2 := Module.le_rank_iff.2 ⟨f, this⟩
  simp [h] at this

lemma rank_one_of_ray {x : M} (hx : x ≠ 0) : (span R {x}).rank = 1 := by
  apply (rank_submodule_eq_one_iff (span R {x}).linSpan).mpr
  use x, (by simp only [Submodule.span_span_of_tower, Submodule.mem_span_singleton_self])
  refine ⟨hx, ?_⟩
  simp only [Submodule.span_span_of_tower, le_refl]
