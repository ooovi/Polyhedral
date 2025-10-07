import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.LinearAlgebra.SesquilinearForm
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.LinearAlgebra.Dimension.Finite

import Polyhedral.Toric.Mathlib.Geometry.Convex.Cone.Submodule_Dual

open Module

namespace Submodule

variable {E S R : Type*} [Semiring R] [Semiring S]
  [AddCommMonoid E] [Module R S] [Module R E] [Module S E] [IsScalarTower R S E]

-- def CoFG (S : Submodule R M) : Prop := ∃ T : Finset M, (span R T) ⊔ S = ⊤

variable {R 𝕜 M N M' N' : Type*}
variable {R : Type*} [CommSemiring R]
variable {F : Type*} [AddCommMonoid F] [Module R F] [Module R E] [Module S E]
variable {p : E →ₗ[R] F →ₗ[R] R}

section CoFG

-- def FG (N : Submodule R M) : Prop :=
--   ∃ S : Finset M, Submodule.span R ↑S = N
def CoFG (N : Submodule R E) : Prop :=
  ∃ S : Finset (Dual R E), dual .id S = N

lemma dual_bilin_dual_id (s : Set E) : dual p s = dual .id (p '' s) := by ext x; simp

-- NOTE: converse is not true
lemma cofg_intro (N : Submodule R F) (hN : ∃ S : Finset E, dual p S = N) : N.CoFG := by
  classical
  obtain ⟨S, hS⟩ := hN
  use Finset.image p S
  rw [Finset.coe_image, ← hS, ← dual_bilin_dual_id]

lemma cofg_def_fg (N : Submodule R E) (hN : N.CoFG) :
    ∃ M : Submodule R (Dual R E), M.FG ∧ dual .id M = N := by
  obtain ⟨S, hS⟩ := hN
  exact ⟨span R S, ⟨S, rfl⟩, by rw [dual_span, hS]⟩

lemma cofg_of_dual_fg (N : Submodule R F) (hN : ∃ M : Submodule R E, M.FG ∧ dual p M = N) :
    N.CoFG := by
  obtain ⟨M, ⟨S, hS⟩, hM⟩ := hN
  refine cofg_intro (E := E) (p := p) N ?_
  exact ⟨S, by rw [← dual_span, hS, hM]⟩

lemma cofg_of_dual_fg' (N : Submodule R F) (M : Submodule R E) (hM : M.FG) (hN : dual p M = N) :
    N.CoFG := cofg_of_dual_fg N ⟨M, hM, hN⟩

lemma dual_cofg_iff_fg (N : Submodule R E) : N.FG → (dual p N).CoFG
  := (cofg_of_dual_fg' _ N · rfl)

lemma cofg_inter (M N : Submodule R E) (hM : M.CoFG) (hN : N.CoFG) : (M ⊓ N).CoFG := by
  classical
  obtain ⟨S, rfl⟩ := hM
  obtain ⟨T, rfl⟩ := hN
  use S ∪ T
  rw [Finset.coe_union, dual_union]

-- @[simp]
lemma dual_fg_iff_cofg (N : Submodule R E) : N.CoFG → (dual p N).FG := sorry

variable {E' F' : Type*}
  [AddCommGroup E'] [Module R E']
  [AddCommGroup F'] [Module R F']
  -- {p' : E' →ₗ[R] F' →ₗ[R] R}

lemma map_dual (f : E →ₗ[R] E') (C : Submodule R E) :
    dual (Dual.eval R E') (map f C) = comap f.dualMap (dual (Dual.eval R E) C) := by
  ext x; simp

-- lemma map_dual' (f : (Dual R E) →ₗ[R] (Dual R E')) (C : Submodule R (Dual R E)) :
--     dual .id (map f C) = comap f.dualMap (dual .id C) := by
--   ext x; simp

end CoFG

end Submodule
