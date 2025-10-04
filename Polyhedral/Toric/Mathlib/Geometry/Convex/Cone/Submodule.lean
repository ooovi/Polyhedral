import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.LinearAlgebra.SesquilinearForm
import Mathlib.LinearAlgebra.Dual.Defs

import Polyhedral.Toric.Mathlib.Geometry.Convex.Cone.Submodule_Dual

namespace Submodule

variable {E S R : Type*} [Semiring R] [Semiring S]
  [AddCommMonoid E] [Module R S] [Module R E] [Module S E] [IsScalarTower R S E]

lemma restrictedScalars_FG_of_FG [Module.Finite R S] {s : Submodule S E} (hfin : s.FG) :
    (s.restrictScalars R).FG := by
  rw [← Module.Finite.iff_fg] at *;
  exact Module.Finite.trans S s

example (S S' : Set E) : span R (S ∪ S') = (span R S) ⊔ (span R S')
  := Submodule.span_union S S' -- should `Submodule.span_union` be a simp lemma? Yael says possibly
example (S S' : Submodule R E) : span R (S ⊔ S' : Submodule R E) = S ⊔ S'
  := by simp

@[simp] lemma span_union' (S S' : Submodule R E) : span R (S ∪ S') = S ⊔ S'
  := by rw [Submodule.span_union]; simp
@[simp] lemma span_inter (S S' : Submodule R E) : span R (S ∩ S') = S ⊓ S'
    := by rw [←coe_inf, span_eq]

example (S S' : Submodule R E) : (S ∩ S' : Set E) = S ⊓ S'
  := by simp -- only [coe_inf]

/-- Restricts a submodule S to a submodule T. -/
def restrict (S T : Submodule R E) : Submodule R T := S.comap T.subtype
-- def restrict_set (S : Set E) (T : Submodule R E) : Set T := S.comap T.subtype

variable {R : Type*} [CommSemiring R]
variable {F : Type*} [AddCommMonoid F] [Module R F] [Module R E] [Module S E]
variable {p : E →ₗ[R] F →ₗ[R] R}

section CoFG

open Module

-- def FG (N : Submodule R M) : Prop :=
--   ∃ S : Finset M, Submodule.span R ↑S = N
def CoFG (N : Submodule R E) : Prop :=
  ∃ S : Finset (Dual R E), dual .id S = N

lemma dual_bilin_dual_id (s : Set E) : dual p s = dual .id (p '' s):= by ext x; simp

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

-- @[simp]
lemma dual_fg_iff_cofg (N : Submodule R E) : N.CoFG → (dual p N).FG := sorry

end CoFG

end Submodule
