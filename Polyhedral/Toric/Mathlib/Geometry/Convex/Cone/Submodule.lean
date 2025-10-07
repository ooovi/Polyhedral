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

@[simps]
protected abbrev copy' (s : Set E) (hs : ∃ p : Submodule R E, s = p) :
    Submodule R E where
  carrier := s
  zero_mem' := by obtain ⟨p, rfl⟩ := hs; exact p.zero_mem'
  add_mem' := by obtain ⟨p, rfl⟩ := hs; exact p.add_mem'
  smul_mem' := by obtain ⟨p, rfl⟩ := hs; exact p.smul_mem'

theorem copy_eq' (s : Set E) (hs : ∃ p : Submodule R E, s = ↑p) : Submodule.copy' s hs = s := rfl

end Submodule
