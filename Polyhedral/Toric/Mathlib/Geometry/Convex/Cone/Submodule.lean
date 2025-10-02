import Mathlib.RingTheory.Finiteness.Basic

namespace Submodule

variable {E S R : Type*} [Semiring R] [Semiring S]
  [AddCommMonoid E] [Module R S] [Module R E] [Module S E] [IsScalarTower R S E]
  [Module.Finite R S]

lemma restrictedScalars_FG_of_FG {s : Submodule S E} (hfin : s.FG) :
    (s.restrictScalars R).FG := by
  rw [← Module.Finite.iff_fg] at *;
  exact Module.Finite.trans S s

omit [Module.Finite R S]

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

end Submodule
