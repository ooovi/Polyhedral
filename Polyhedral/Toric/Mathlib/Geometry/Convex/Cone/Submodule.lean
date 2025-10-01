import Mathlib.RingTheory.Finiteness.Basic

namespace Submodule

lemma restrictedScalars_FG_of_FG {E S R : Type*} [Semiring R] [Semiring S]
  [AddCommMonoid E] [Module R S] [Module R E] [Module S E] [IsScalarTower R S E]
  [Module.Finite R S] {s : Submodule S E} (hfin : s.FG) : (s.restrictScalars R).FG := by
  rw [← Module.Finite.iff_fg] at *
  exact Module.Finite.trans S s

end Submodule
