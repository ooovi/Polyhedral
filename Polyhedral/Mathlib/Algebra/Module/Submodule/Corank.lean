import Mathlib.LinearAlgebra.Dimension.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Dimension.RankNullity

import Polyhedral.Mathlib.Algebra.Module.Submodule.Basic

open Module Cardinal

namespace Submodule

section Semiring

variable {R : Type*} [Semiring R] {M : Type*} [AddCommMonoid M] [Module R M]

noncomputable def spanCorank (S : Submodule R M) :=
  ⨅ ι : { s : Submodule R M // span R s ⊔ S = ⊤ }, (Module.rank R ι.1)

noncomputable def corank' (S : Submodule R M) :=
  ⨆ ι : { s : Submodule R M // span R s ⊓ S = ⊥ }, (Module.rank R ι.1)

end Semiring

section Ring

variable {R : Type*} [Ring R] {M : Type*} [AddCommGroup M] [Module R M]

noncomputable abbrev corank (S : Submodule R M) :
    Cardinal := Module.rank R (M ⧸ S)

lemma Submodule.corank_eq_inf_linearIndep (S : Submodule R M) :
    corank S = ⨅ ι : { s : Set M // S ⊔ span R s = ⊤}, (#ι.1) := by
  sorry

lemma rank_add_corank (S : Submodule R M) : Module.rank R S + corank S = Module.rank R M :=
  sorry

lemma rank_eq_corank_of_isCompl {S T : Submodule R M} (h : IsCompl S T) :
    Module.rank R S = corank T :=
  sorry

end Ring

end Submodule
