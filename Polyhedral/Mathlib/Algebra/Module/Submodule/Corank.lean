import Mathlib.LinearAlgebra.Dimension.Basic

-- import Mathlib.RingTheory.Finiteness.Basic
-- import Mathlib.LinearAlgebra.SesquilinearForm
-- import Mathlib.LinearAlgebra.Dual.Defs
-- import Mathlib.LinearAlgebra.Dimension.Finrank
-- import Mathlib.RingTheory.Finiteness.Defs
-- import Mathlib.LinearAlgebra.Dimension.Finite

open Module

namespace Submodule

variable {R : Type*} [Semiring R] {M : Type*} [AddCommMonoid M] [Module R M]

noncomputable def corank (S : Submodule R M) :=
  ⨅ ι : { s : Submodule R M // span R s ⊔ S = ⊤ }, (Module.rank R ι.1)

end Submodule
