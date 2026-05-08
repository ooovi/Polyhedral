import Polyhedral.Mathlib.LinearAlgebra.ConvexSpace
import Polyhedral.Mathlib.LinearAlgebra.AffineSpace.Defs

namespace ConvexSpace.ConvexSet

variable {R A : Type*}
variable [PartialOrder R] [Ring R] [IsStrictOrderedRing R]
variable {V : Type*} [AddCommGroup V] [Module R V]
variable [AddTorsor V A]

variable {C : ConvexSet R A}

-- Affine.rank needs ring

noncomputable abbrev rank (C : ConvexSet R A) := Affine.rank R (C : Set A)

noncomputable abbrev finrank (C : ConvexSet R A) := Affine.finrank R (C : Set A)

namespace Face

noncomputable abbrev rank (F : C.Face) : Cardinal := F.toConvexSet.rank

noncomputable abbrev finrank (F : C.Face) : ℕ := F.toConvexSet.finrank

end Face

end ConvexSpace.ConvexSet
