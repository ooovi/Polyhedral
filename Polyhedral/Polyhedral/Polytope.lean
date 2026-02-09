
import Polyhedral.Mathlib.LinearAlgebra.AffineSpace.Defs

open AffineSpace -- TODO who imports Convex!!

namespace Polytope

variable {R M : Type*}
variable [PartialOrder R] [Semiring R] [IsStrictOrderedRing R] [AffineSpace R M]
variable {s t : Set M} {x y : M}

/-- A set is a polytope if it is the convex hull of finitely many points. -/
def IsPolytope (s : Set M) : Prop := ∃ t : Finset M, s = AffineSpace.convexHull R t

end Polytope
