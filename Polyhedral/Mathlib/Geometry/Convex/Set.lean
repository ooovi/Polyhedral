module

public import Mathlib.Geometry.Convex.Set

public section

namespace Convexity

variable {R X Y : Type*} [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]
  [ConvexSpace R X] [ConvexSpace R Y]

/-- The range of an affine map between convex spaces is convex. -/
lemma IsAffineMap.isConvexSet_range {f : X → Y} (hf : IsAffineMap R f) :
    IsConvexSet R (.range f) := by simpa using IsConvexSet.univ.image hf

end Convexity
