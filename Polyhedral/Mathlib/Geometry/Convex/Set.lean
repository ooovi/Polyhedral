module

public import Mathlib.Geometry.Convex.Set

public section

namespace Convexity

variable {R X Y Z : Type*} [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]
  [ConvexSpace R X] [ConvexSpace R Y] [ConvexSpace R Z] {f : X → Y} {s : Set X} {t : Set Y}

/-- The range of an affine map between convex spaces is convex. -/
lemma IsAffineMap.isConvexSet_range (hf : IsAffineMap R f) :
    IsConvexSet R (.range f) := by simpa using IsConvexSet.univ.image hf

protected lemma IsConvexSet.image2 {f : X → Y → Z} (hf : IsAffineMap R ↿f)
    (hs : IsConvexSet R s) (ht : IsConvexSet R t) : IsConvexSet R (.image2 f s t) := by
  simpa [← Set.image_uncurry_prod, Function.HasUncurry.uncurry] using (hs.prod ht).image hf

end Convexity
