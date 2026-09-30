module

public import Mathlib.Geometry.Convex.Hull
public import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Defs
public import Polyhedral.Mathlib.Geometry.Convex.Set

public section

namespace Convexity
variable {R X Y ι : Type*} [Semiring R] [PartialOrder R] [IsStrictOrderedRing R] [ConvexSpace R X]
  [ConvexSpace R Y]

/-- The convex hull of a product is the product of the convex hulls. -/
lemma convexHull_prod (s : Set X) (t : Set Y) :
    convexHull R (s ×ˢ t) = convexHull R s ×ˢ convexHull R t := by
  refine (convexHull_min (by grw [← subset_convexHull_self, ← subset_convexHull_self])
    (.prod .convexHull .convexHull)).antisymm ?_
  rintro ⟨x, y⟩ ⟨hx, hy⟩
  have step y (hy : y ∈ t) : (x, y) ∈ convexHull R (s ×ˢ t) := by
    have hcvx : IsConvexSet R ((·, y) ⁻¹' convexHull R (s ×ˢ t)) :=
      .preimage (by fun_prop) .convexHull
    exact hcvx.convexHull_subset_iff.mpr (fun x hx ↦ subset_convexHull_self ⟨hx, hy⟩) hx
  have hcvx : IsConvexSet R ((x, ·) ⁻¹' convexHull R (s ×ˢ t)) :=
    .preimage (by fun_prop) .convexHull
  exact hcvx.convexHull_subset_iff.mpr step hy

/-- The convex hull of the range of `f` is the image of the standard simplex `StdSimplex R ι`
under the affine map sending weights to the corresponding convex combination of `f`.

For finite `ι`, this can be interpreted as saying that a polytope is the image of some
simplex under some affine map. -/
lemma convexHull_range (f : ι → X) :
    convexHull R (.range f) = .range (fun w : StdSimplex R ι ↦ iConvexComb w f) := by
  refine (convexHull_min ?_ isAffineMap_iConvexComb.isConvexSet_range).antisymm ?_
  · rintro _ ⟨i, rfl⟩
    exact ⟨.single i, by simp⟩
  · rintro _ ⟨w, rfl⟩
    exact IsConvexSet.convexHull.iConvexComb_mem fun i _ ↦ subset_convexHull_self ⟨i, rfl⟩

end Convexity
