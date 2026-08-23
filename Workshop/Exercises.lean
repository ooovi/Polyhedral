import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Face.Basic

variable {R X Y : Type*}

open Convexity

section Semiring

variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [ConvexSpace R X]

variable {S P P₁ P₂ s : Set X}

variable (R) in
def IsPolytope (s : Set X) : Prop := ∃ t : Finset X, s = Convexity.convexHull R t

/- # Exercise 1:
Given the definition of a polytope, show that the empty set is a polytope. -/

lemma empty_isPolytope : IsPolytope R (∅ : Set X) := by
  sorry

/- # Exercise 2:
Define the unit square as the convex hull of its vertices in the convex space
and show that is a polytope. -/

def vertices : Finset (ℚ × ℚ) := {(0, 0), (1,0), (0,1), (1,1)}

def unitSquare : Set (ℚ × ℚ) := sorry

theorem unitSquare_isPolytope : IsPolytope ℚ unitSquare := by
  sorry

/- # Exercise 3:
Show that polytopes are convex sets -/

lemma polytope_isConvexSet (hP : IsPolytope R P) : IsConvexSet R P := by
  sorry

/- Constructor is a tactic that we use to split a complex goal into multiple simpler
goals. To prove that a convex set is a face of another we need to show two things:
the first one is a subset relation and the second one is that is the extreme property. -/

/- # Exercise 4:
Show that every convex set is a face of itself -/
theorem refl_convexSet (S : ConvexSet R X) : S.IsFaceOf S := by
  sorry

/- # Exercise 5:
Show that the intersection of two convex sets is a convex set -/

lemma intersection_isConvexSet (hP₁ : IsConvexSet R P₁) (hP₂ : IsConvexSet R P₂) :
    IsConvexSet R (P₁ ∩ P₂) := by
  sorry

/- # Exercise 6:
Show that the convex hull of the union of finitely many polytopes is a polytope.
For this we can start by showing that the convex hull of the union of two polytopes is a
polytope and then use the iduction tactic. -/

lemma convexHull_union (h₁ : IsPolytope R P₁) (h₂ : IsPolytope R P₂) :
    IsPolytope R (convexHull R (P₁ ∪ P₂)) := by
  sorry

lemma convexHull_iUnion_finite {p : Set (Set X)} (hp : p.Finite)
    (h : ∀ P ∈ p, IsPolytope R P) : IsPolytope R (convexHull R (⋃ P ∈ p, P)) := by
  sorry

end Semiring
