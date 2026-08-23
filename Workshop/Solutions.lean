import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Face.Basic

variable {R X Y : Type*}

open Convexity

section Semiring

variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [ConvexSpace R X]

variable {S P P₁ P₂ : Set X}

variable (R) in
def IsPolytope (s : Set X) : Prop := ∃ t : Finset X, s = Convexity.convexHull R t

/- # Exercise 1:
Given the definition of a polytope, show that the empty set is a polytope. -/

lemma empty_isPolytope : IsPolytope R (∅ : Set X) := by
  use ∅
  simp

/- # Exercise 2:
Define the unit square as the convex hull of its vertices in the convex space
and show that is a polytope. -/

def vertices : Finset (ℚ × ℚ) := {(0, 0), (1,0), (0,1), (1,1)}

def unitSquare : Set (ℚ × ℚ) := Convexity.convexHull ℚ vertices

theorem unitSquare_isPolytope : IsPolytope ℚ unitSquare := by
  unfold unitSquare
  use vertices

/- # Exercise 3:
Show that polytopes are convex sets -/

lemma polytope_isConvexSet (hP : IsPolytope R P) : IsConvexSet R P := by
  unfold IsPolytope at hP
  obtain ⟨t, ht⟩ := hP
  rw [ht]
  exact IsConvexSet.convexHull

/- Constructor is a tactic that we use to split a complex goal into multiple simpler
goals. To prove that a convex set is a face of another we need to show two things:
the first one is a subset relation and the second one is that is the extreme property. -/

/- # Exercise 4:
Show that every convex set is a face of itself -/
theorem refl_convexSet (S : ConvexSet R X) : S.IsFaceOf S := by
  constructor
  · simp
  · intro x hx y hy z hz hhz
    exact hx

/- The proof can be condensed. -/
theorem refl_convexSet' (S : ConvexSet R X) : S.IsFaceOf S :=
  ⟨by simp, by intro x hx y hy z hz h; exact hx⟩

/- And even more. -/
theorem refl_convexSet'' (S : ConvexSet R X) : S.IsFaceOf S :=
  ⟨by simp, fun _ hx _ _ _ _ _ => hx⟩

/- # Exercise 5:
Show that the intersection of two convex sets is a convex set -/

lemma intersection_isConvexSet (hP₁ : IsConvexSet R P₁) (hP₂ : IsConvexSet R P₂) :
    IsConvexSet R (P₁ ∩ P₂) := by
  unfold IsConvexSet at ⊢ hP₁ hP₂
  intro w hw
  rw [Set.subset_inter_iff] at hw
  constructor
  · exact hP₁ hw.1
  · exact hP₂ hw.2

/- `specialize` is a tactic used to apply hypotheses of the form `∀` to a specific value. -/
lemma intersection_isConvexSet' (hP₁ : IsConvexSet R P₁) (hP₂ : IsConvexSet R P₂) :
    IsConvexSet R (P₁ ∩ P₂) := by
  unfold IsConvexSet at ⊢ hP₁ hP₂
  intro w hw
  rw [Set.subset_inter_iff] at hw
  specialize @hP₁ w hw.1
  specialize @hP₂ w hw.2
  exact ⟨hP₁, hP₂⟩

/- The proof can be condensed. -/
lemma intersection_isConvexSet'' (hP₁ : IsConvexSet R P₁) (hP₂ : IsConvexSet R P₂) :
    IsConvexSet R (P₁ ∩ P₂) := by
  intro w hw
  rw [Set.subset_inter_iff] at hw
  exact ⟨hP₁ hw.1, hP₂ hw.2⟩

/- # Exercise 6:
Show that the convex hull of the union of finitely many polytopes is a polytope.
For this we can start by showing that the convex hull of the union of two polytopes is a
polytope and then use the iduction tactic. -/

lemma convexHull_union (h₁ : IsPolytope R P₁) (h₂ : IsPolytope R P₂) :
    IsPolytope R (convexHull R (P₁ ∪ P₂)) := by
  classical
  obtain ⟨v₁, rfl⟩ := h₁
  obtain ⟨v₂, rfl⟩ := h₂
  use v₁ ∪ v₂
  simp [convexHull_union_convexHull, convexHull_convexHull_union]

lemma convexHull_iUnion_finite {p : Set (Set X)} (hp : p.Finite)
    (h : ∀ P ∈ p, IsPolytope R P) : IsPolytope R (convexHull R (⋃ P ∈ p, P)) := by
  induction p, hp using Set.Finite.induction_on with
  | empty =>
    rw [Set.biUnion_empty]
    rw [convexHull_empty]
    exact empty_isPolytope
  | insert _ _ h' =>
    simp only [Set.mem_insert_iff, Set.iUnion_iUnion_eq_or_left, forall_eq_or_imp] at ⊢ h
    rw [← convexHull_union_convexHull]
    exact convexHull_union h.1 (h' h.2)

end Semiring
