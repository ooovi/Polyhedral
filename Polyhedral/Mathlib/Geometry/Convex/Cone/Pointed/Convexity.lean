/-
Copyright (c) 2025 Olivia Röhrig, Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Olivia Röhrig, Martin Winter
-/

import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Basic
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Basic
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Hull
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Lattice
import Mathlib.Geometry.Convex.ConvexSpace.Module

/-!
# Pointed cones in `ConvexSpace`s

This file shows a pointed cone is a convex set, as well as proves results about the conic hull of
convex sets.
-/

section Convexity

namespace PointedCone

open Convexity

section Ring

variable {R M : Type*} [Ring R] [PartialOrder R] [IsStrictOrderedRing R] [AddCommGroup M]
    [Module R M] [ConvexSpace R M] [IsModuleConvexSpace R M] {s : Set M}

lemma isConvexSet (P : PointedCone R M) :
    IsConvexSet R (P : Set M) := by
  intro w hw
  rw [sConvexComb_eq_sum w]
  refine P.finsuppSum_mem _ _ (fun i r ↦ r • i) (fun c hc ↦ ?_)
  exact P.smul_mem (w.weights_nonneg c) <| hw (Finsupp.mem_support_iff.mpr hc)

@[coe]
def toConvexSet (P : PointedCone R M) : ConvexSet R M := ⟨_, P.isConvexSet⟩

instance : Coe (PointedCone R M) (ConvexSet R M) := ⟨toConvexSet⟩

@[simp] theorem hull_convexHull (t : Set M) :
    hull R (Convexity.convexHull R t) = hull R t := by
  apply le_antisymm
  · exact sInf_le <| Convexity.convexHull_min le_hull (isConvexSet _)
  · exact hull_mono Convexity.subset_convexHull_self

end Ring

section Field

variable {R M : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup M]
    [Module R M] [ConvexSpace R M] [IsModuleConvexSpace R M] {s : Set M}

open Pointwise Set

/-- The cone hull of a convex set is the union of the closed halflines through that set. -/
lemma mem_hull_iff_of_convex (hs : s.Nonempty) (hc : IsConvexSet R s) (x : M) :
    x ∈ hull R s ↔ x ∈ Ici (0 : R) • s where
  mp hx := by
    let C : PointedCone R M := {
      carrier := {y | ∃ r : R, 0 ≤ r ∧ y ∈ r • s}
      smul_mem' := by
        intro c x ⟨r, rpos, hr⟩
        use c.val • r, mul_nonneg c.prop rpos
        obtain ⟨m, hm, rfl⟩ := hr
        exact ⟨m, hm, by simp [mul_smul]⟩
      add_mem' := by
        rintro y₁ y₂ ⟨r₁, hr₁, hy₁⟩ ⟨r₂, hr₂, hy₂⟩
        refine ⟨r₁ + r₂, add_nonneg hr₁ hr₂, ?_⟩
        by_cases h : r₁ + r₂ = 0
        · have h₁ : r₁ = 0 := by linarith
          have h₂ : r₂ = 0 := by linarith
          simp only [h₁, h₂, hs, zero_smul_set, mem_zero] at hy₂ hy₁
          simp [hy₁, hy₂, h, zero_smul_set hs]
        · rw [IsConvexSet.add_smul hc hr₁ hr₂ h]
          exact add_mem_add hy₁ hy₂
      zero_mem' := by
        use 0; simpa using ⟨hs.choose, hs.choose_spec, zero_smul R (Exists.choose hs)⟩
    }
    refine sInf_le (a := C) ?_ hx
    exact fun _ hy ↦ ⟨1, by simp [hy]⟩
  mpr h := by
    obtain ⟨r, hr, y, hy, rfl⟩ := h
    exact (hull R s).smul_mem (Set.mem_Ici.mp hr) <| subset_hull hy

/-- Every nonzero member of the conic hull of a convex set is a pos. smultiple of a set member. -/
theorem mem_hull_iff_mem_pos_smul_of_convex_nonzero {x : M} {s} (hc : IsConvexSet R s)
    (hx : x ≠ 0) :
    x ∈ hull R s ↔ x ∈ Ioi (0 : R) • s := by
  by_cases hs : s.Nonempty
  · constructor <;> intro h
    · obtain ⟨r, rpos, hr⟩ := (mem_hull_iff_of_convex hs hc _).mp h
      rcases eq_or_ne 0 r with rfl | h
      · simp_all
      exact ⟨r, lt_of_le_of_ne rpos h, hr⟩
    · simp [mem_hull_iff_of_convex hs hc, Set.smul_subset_smul_right Ioi_subset_Ici_self h]
  · simp [Set.not_nonempty_iff_eq_empty.mp hs, hx]

-- TODO: this should be proven directly, and the lemmas above can be removed.
theorem hull_eq_smul (hs : s.Nonempty) (hc : IsConvexSet R s) :
    hull R s = Ici (0 : R) • s := by
  ext x; exact mem_hull_iff_of_convex hs hc x

end Field

end PointedCone

end Convexity
