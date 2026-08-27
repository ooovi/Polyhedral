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

theorem hull_eq_smul (hs : s.Nonempty) (hc : IsConvexSet R s) :
    hull R s = Ici (0 : R) • s := by
  let C : PointedCone R M := {
    carrier := {y | ∃ r : R, 0 ≤ r ∧ y ∈ r • s}
    smul_mem' := by
      intro c x ⟨r, hr, hx⟩
      refine ⟨c.val * r, mul_nonneg c.prop hr, ?_⟩
      obtain ⟨y, hy, rfl⟩ := hx
      exact ⟨y, hy, by simp [mul_smul]⟩
    add_mem' := by
      rintro x y ⟨a, ha, hx⟩ ⟨b, hb, hy⟩
      refine ⟨a + b, add_nonneg ha hb, ?_⟩
      by_cases hab : a + b = 0
      · have ha0 : a = 0 := by linarith
        have hb0 : b = 0 := by linarith
        simp only [ha0, hb0, hs, zero_smul_set, mem_zero] at hx hy
        simp [hx, hy, hab, zero_smul_set hs]
      · rw [IsConvexSet.add_smul hc ha hb hab]
        exact add_mem_add hx hy
    zero_mem' := by
      exact ⟨0, le_rfl, hs.choose, hs.choose_spec, zero_smul R hs.choose⟩ }
  ext y
  constructor
  · intro hy
    have hle : hull R s ≤ C := sInf_le fun z hz ↦ ⟨1, by simp [hz]⟩
    exact hle hy
  · rintro ⟨r, hr, z, hz, rfl⟩
    exact (hull R s).smul_mem hr (subset_hull hz)

/-- Every nonzero member of the conic hull of a convex set is a positive scalar multiple of a
member of the set. -/
theorem mem_hull_iff_mem_pos_smul_of_convex_nonzero {x : M} {s : Set M}
    (hc : IsConvexSet R s) (hx : x ≠ 0) : x ∈ hull R s ↔ x ∈ Ioi (0 : R) • s := by
  by_cases hs : s.Nonempty
  · constructor
    · intro h
      obtain ⟨r, hr, hxs⟩ := (Set.ext_iff.mp (hull_eq_smul hs hc) x).mp h
      rcases eq_or_ne r 0 with rfl | hr0
      · simp_all
      exact ⟨r, lt_of_le_of_ne hr hr0.symm, hxs⟩
    · exact fun h ↦ (Set.ext_iff.mp (hull_eq_smul hs hc) x).mpr
        (Set.smul_subset_smul_right Ioi_subset_Ici_self h)
  · simp [Set.not_nonempty_iff_eq_empty.mp hs, hx]

end Field

end PointedCone

end Convexity
