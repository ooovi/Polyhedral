import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Module
import Mathlib.Geometry.Convex.Hull
import Mathlib.Tactic.Ring

namespace Convexity

variable {R X : Type*}

section OrderedConvexSpace

variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]
  [PartialOrder X] [ConvexSpace R X] [IsOrderedConvexSpace R X]

variable (R)

protected lemma IsConvexSet.Iic (a : X) : IsConvexSet R (Set.Iic a) := by
  refine .of_sConvexComb_mem fun w hw ↦ ?_
  change w.sConvexComb ≤ a
  rw [← iConvexComb_id' w, ← iConvexComb_const w a]
  exact iConvexComb_le_iConvexComb_of_support fun x hx ↦ hw (by simpa using hx)

protected lemma IsConvexSet.Ici (a : X) : IsConvexSet R (Set.Ici a) := by
  refine .of_sConvexComb_mem fun w hw ↦ ?_
  change a ≤ w.sConvexComb
  rw [← iConvexComb_id' w, ← iConvexComb_const w a]
  exact iConvexComb_le_iConvexComb_of_support fun x hx ↦ hw (by simpa using hx)

protected lemma IsConvexSet.Icc (a b : X) : IsConvexSet R (Set.Icc a b) := by
  simpa [Set.Ici_inter_Iic] using
    (IsConvexSet.Ici R a).inter (IsConvexSet.Iic R b)

lemma convexHull_pair_subset_Icc_of_le (a b : X) (hab : a ≤ b) :
    convexHull R {a, b} ⊆ Set.Icc a b :=
  (IsConvexSet.Icc R a b).convexHull_subset_iff.mpr
    (Set.pair_subset (Set.left_mem_Icc.mpr hab) (Set.right_mem_Icc.mpr hab))

end OrderedConvexSpace

section Semiring

variable [Semiring R] [LinearOrder R] [IsStrictOrderedRing R]

variable (R)

private lemma mem_convexHull_pair_of_weights {a b x p q : R}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q = 1)
    (hcomb : p * a + q * b = x) :
    x ∈ convexHull R ({a, b} : Set R) := by
  have ha : a ∈ convexHull R ({a, b} : Set R) := subset_convexHull_self (by simp)
  have hb : b ∈ convexHull R ({a, b} : Set R) := subset_convexHull_self (by simp)
  rw [← hcomb]
  simpa [convexCombPair_eq_sum, smul_eq_mul] using
    (IsConvexSet.convexHull (R := R) (s := ({a, b} : Set R))).convexCombPair_mem
      ha hb hp hq hpq

lemma Icc_zero_one_subset_convexHull [ExistsAddOfLE R] :
    Set.Icc 0 1 ⊆ convexHull R ({0, 1} : Set R) := by
  rintro x ⟨hx0, hx1⟩
  obtain ⟨d, hd, hxd⟩ := exists_nonneg_add_of_le hx1
  exact mem_convexHull_pair_of_weights R hd hx0 (by simpa [add_comm] using hxd) (by simp)

@[simp]
lemma convexHull_zero_one_eq_Icc [ExistsAddOfLE R] :
    convexHull R ({0, 1} : Set R) = Set.Icc 0 1 :=
  Set.Subset.antisymm (convexHull_pair_subset_Icc_of_le R 0 1 zero_le_one)
    (Icc_zero_one_subset_convexHull R)

end Semiring

section Semifield

variable [Semifield R] [LinearOrder R] [IsStrictOrderedRing R] [PosMulReflectLT R]

variable (R)

lemma Icc_subset_convexHull [ExistsAddOfLE R] (a b : R) :
    Set.Icc a b ⊆ convexHull R ({a, b} : Set R) := by
  rintro x ⟨hxa, hxb⟩
  obtain ⟨c, hc, hxc⟩ := exists_nonneg_add_of_le hxa
  obtain ⟨d, hd, hxd⟩ := exists_nonneg_add_of_le hxb
  by_cases h : c + d = 0
  · have hc0 : c = 0 := (add_eq_zero_iff_of_nonneg hc hd).mp h |>.1
    have hx : x = a := by simpa [hc0] using hxc.symm
    rw [hx]
    exact subset_convexHull_self (by simp)
  · let e := (c + d)⁻¹
    have he : 0 ≤ e := inv_nonneg.mpr (add_nonneg hc hd)
    have hunit : (c + d) * e = 1 := mul_inv_cancel₀ h
    have hp : 0 ≤ d * e := mul_nonneg hd he
    have hq : 0 ≤ c * e := mul_nonneg hc he
    have hpq : d * e + c * e = 1 := by rw [← add_mul, add_comm d c, hunit]
    refine mem_convexHull_pair_of_weights R hp hq hpq ?_
    calc
      d * e * a + c * e * b = (a + c) * ((c + d) * e) := by
        rw [← hxd, ← hxc]
        ring
      _ = x := by rw [hunit, mul_one, ← hxc]

@[simp]
lemma convexHull_pair_eq_Icc [ExistsAddOfLE R]
    (a b : R) (hab : a ≤ b) : convexHull R ({a, b} : Set R) = Set.Icc a b :=
  Set.Subset.antisymm (convexHull_pair_subset_Icc_of_le R a b hab)
    (Icc_subset_convexHull R a b)

end Semifield
end Convexity
