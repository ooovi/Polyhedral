
import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.Geometry.Convex.Cone.Dual
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Mathlib.Algebra.Module.Submodule.Pointwise
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.SetTheory.Cardinal.Defs

import Polyhedral.Mathlib.Algebra.Module.Submodule.FG
import Polyhedral.Mathlib.Algebra.Module.Submodule.Dual

import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Basic

namespace PointedCone

open Module Function

open Pointwise

section Semiring_AddCommGroup

variable {R : Type*} [Ring R] [PartialOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

-- TODO: Does this not already exist?
lemma map_id_eq_neg (C : PointedCone R M) : C.map (-.id) = -C := by
  ext x
  simp only [Submodule.mem_neg, mem_map, LinearMap.neg_apply, LinearMap.id_coe, id_eq]
  constructor
  · intro h
    obtain ⟨y, hyC, rfl⟩ := h
    simpa using hyC
  · exact fun h => by use -x; simp [h]

lemma comap_id_eq_neg (C : PointedCone R M) : C.comap (-.id) = -C := by
  ext x; simp

variable {N : Type*} [AddCommGroup N] [Module R N]

lemma map_neg (C : PointedCone R M) (f : M →ₗ[R] N) : map (-f) C = map f (-C) := by
  ext x
  simp only [mem_map, LinearMap.neg_apply, Submodule.mem_neg]
  constructor <;> {
    intro h
    obtain ⟨x, hx⟩ := h
    exact ⟨-x, by simpa using hx⟩
  }

lemma map_neg_apply (C : PointedCone R M) (f : M →ₗ[R] N) : - map f C = map f (-C) := by
  ext x
  simp
  constructor <;> {
    intro h
    obtain ⟨x, hx⟩ := h
    exact ⟨-x, by simpa [neg_eq_iff_eq_neg] using hx⟩
  }

lemma comap_neg (C : PointedCone R M) (f : N →ₗ[R] M) : comap (-f) C = comap f (-C) := by
  ext x; simp

lemma comap_neg_apply (C : PointedCone R M) (f : N →ₗ[R] M) : -comap f C = comap f (-C) := by
  ext x; simp

end Semiring_AddCommGroup

section DirectedOrderRing

variable {R : Type*} [Ring R] [PartialOrder R] [IsDirectedOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]


-- lemma neg_self_iff_eq_span_submodule {C : PointedCone R M} (hC : -C = C) :
--     Submodule.span R (C : Set M) = C := by
--   suffices h : ∀ C, Submodule.span R (C : Set M) ≥ C from by
--     rw [le_antisymm_iff]
--     constructor
--     · rw [← Submodule.neg_le_neg]
--       sorry
--     · exact h C
--   intro C
--   exact Submodule.subset_span

-- lemma foo {α : Type} [InvolutiveNeg α] [SupSet α] (s : Set α) :
--     ⨆ a ∈ s ⊔ -s, a = ⨆ a ∈ α × FinSet 2,  := by sorry

-- lemma foo (s : Set (PointedCone R M)) :
--     ⨆ C ∈ s ⊔ -s, C = ⨆ C ∈ s, (C ⊔ -C) := by
--   simp
--   rw [le_antisymm_iff]
--   constructor
--   · intro h

--     sorry
--   · sorry

-- Mathematically, this lemma is equivalent to directedness of the order on `R`: for `M = R`
-- and `x = 1`, it says every element of `R` is a difference of two nonnegative elements.
variable (R) in
lemma span_pm_pair_eq_submodule_span (x : M) :
    span R {-x, x} = Submodule.span R {-x, x} := by
  ext y
  simp only [Submodule.restrictScalars_mem, Submodule.mem_span_pair,
    smul_neg, Subtype.exists, Nonneg.mk_smul, exists_prop]
  constructor
  · rintro ⟨a, _, b, _, rfl⟩
    exact ⟨a, b, rfl⟩
  · rintro ⟨a, b, rfl⟩
    obtain ⟨c, hac, hbc⟩ := exists_ge_ge a b
    refine ⟨c - b, sub_nonneg.mpr hbc, c - a, sub_nonneg.mpr hac, ?_⟩
    calc
      -((c - b) • x) + (c - a) • x = (-(c - b) + (c - a)) • x := by
        rw [← neg_smul, ← add_smul]
      _ = (b - a) • x := by
        congr 1
        abel
      _ = -(a • x) + b • x := by
        rw [sub_smul]
        abel

omit [IsDirectedOrder R] in
@[simp]
lemma neg_coe (S : Submodule R M) : -(S : PointedCone R M) = S := by ext x; simp

variable (R) in
@[simp] lemma span_sign_pair_eq_submodule_span_singleton (x : M) :
    span R {-x, x} = Submodule.span R {x} := by
  simpa [← Submodule.span_insert_eq_span_of_mem] using span_pm_pair_eq_submodule_span R x

lemma submodule_span_eq_add_span_neg (s : Set M) : Submodule.span R s = span R s ⊔ span R (-s) := by
  ext x; constructor <;> intro h
  · simp only [Submodule.restrictScalars_mem, Submodule.mem_span_set'] at h
    obtain ⟨n, f, g, rfl⟩ := h
    have hx : ∑ i, f i • (g i : M) ∈ span R (-s ∪ s) := by
      refine sum_mem ?_
      intro i _
      have hpair : f i • (g i : M) ∈ span R ({-(g i : M), (g i : M)} : Set M) := by
        rw [span_sign_pair_eq_submodule_span_singleton (R := R) (x := (g i : M))]
        exact Submodule.mem_span_singleton.mpr ⟨f i, by simp⟩
      exact Set.mem_of_subset_of_mem (Submodule.span_mono <| by
        intro z hz
        rcases Set.mem_insert_iff.mp hz with rfl | hz
        · exact Set.mem_union_left _ (by simp [(g i).property])
        · rcases Set.mem_singleton_iff.mp hz with rfl
          exact Set.mem_union_right _ (g i).property) hpair
    simpa [span_union, sup_comm, Set.union_comm] using hx
  · simp only [Submodule.mem_sup] at h
    obtain ⟨_, hy, _, hz, rfl⟩ := h
    exact add_mem
      (Submodule.mem_span.mpr fun p hp => Submodule.mem_span.mp hy p hp)
      (Submodule.mem_span.mpr fun p hp => Submodule.mem_span.mp hz p <| by
        intro y hy
        simpa using p.neg_mem (hp (Set.mem_neg.mp hy)))

-- NOTE: if this is implemented, it is more general than what mathlib already provides
-- for converting submodules into pointed cones. Especially the proof that R≥0 is an FG
-- submodule of R should be easier with this.
lemma span_union_neg_eq_span_submodule (s : Set M) :
    span R (-s ∪ s) = Submodule.span R s := by
  ext x
  simp only [Set.involutiveNeg, Submodule.mem_span, Set.union_subset_iff, and_imp,
    Submodule.restrictScalars_mem]
  constructor <;> intros h B sB
  · refine h (Submodule.restrictScalars {c : R // 0 ≤ c} B) ?_ sB
    rw [Submodule.coe_restrictScalars]
    exact fun _ tm => neg_mem_iff.mp (sB tm)
  · intro nsB
    have : x ∈ (Submodule.span R s : PointedCone R M) :=
      h (Submodule.span R s) Submodule.subset_span
    rw [submodule_span_eq_add_span_neg s] at this
    obtain ⟨_, h₁, _, h₂, h⟩ := Submodule.mem_sup.mp this
    rw [← h]
    apply add_mem
    · exact Set.mem_of_subset_of_mem (Submodule.span_le.mpr nsB) h₁
    · exact Set.mem_of_subset_of_mem (Submodule.span_le.mpr sB) h₂

lemma sup_neg_eq_submodule_span (C : PointedCone R M) : -C ⊔ C = C.linSpan := by
  nth_rw 1 2 [← Submodule.span_eq C]
  rw [← Submodule.span_neg_eq_neg, ← Submodule.span_union]
  exact span_union_neg_eq_span_submodule (C : Set M)

lemma span_eq_submodule_span_of_neg_self {s : Set M} (hs : s = -s) :
    span R s = Submodule.span R s := by
  nth_rw 1 [← Set.union_self s]
  nth_rw 1 [hs]
  exact span_union_neg_eq_span_submodule s

omit [IsDirectedOrder R] in
lemma neg_le_iff_neg_eq {C : PointedCone R M} : -C ≤ C ↔ -C = C  where
  mp := by
    intro h
    ext x; rw [Submodule.mem_neg]
    suffices h : ∀ x, -x ∈ C → x ∈ C from by
      exact ⟨h x, by nth_rw 1 [← neg_neg x]; exact h (-x)⟩
    exact SetLike.le_def.mp @h
  mpr := le_of_eq

lemma neg_self_iff_eq_span_submodule {C : PointedCone R M} :
    -C = C ↔ Submodule.span R (C : Set M) = C := by
  rw [← sup_neg_eq_submodule_span, sup_eq_right]
  exact neg_le_iff_neg_eq.symm

lemma neg_self_iff_eq_span_submodule' {C : PointedCone R M} :
    -C ≤ C ↔ Submodule.span R (C : Set M) = C
  := Iff.trans neg_le_iff_neg_eq neg_self_iff_eq_span_submodule

lemma mem_linSpan (C : PointedCone R M) {x : M} :
    x ∈ C.linSpan ↔ ∃ p ∈ C, ∃ n ∈ C, p = x + n := by
  rw [← mem_coe, ← sup_neg_eq_submodule_span, Submodule.mem_sup]
  simp only [Submodule.mem_neg]
  constructor <;> intro h
  · obtain ⟨y, hy', z, hz, rfl⟩ := h
    exact ⟨z, hz, -y, hy', by simp⟩
  · obtain ⟨p, hp, n, hn, rfl⟩ := h
    exact ⟨-n, by simp [hn], x + n, hp, by simp⟩

end DirectedOrderRing

end PointedCone
