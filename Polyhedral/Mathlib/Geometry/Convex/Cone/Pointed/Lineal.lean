
import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.Geometry.Convex.Cone.Dual
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Mathlib.Algebra.Module.Submodule.Pointwise

import Polyhedral.Mathlib.Algebra.Module.Submodule.FG
import Polyhedral.Mathlib.Algebra.Module.Submodule.Dual
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Basic

namespace PointedCone

open Module

section Ring_AddCommGroup

variable {R : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommMonoid M] [Module R M]

-- ## Lineality

/-- The lineality space of a cone. -/
def lineal (C : PointedCone R M) : Submodule R M := sSup {S : Submodule R M | S ≤ C }

def lineal_sSup (C : PointedCone R M) : C.lineal = sSup {S : Submodule R M | S ≤ C } := by rfl

lemma lineal_le (C : PointedCone R M) : C.lineal ≤ C := by simp [lineal]

lemma le_lineal {C : PointedCone R M} {S : Submodule R M} (hS : S ≤ C) :
    S ≤ C.lineal := le_sSup hS

@[simp]
lemma lineal_submodule (S : Submodule R M) : (S : PointedCone R M).lineal = S := by
  rw [le_antisymm_iff]
  constructor
  · --apply ofSubmodule_embedding.strictMono
    --refine le_trans (lineal_le S) ?_
    --exact lineal_le S
    sorry
  · exact le_lineal (by simp)

@[simp] lemma lineal_top : (⊤ : PointedCone R M).lineal = ⊤ := lineal_submodule ⊤
@[simp] lemma lineal_bot : (⊥ : PointedCone R M).lineal = ⊥ := lineal_submodule ⊥

section Ring

variable {R : Type*} [Ring R] [PartialOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

lemma neg_mem_of_mem_lineal {C : PointedCone R M} {x : M} (hx : x ∈ C.lineal) : -x ∈ C := by
  rw [← Submodule.neg_mem_iff] at hx
  exact lineal_le C hx

lemma mem_of_neg_mem_lineal {C : PointedCone R M} {x : M} (hx : -x ∈ C.lineal) : x ∈ C := by
  rw [Submodule.neg_mem_iff] at hx
  exact lineal_le C hx

variable {R : Type*} [Ring R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

-- @[simp] -- no simp because right side has twice as many `x`?
lemma lineal_mem {C : PointedCone R M} {x : M} : x ∈ C.lineal ↔ x ∈ C ∧ -x ∈ C := by
  constructor
  · intro h
    have h' := neg_mem_iff.mpr h
    exact ⟨lineal_le C h, lineal_le C h'⟩
  · intro ⟨h, h'⟩
    let S := Submodule.span R {-x, x}
    have hSC : S ≤ C := by
      have hx : ({-x, x} : Set M) ⊆ C := by
        intro x hx
        obtain (rfl | rfl) := hx
        exact h'; exact h
      have hx := Submodule.span_mono (R := {c : R // 0 ≤ c}) hx
      simp at hx
      simpa only [S, ← span_pm_pair_eq_submodule_span R] using hx
    have hSC := le_lineal hSC
    have hxS : x ∈ S := Submodule.mem_span_of_mem (by simp)
    exact hSC hxS -- maybe we could use the lemma that s ∪ -s spans a linear space (see above)

def lineal_inf_neg (C : PointedCone R M) : C.lineal = C ⊓ -C := by
  ext x; simp [lineal_mem]

def lineal_mem_neg (C : PointedCone R M) : C.lineal = {x ∈ C | -x ∈ C} := by
  ext x; simp; exact lineal_mem

@[simp]
lemma lineal_inf (C D : PointedCone R M) : (C ⊓ D).lineal = C.lineal ⊓ D.lineal := by
  ext x; simp [lineal_mem]; aesop

end Ring

section Semiring

variable {R : Type*} [Ring R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

/- In this section we show properties of lineal that also follow from lineal
  being a face. But we need this earlier than faces, so we need to prove that
  lineal is a face here. This can then be resused later.

  Alternatively, lineal can be defined in Faces.lean
-/

lemma lineal_isExtreme_left {C : PointedCone R M} {x y : M} (hx : x ∈ C) (hy : y ∈ C)
    (hxy : x + y ∈ C.lineal) : x ∈ C.lineal := by
  have hxy' := neg_mem_of_mem_lineal hxy
  have hx' := C.add_mem hy hxy'
  simp only [neg_add_rev, add_neg_cancel_left] at hx'
  exact lineal_mem.mpr ⟨hx, hx'⟩

lemma lineal_isExtreme_right {C : PointedCone R M} {x y : M} (hx : x ∈ C) (hy : y ∈ C)
    (hxy : x + y ∈ C.lineal) : y ∈ C.lineal := by
  rw [add_comm] at hxy; exact lineal_isExtreme_left hy hx hxy

lemma lineal_isExtreme {C : PointedCone R M} {x y : M} (hx : x ∈ C) (hy : y ∈ C)
    (hxy : x + y ∈ C.lineal) : x ∈ C.lineal ∧ y ∈ C.lineal :=
  ⟨lineal_isExtreme_left hx hy hxy, lineal_isExtreme_right hx hy hxy⟩

lemma lineal_isExtreme_right_of_inv {C : PointedCone R M} {x y : M} (hx : x ∈ C) (hy : y ∈ C)
    {c : R} (hc : 0 < c) (hc' : Invertible c) (hxy : x + c • y ∈ C.lineal) : y ∈ C.lineal := by
  have h := lineal_isExtreme_right hx (C.smul_mem (le_of_lt hc) hy) hxy
  simpa using C.lineal.smul_mem (Invertible.invOf c) h

lemma lineal_isExtreme_left_of_inv {C : PointedCone R M} {x y : M} (hx : x ∈ C) (hy : y ∈ C)
    {c : R} (hc : 0 < c) (hc' : Invertible c) (hxy : c • x + y ∈ C.lineal) : x ∈ C.lineal := by
  have h := lineal_isExtreme_left (C.smul_mem (le_of_lt hc) hx) hy hxy
  simpa using C.lineal.smul_mem (Invertible.invOf c) h

lemma lineal_isExtreme_sum {C : PointedCone R M} {xs : Finset M} (hxs : (xs : Set M) ⊆ C)
    (h : ∑ x ∈ xs, x ∈ C.lineal) : (xs : Set M) ⊆ C.lineal := by classical
  induction xs using Finset.induction_on with
  | empty => simp
  | insert y xs hy H =>
    simp only [Set.subset_def, Finset.mem_coe, SetLike.mem_coe, Finset.coe_insert,
      Set.mem_insert_iff, forall_eq_or_imp, Finset.sum_insert hy] at *
    have h := lineal_isExtreme hxs.1 (C.sum_mem hxs.2) h
    exact ⟨h.1, H hxs.2 h.2⟩

section DivisionRing

variable {R : Type*} [DivisionRing R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

lemma lineal_isExtreme_left' {C : PointedCone R M} {x y : M} (hx : x ∈ C) (hy : y ∈ C)
    {c : R} (hc : 0 < c) (hxy : c • x + y ∈ C.lineal) : x ∈ C.lineal := by
  exact lineal_isExtreme_left_of_inv hx hy hc (invertibleOfNonzero <| ne_of_gt hc) hxy

lemma lineal_isExtreme_right' {C : PointedCone R M} {x y : M} (hx : x ∈ C) (hy : y ∈ C)
    {c : R} (hc : 0 < c) (hxy : x + c • y ∈ C.lineal) : y ∈ C.lineal := by
  exact lineal_isExtreme_right_of_inv hx hy hc (invertibleOfNonzero <| ne_of_gt hc) hxy

lemma lineal_isExtreme_sum' {C : PointedCone R M} {xs : Finset M} (hxs : (xs : Set M) ⊆ C)
    (c : M → R) (hc : ∀ x ∈ xs, 0 < c x) (h : ∑ x ∈ xs, c x • x ∈ C.lineal) :
    ∀ x ∈ xs, c x ≠ 0 → x ∈ C.lineal := by classical
  induction xs using Finset.induction_on with
  | empty => simp
  | insert y xs hy H =>
    simp only [Set.subset_def, Finset.mem_coe, SetLike.mem_coe, ne_eq, Finset.coe_insert,
      Set.mem_insert_iff, forall_eq_or_imp, Finset.mem_insert, Finset.sum_insert hy] at *
    have hxsC := C.sum_mem (fun x hx => C.smul_mem (le_of_lt <| hc.2 x hx) (hxs.2 x hx))
    constructor
    · exact fun _ => lineal_isExtreme_left' hxs.1 hxsC hc.1 h
    · exact H hxs.2 hc.2 <| lineal_isExtreme_right (C.smul_mem (le_of_lt hc.1) hxs.1) hxsC h

variable (R) in
lemma span_inter_lineal_eq_lineal (s : Set M) :
    span R (s ∩ (span R s).lineal) = (span R s).lineal := by
  rw [le_antisymm_iff]
  constructor
  · rw [← Submodule.span_eq <| ofSubmodule ((span R s).lineal)]
    refine Submodule.span_mono ?_
    simp only [Submodule.coe_restrictScalars, Set.inter_subset_right]
  · sorry
  -- constructor
  -- · rw [← Submodule.span_eq (C.lineal : PointedCone R M)]
  --   exact Submodule.span_mono (by simp)
  -- · rw [← SetLike.coe_subset_coe]
  --   rw [Set.subset_def]
  --   intro x hx
  --   let S:= s ∩ C.lineal
  --   let S' := s \ C.lineal
  --   have hS : S ∪ S' = s := by simp [S, S']
  --   have hS' : S ∩ S' = ∅ := by aesop

  --   --have hs : s = (s ∩ C.lineal) ∪ ()
  --   -- rw [Submodule.mem_span_finite_of_mem_span] at h
    -- sorry

lemma FG.lineal_fg {C : PointedCone R M} (hC : C.FG) : C.lineal.FG := by classical
  obtain ⟨s, hs⟩ := hC
  use (s.finite_toSet.inter_of_left C.lineal).toFinset -- means {x ∈ s | x ∈ C.lineal}
  rw [submodule_span_of_span]
  simpa [← hs] using span_inter_lineal_eq_lineal R (s : Set M)

end DivisionRing

end Semiring

end Ring_AddCommGroup



section Ring_AddCommGroup

variable {R : Type*} [Ring R] [PartialOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

-- ## Salient

/-- A salient cone has trivial lineality space, see `salient_iff_lineal_bot`. -/
abbrev Salient (C : PointedCone R M) := C.toConvexCone.Salient

lemma salient_iff_mem_neg {C : PointedCone R M} : C.Salient ↔ ∀ x ∈ C, x ≠ 0 → -x ∉ C := by rfl

lemma Salient.mem_neg_mem_zero {C : PointedCone R M} (hC : C.Salient)
    {x : M} (hx : x ∈ C) (hx' : -x ∈ C) : x = 0 := by
  specialize hC x hx
  rw [not_imp_not] at hC
  exact hC hx'

lemma inf_sup_lineal {C : PointedCone R M} {S : Submodule R M} (hCS : Codisjoint C.lineal S) :
    (C ⊓ S) ⊔ C.lineal = C := by
  rw [le_antisymm_iff]
  constructor
  · exact sup_le_iff.mpr ⟨inf_le_left, lineal_le C⟩
  · intro x hx
    rw [Submodule.codisjoint_iff_exists_add_eq] at hCS
    obtain ⟨y, z, hy, hz, hyz⟩ := hCS x
    rw [Submodule.mem_sup]
    have hzC : z ∈ C := by
      have h := Submodule.add_mem C hx (neg_mem_of_mem_lineal hy)
      rw [← hyz, add_neg_cancel_comm] at h
      exact h
    exact ⟨z, by simp; exact ⟨hzC, hz⟩, y, hy, by rw [add_comm]; exact hyz⟩

variable {R : Type*} [Ring R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

lemma salient_iff_lineal_bot {C : PointedCone R M} : C.Salient ↔ C.lineal = ⊥ := by
  constructor
  · intro h
    ext x
    simp only [lineal_mem, Submodule.mem_bot]
    exact ⟨fun H => h.mem_neg_mem_zero H.1 H.2, by simp +contextual⟩
  · intro h x hx
    rw [not_imp_not]
    intro hnx
    have hlin := lineal_mem.mpr ⟨hx, hnx⟩
    rw [h] at hlin
    exact hlin

lemma inf_salient {C : PointedCone R M} {S : Submodule R M} (hCS : Disjoint C.lineal S) :
    (C ⊓ S).Salient := by
  simp only [salient_iff_lineal_bot, lineal_inf, lineal_submodule, ← disjoint_iff, hCS]

section DivisionRing

variable {R : Type*} [DivisionRing R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

/-- A pointed cone can be written as a sup of its lineality space and a complementary
  salient cone. -/
lemma exists_salient_disj_sup_lineal (C : PointedCone R M) :
    ∃ D : PointedCone R M, D.Salient
      ∧ Disjoint C.lineal (.span R D)
      ∧ D ⊔ C.lineal = C := by
  have ⟨S, hDis, hCod⟩ := exists_isCompl C.lineal
  refine ⟨C ⊓ S, inf_salient hDis, Disjoint.mono_right ?_ hDis, inf_sup_lineal hCod⟩
  rw [← Submodule.span_eq (p := S)]
  exact Submodule.span_mono (by simp)

/-- A pointed cone can be written as a sup of a submodule and a complementary
  salient cone. -/
lemma exists_salient_submodul_disj_sup (C : PointedCone R M) :
    ∃ D : PointedCone R M, D.Salient ∧
      ∃ S : Submodule R M, Disjoint S (.span R D) ∧ D ⊔ S = C := by
  obtain ⟨D, hSal, hDis, hSup⟩ := exists_salient_disj_sup_lineal C
  exact ⟨D, hSal, C.lineal, hDis, hSup⟩

end DivisionRing


lemma span_diff_lineal_pointy {C : PointedCone R M} {s : Set M} (h : span R s = C) :
    (span R (s \ C.lineal)).Salient := by
  sorry

/-- A cone is a sum of a pointed cone and its lineality space. -/
-- NOTE: I just realzed that this is true in a boring sense: let D := span C \ C.lineal ∪ {0}
lemma exists_pointy_sup_lineal (C : PointedCone R M) :
    ∃ D : PointedCone R M, D.Salient ∧ D ⊔ C.lineal = C := by
  have hT : ∃ T : Submodule R M, IsCompl C.lineal T := sorry
    -- Submodule.exists_isCompl (K := R) (V := M) C.lineal
  obtain ⟨CoLin, h⟩ := hT
  use (C ⊓ CoLin)
  constructor
  · sorry
  · sorry

/-- A cone is a sum of a pointed cone and its lineality space. -/
-- NOTE: I just realzed that this is true in a boring sense: let D := span C \ C.lineal ∪ {0}
lemma exists_pointy_sup_lineal' (C : PointedCone R M) :
    ∃ D : PointedCone R M, (Submodule.span R D) ⊓ C.lineal = ⊥ ∧ D ⊔ C.lineal = C := by

  sorry

/-- This is a variant of `IsModularLattice.sup_inf_assoc_of_le`. While submodules form a modular
  lattice, pointed cones do in general not. -/
lemma sup_inf_assoc_of_le_submodule {C : PointedCone R M} (D : PointedCone R M)
    {S : Submodule R M} (hCS : C ≤ S) : C ⊔ (D ⊓ S) = (C ⊔ D) ⊓ S := by
  ext x
  simp [Submodule.mem_sup]
  constructor
  · intro h
    obtain ⟨y, hy, z, ⟨hz, hz'⟩, hyzx⟩ := h
    exact ⟨⟨y, hy, z, hz, hyzx⟩, by
      rw [← hyzx]; exact S.add_mem (hCS hy) hz' ⟩
  · intro h
    obtain ⟨⟨y, hy, z, hz, hyzx⟩, hx⟩ := h
    exact ⟨y, hy, z, ⟨hz, by
      rw [← add_left_cancel_iff (a := -y), neg_add_cancel_left] at hyzx
      rw [hyzx]
      specialize hCS hy
      rw [Submodule.restrictScalars_mem, ← neg_mem_iff] at hCS
      exact S.add_mem hCS hx
    ⟩, hyzx⟩

end Ring_AddCommGroup

end PointedCone
