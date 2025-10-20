/-
Copyright (c) 2025 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/

import Polyhedral.Mathlib.LinearAlgebra.BilinearMap
import Polyhedral.Mathlib.Algebra.Module.Submodule.Dual

open Module Function LinearMap

namespace Submodule

section CommSemiring

variable {R M N : Type*}
variable [CommSemiring R]
variable [AddCommMonoid M] [Module R M]
variable [AddCommMonoid N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R} -- bilinear pairing

variable (p)

/-- A co-finitely generated (CoFG) submodule is the dual of a finite set. This is in analogy to
  finitely generated (FG) submodules, which are the span of a finite set. -/
def CoFG (C : Submodule R N) : Prop := ∃ s : Finset M, dual p s = C

/-- The dual of a `Finset` is co-FG. -/
lemma cofg_of_finset (s : Finset M) : (dual p s).CoFG p := by use s

/-- The dual of a finite set is co-FG. -/
lemma cofg_of_finite {s : Set M} (hs : s.Finite) : (dual p s).CoFG p := by
  use hs.toFinset; simp

/-- The dual of an FG-cone is co-FG. -/
lemma cofg_of_fg {S : Submodule R M} (hS : S.FG) : (dual p S).CoFG p := by
  obtain ⟨s, rfl⟩ := hS
  use s; rw [← dual_span]

variable {p}

lemma cofg_inf (S T : Submodule R N) (hS : S.CoFG p) (hT : T.CoFG p) : (S ⊓ T).CoFG p
    := by classical
  obtain ⟨s, rfl⟩ := hS
  obtain ⟨t, rfl⟩ := hT
  use s ∪ t; rw [Finset.coe_union, dual_union]

-- We probably want to show stronger that `span R s` and `dual p.flip t` are complementary
-- lemma exists_finite_span_inf_dual_eq_bot (s : Finset M) :
--     ∃ t : Finset N, span R s ⊓ dual p.flip t = ⊥ := by
--   classical
--   induction s using Finset.induction with
--   | empty => use ∅; simp
--   | insert w s hws hs =>
--     obtain ⟨t, ht⟩ := hs
--     by_cases w = 0
--     case pos hw => use t; simp [hw, ht]
--     case neg hw =>
--       have h : p w ≠ 0 := fun h => hw (hp (by simp [h]))
--       have h : ∃ x, p w x ≠ 0 := by
--         by_contra H; apply h; ext x; by_contra hx; apply H; use x; exact hx
--       let r := h.choose
--       have hr : p w r ≠ 0 := Exists.choose_spec h
--       use insert r t
--       rw [Finset.coe_insert, Finset.coe_insert, span_insert, dual_insert]
--       -- distribute, reshuffle and exact `ht`
--       sorry

/-- The top submodule is CoFG. -/
lemma cofg_top : (⊤ : Submodule R N).CoFG p := ⟨⊥, by simp⟩

/-- The top submodule is CoFG. -/
lemma cofg_bot [Module.Finite R N] : (⊥ : Submodule R N).CoFG p := by
  -- obtain ⟨s, hs⟩ := fg_top ⊤
  -- use
  sorry

/-- The double dual of a CoFG submodule is itself. -/
lemma cofg_dual_dual_flip {S : Submodule R M} (hS : S.CoFG p.flip) :
    dual p.flip (dual p S) = S := by
  obtain ⟨s, rfl⟩ := hS
  rw [dual_flip_dual_dual_flip]

/-- The double dual of a CoFG submodule is itself. -/
lemma cofg_dual_flip_dual {S : Submodule R N} (hS : S.CoFG p) : dual p (dual p.flip S) = S := by
  obtain ⟨s, rfl⟩ := hS
  rw [dual_dual_flip_dual]

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}

variable (p)

variable [Fact p.IsFaithfulPair] in
/-- For an FG submodule `S`, there exists a CoFG submodule `T` so that `S ⊓ T = ⊥`. -/
lemma FG.exists_cofg_inf_bot {S : Submodule R N} (hS : S.FG) :
    ∃ T : Submodule R N, T.CoFG p ∧ S ⊓ T = ⊥ := by classical
  obtain ⟨g, hg⟩ : Fact p.IsFaithfulPair := inferInstance
  use dual p (Submodule.map g S)
  constructor
  · exact cofg_of_fg p (Submodule.FG.map g hS)
  · rw [dual_bilin_dual_id_submodule, ← map_comp, ← dual_bilin_dual_id_submodule]
    ext x
    simp only [mem_inf, mem_dual, SetLike.mem_coe, mem_bot]
    constructor
    · intro hS; exact (hg x) (hS.2 hS.1).symm
    · simp +contextual

lemma cofg_of_fg_sup_cofg {C D : Submodule R N} (hC : C.FG) (hD : D.CoFG p) : (C ⊔ D).CoFG p := by
  -- classical
  -- obtain ⟨_, b⟩ := Free.exists_basis R M
  -- obtain ⟨s, rfl⟩ := hC
  -- induction s using Finset.induction with
  -- | empty => simp [hD]
  -- | insert w s hws hs =>
  --   obtain ⟨t, ht⟩ := hs
  --   use insert (b.toDual w) t
  --   simp [span_insert, sup_assoc, ← ht]
  --   simp [dual_insert]
  --   rw [← dual_union]
  --   ext x
  --   simp
    sorry
-- omit [Free R M] [LinearOrder R] [IsStrictOrderedRing R] in
-- lemma CoFG.cofg_id_of_cofg_toDual {ι : Type*} [DecidableEq ι] {S : Submodule R M}
--      {b : Basis ι R M} (hS : S.CoFG b.toDual) : S.CoFG .id := by classical
--   obtain ⟨s, rfl⟩ := hS
--   use Finset.image b.toDual s
--   ext x; simp

-- Q: Is this true? If so, also implement with `IsCompl`.
lemma exists_cofg_sup_top {S : Submodule R N} (hS : S.FG) :
    ∃ T : Submodule R N, T.CoFG p ∧ S ⊔ T = ⊤ := by
  -- classical
  -- obtain ⟨_, b⟩ := Free.exists_basis R M
  -- use dual b.toDual S
  -- constructor
  -- · exact Submodule.cofg_of_fg _ hS
  -- · ext x
  --   simp only [mem_sup, mem_dual, SetLike.mem_coe, mem_top, iff_true]
  sorry

lemma FG.exists_cofg_inf_of_le {S S' : Submodule R N} (hS : S.FG) (hS' : S'.FG) (hSS' : S ≤ S') :
    ∃ T : Submodule R N, T.CoFG p ∧ S' ⊓ T = S := by sorry
  -- classical
  -- obtain ⟨s, rfl⟩ := hS
  -- induction s using Finset.induction with
  -- | empty => simp [exists_cofg_inf_bot hS']
  -- | insert w s hws hs =>
  --   obtain ⟨t, ht⟩ := hs
  --   use (auxGenSet .id t.toSet w).toFinset
  --   simp [span_insert, sup_assoc, ← ht]
  --   exact dual_auxGenSet t.finite_toSet
  --   sorry

variable {p}

lemma fg_of_cofg_inf_fg {S T : Submodule R N} (hS : S.CoFG p) (hT : S.FG) : (S ⊓ T).FG :=
  sorry

lemma cofg_of_cofg_inf_fg {S T : Submodule R N} (hS : S.CoFG p) (hT : S.FG) : (S ⊔ T).CoFG p :=
  sorry

-- ### HIGH PRIORITY! This is needed in the cone theory!
lemma fg_dual_flip_dual {S : Submodule R M} (hS : S.FG) : dual p.flip (dual p S) = S := by sorry

-- ### HIGH PRIORITY! This is needed in the cone theory!
lemma fg_dual_dual_flip {S : Submodule R N} (hS : S.FG) : dual p (dual p.flip S) = S := by sorry

end CommRing

section Function

variable {R : Type*} [CommSemiring R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {M' : Type*} [AddCommGroup M'] [Module R M']
variable {N' : Type*} [AddCommGroup N'] [Module R N']
variable {p : M →ₗ[R] N →ₗ[R] R}

/- TODO: generalize to arbitrary pairings. -/

lemma map_dual (f : M →ₗ[R] M') (C : Submodule R M) :
    dual (Dual.eval R M') (map f C) = comap f.dualMap (dual (Dual.eval R M) C) := by
  ext x; simp

-- lemma map_dual' (f : (Dual R M) →ₗ[R] (Dual R E')) (C : Submodule R (Dual R M)) :
--     dual .id (map f C) = comap f.dualMap (dual .id C) := by
--   ext x; simp

end Function

end Submodule
