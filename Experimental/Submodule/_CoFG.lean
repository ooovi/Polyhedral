/-
Copyright (c) 2025 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/

import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.PerfectPairing.Basic

import Polyhedral.Mathlib.Algebra.Module.Submodule.Basic
import Polyhedral.Mathlib.Algebra.Module.Submodule.Dual
import Polyhedral.Mathlib.LinearAlgebra.Dual.Basis

open Module

namespace Submodule

section CoFG

variable {R E F : Type*}
variable [CommSemiring R]
variable [AddCommMonoid E] [Module R E]
variable [AddCommMonoid F] [Module R F]
variable {p : E →ₗ[R] F →ₗ[R] R} -- bilinear pairing

-- def FG (N : Submodule R M) : Prop :=
--   ∃ S : Finset M, Submodule.span R ↑S = N
def CoFG (S : Submodule R E) : Prop :=
  ∃ s : Finset (Dual R E), dual .id s = S

variable (p)

/-- The dual of a `Finset` is co-FG. -/
lemma cofg_of_finset (s : Finset E) : (dual p s).CoFG := by
  classical
  use Finset.image p s
  simp [dual_bilin_dual_id]

/-- The dual of a finite set is co-FG. -/
lemma cofg_of_finite {s : Set E} (hs : s.Finite) : (dual p s).CoFG := by
  classical
  use Finset.image p hs.toFinset
  simp [dual_bilin_dual_id]

/-- The dual of an FG-cone is co-FG. -/
lemma cofg_of_fg {C : Submodule R E} (hC : C.FG) : (dual p C).CoFG := by
  obtain ⟨s, hs⟩ := hC
  rw [← hs, dual_span]
  exact cofg_of_finset p _

section IsPerfPair

variable {R E F : Type*}
variable [CommRing R]
variable [AddCommGroup E] [Module R E]
variable [AddCommGroup F] [Module R F]
variable {p : E →ₗ[R] F →ₗ[R] R} [p.IsPerfPair]

open Function

variable (p)

/- TODO: all theorems in this section only need that `p.flip` is surjective
  rather than full `p.IsPerfPair`. Perhaps implement this when typeclasses are
  available ? -/

lemma CoFG.exists_finset_dual {C : Submodule R E} (hC : C.CoFG) :
    ∃ s : Finset F, dual p.flip s = C := by
  classical
  obtain ⟨s, rfl⟩ := hC
  use s.image <| surjInv (LinearMap.IsPerfPair.bijective_right p).surjective
  rw [Finset.coe_image, dual_bilin_dual_id, ← Set.image_comp, comp_surjInv, Set.image_id]

lemma CoFG.exists_finite_dual {C : Submodule R E} (hC : C.CoFG) :
    ∃ s : Set F, s.Finite ∧ dual p.flip s = C := by
  obtain ⟨s, rfl⟩ := exists_finset_dual (p := p) hC
  use s; simp

lemma CoFG.exists_fg_dual {C : Submodule R E} (hC : C.CoFG) :
    ∃ S : Submodule R F, S.FG ∧ dual p.flip S = C := by
  obtain ⟨s, rfl⟩ := exists_finset_dual (p := p) hC
  use span R s; simp [fg_span]

end IsPerfPair

-- NOTE: converse is not true
-- @[deprecated cofg_of_finset (since := "2025-10-10")]
-- lemma cofg_intro (N : Submodule R F) (hN : ∃ S : Finset E, dual p S = N) : N.CoFG := by
--   classical
--   obtain ⟨S, hS⟩ := hN
--   use Finset.image p S
--   rw [Finset.coe_image, ← hS, ← dual_bilin_dual_id]

-- @[deprecated cofg_of_fg (since := "2025-10-10")]
-- lemma cofg_of_dual_fg (N : Submodule R F) (hN : ∃ M : Submodule R E, M.FG ∧ dual p M = N) :
--     N.CoFG := by
--   obtain ⟨M, ⟨S, hS⟩, hM⟩ := hN
--   refine cofg_intro (E := E) (p := p) N ?_
--   exact ⟨S, by rw [← dual_span, hS, hM]⟩

-- @[deprecated cofg_of_fg (since := "2025-10-10")]
-- lemma cofg_of_dual_fg' (N : Submodule R F) (M : Submodule R E) (hM : M.FG) (hN : dual p M = N) :
--     N.CoFG := cofg_of_dual_fg N ⟨M, hM, hN⟩

-- -- NOTE: converse not true in general (but true over fields)
-- variable (p) in
-- @[deprecated cofg_of_fg (since := "2025-10-10")]
-- lemma dual_cofg_of_fg {N : Submodule R E} (hN : N.FG) : (dual p N).CoFG
--   := cofg_of_dual_fg' _ N hN rfl

-- @[deprecated CoFG.exists_fg_dual (since := "2025-10-10")]
-- lemma cofg_def_fg (N : Submodule R E) (hN : N.CoFG) :
--     ∃ M : Submodule R (Dual R E), M.FG ∧ dual .id M = N := by
--   obtain ⟨S, hS⟩ := hN
--   exact ⟨span R S, ⟨S, rfl⟩, by rw [dual_span, hS]⟩

lemma cofg_inter (M N : Submodule R E) (hM : M.CoFG) (hN : N.CoFG) : (M ⊓ N).CoFG := by
  obtain ⟨S, rfl⟩ := hM
  obtain ⟨T, rfl⟩ := hN
  classical
  use S ∪ T; rw [Finset.coe_union, dual_union]

-- @[simp]
-- lemma dual_fg_iff_cofg (N : Submodule R E) : N.CoFG → (dual p N).FG := sorry

open Function

-- We probably want to show stronger that `span R s` and `dual p.flip t` are complementary
-- lemma exists_finite_span_inf_dual_eq_bot (s : Finset E) :
--     ∃ t : Finset F, span R s ⊓ dual p.flip t = ⊥ := by
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

lemma cofg_top : (⊤ : Submodule R E).CoFG := ⟨⊥, by simp⟩

/-- If a submodule is co-FG, then it equals its double dual. -/
lemma cofg_dual_dual {S : Submodule R E} (hS : S.CoFG) : dual .id (dual (Dual.eval R E) S) = S := by
  obtain ⟨s, rfl⟩ := hS
  exact dual_flip_dual_dual_flip (p := Dual.eval R E) s

/-- If a submodule is co-FG, then so is its double-dual. -/
lemma dual_dual_cofg {S : Submodule R E} (hS : S.CoFG) :
    (dual .id (dual (Dual.eval R E) S) : Submodule R E).CoFG := by
  rw [cofg_dual_dual hS]; exact hS

section Module.Free

-- lemma dual_dual {S : Submodule R E} (hS : S.CoFG) : (dual p.flip (dual p S)).CoFG := by
--   obtain ⟨s, rfl⟩ := hS
--   exact dual_flip_dual_dual_flip (p := Dual.eval R E) s

-- TODO: maybe in this section we can do with less assumptions. Eg Module.Free and something that
--  ensures that submodules are projective. But I don't know.
variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
variable {E : Type*} [AddCommGroup E] [Module R E] [Free R E]

section Field

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable {E : Type*} [AddCommGroup E] [Module R E] [Free R E]

lemma cofg_of_cofg_sup {S T : Submodule R E} (hS : S.CoFG) : (S ⊔ T).CoFG := by
  classical
  -- obtain ⟨W, hW⟩ := exists_isCompl (S ⊔ T)
  obtain ⟨p, hp⟩ := (S ⊔ T).exists_isProj -- IsCompl.projection hW
  obtain ⟨s, hS⟩ := hS
  use Finset.image (.id - p).dualMap s
  simp [← dual_map', hS]
  have hker : LinearMap.ker (.id - p) = S ⊔ T := sorry
  have h := Submodule.comap_map_eq (f := .id - p) (p := S)
  sorry

  -- let S' := span R s ⊓ dual (Dual.eval R E) T
  -- obtain ⟨p, hp⟩ := exists_isProj S'
  -- use Finset.image p s
  -- simp
  -- rw [← dual_map' (f := p.dualMap)]

  -- let S' : Submodule R (Dual R E) := span R s'
  -- let S'' := restrict S' (dual (Dual.eval R E) T)
  -- let s'' : Set S' := {x : S' | (x : Dual R E) ∈ s'}
  -- have hs'' : s''.Finite := sorry
  -- obtain ⟨p, hp⟩ := exists_isProj S''
  -- use (Finset.image S'.subtype (Finset.image p hs''.toFinset))
  -- simp
  -- ext x
  -- simp [mem_sup]
  -- constructor
  -- · sorry
  -- · intro h
  --   obtain ⟨y, hy⟩ := h
  --   sorry

end Field

lemma cofg_of_fg_sup_cofg {C D : Submodule R E} (hC : C.FG) (hD : D.CoFG) : (C ⊔ D).CoFG := by
  classical
  obtain ⟨_, b⟩ := Free.exists_basis R E
  obtain ⟨s, rfl⟩ := hC
  induction s using Finset.induction with
  | empty => simp [hD]
  | insert w s hws hs =>
    obtain ⟨t, ht⟩ := hs
    use insert (b.toDual w) t
    simp [span_insert, sup_assoc, ← ht]
    simp [dual_insert]
    rw [← dual_union]
    ext x
    simp
    sorry

-- Q: Does this lemma really depend on a linear order on `R`? Can it be proven without?
--  Currently the order is needed for `Dual.toDual_eq_zero`.
--  It would further be interesting to know whether any complemented pair (which exists in a
--  in the case of a field; use `ComplementedLattice`) with on FG has the other one CoFG.
/-- For an FG submodule `S`, there exists a CoFG submodule `T` so that `S ⊓ T = ⊥`. -/
lemma FG.exists_cofg_inf_bot {S : Submodule R E} (hS : S.FG) :
    ∃ T : Submodule R E, T.CoFG ∧ S ⊓ T = ⊥ := by
  classical
  obtain ⟨_, b⟩ := Free.exists_basis R E
  use dual b.toDual S
  constructor
  · exact Submodule.cofg_of_fg _ hS
  · ext x
    simp only [mem_inf, mem_dual, SetLike.mem_coe, mem_bot]
    constructor
    · intro hS; exact Dual.toDual_eq_zero (hS.2 hS.1).symm
    · simp +contextual

-- Q: is this true? If so, also implement with `IsCompl`.
lemma exists_cofg_sup_top {S : Submodule R E} (hS : S.FG) :
    ∃ T : Submodule R E, T.CoFG ∧ S ⊔ T = ⊤ := by
  classical
  obtain ⟨_, b⟩ := Free.exists_basis R E
  use dual b.toDual S
  constructor
  · exact Submodule.cofg_of_fg _ hS
  · ext x
    simp only [mem_sup, mem_dual, SetLike.mem_coe, mem_top, iff_true]
    sorry

lemma FG.exists_cofg_inf_of_le {S S' : Submodule R E} (hS : S.FG) (hS' : S'.FG) (hSS' : S ≤ S') :
    ∃ T : Submodule R E, T.CoFG ∧ S' ⊓ T = S := by sorry
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

lemma fg_of_cofg_inf_fg {S T : Submodule R E} (hS : S.CoFG) (hT : S.FG) : (S ⊓ T).FG :=
  sorry

lemma cofg_of_cofg_inf_fg {S T : Submodule R E} (hS : S.CoFG) (hT : S.FG) : (S ⊔ T).CoFG :=
  sorry

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable {E : Type*} [AddCommGroup E] [Module R E] [Free R E]
variable {F : Type*} [AddCommGroup F] [Module R F] [Free R F]

variable {p : E →ₗ[R] F →ₗ[R] R} -- bilinear pairing

-- ### HIGH PRIORITY! Prove this!
lemma fg_dual_dual_flip {S : Submodule R E} (hS : S.FG) : dual p.flip (dual p S) = S := by sorry

end Module.Free

variable {E' F' : Type*}
  [AddCommGroup E'] [Module R E']
  [AddCommGroup F'] [Module R F']
  -- {p' : E' →ₗ[R] F' →ₗ[R] R}

lemma map_dual (f : E →ₗ[R] E') (C : Submodule R E) :
    dual (Dual.eval R E') (map f C) = comap f.dualMap (dual (Dual.eval R E) C) := by
  ext x; simp

-- lemma map_dual' (f : (Dual R E) →ₗ[R] (Dual R E')) (C : Submodule R (Dual R E)) :
--     dual .id (map f C) = comap f.dualMap (dual .id C) := by
--   ext x; simp

end CoFG

end Submodule
