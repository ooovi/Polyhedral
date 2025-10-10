import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.LinearAlgebra.SesquilinearForm
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.PerfectPairing.Basic

import Polyhedral.Toric.Mathlib.Geometry.Convex.Cone.Module
import Polyhedral.Toric.Mathlib.Geometry.Convex.Cone.Submodule_Dual

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

variable [DecidableEq (Dual R F)] in
/-- The dual of a `Finset` is co-FG. -/
lemma cofg_of_finset (s : Finset E) : (dual p s).CoFG := by
  use Finset.image p s
  simp [dual_bilin_dual_id]

variable [DecidableEq (Dual R F)] in
/-- The dual of a finite set is co-FG. -/
lemma cofg_of_finite {s : Set E} (hs : s.Finite) : (dual p s).CoFG := by
  use Finset.image p hs.toFinset
  simp [dual_bilin_dual_id]

variable [DecidableEq (Dual R F)] in
/-- The dual of an FG-cone is co-FG. -/
lemma cofg_of_fg {C : Submodule R E} (hC : C.FG) : (dual p C).CoFG := by
  obtain ⟨s, hs⟩ := hC
  rw [← hs, dual_span]
  exact cofg_of_finset _

section IsPerfPair

variable {R E F : Type*}
variable [CommRing R]
variable [AddCommGroup E] [Module R E]
variable [AddCommGroup F] [Module R F]
variable {p : E →ₗ[R] F →ₗ[R] R} [p.IsPerfPair]

open Function

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
@[deprecated cofg_of_finset (since := "2025-10-10")]
lemma cofg_intro (N : Submodule R F) (hN : ∃ S : Finset E, dual p S = N) : N.CoFG := by
  classical
  obtain ⟨S, hS⟩ := hN
  use Finset.image p S
  rw [Finset.coe_image, ← hS, ← dual_bilin_dual_id]

@[deprecated cofg_of_fg (since := "2025-10-10")]
lemma cofg_of_dual_fg (N : Submodule R F) (hN : ∃ M : Submodule R E, M.FG ∧ dual p M = N) :
    N.CoFG := by
  obtain ⟨M, ⟨S, hS⟩, hM⟩ := hN
  refine cofg_intro (E := E) (p := p) N ?_
  exact ⟨S, by rw [← dual_span, hS, hM]⟩

@[deprecated cofg_of_fg (since := "2025-10-10")]
lemma cofg_of_dual_fg' (N : Submodule R F) (M : Submodule R E) (hM : M.FG) (hN : dual p M = N) :
    N.CoFG := cofg_of_dual_fg N ⟨M, hM, hN⟩

-- NOTE: converse not true in general (but true over fields)
variable (p) in
@[deprecated cofg_of_fg (since := "2025-10-10")]
lemma dual_cofg_of_fg {N : Submodule R E} (hN : N.FG) : (dual p N).CoFG
  := cofg_of_dual_fg' _ N hN rfl

@[deprecated CoFG.exists_fg_dual (since := "2025-10-10")]
lemma cofg_def_fg (N : Submodule R E) (hN : N.CoFG) :
    ∃ M : Submodule R (Dual R E), M.FG ∧ dual .id M = N := by
  obtain ⟨S, hS⟩ := hN
  exact ⟨span R S, ⟨S, rfl⟩, by rw [dual_span, hS]⟩

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

section Dual

lemma dual_dual' {S : Submodule R E} (hS : S.CoFG) : dual .id (dual (Dual.eval R E) S) = S := by
  obtain ⟨s, rfl⟩ := hS
  exact dual_flip_dual_dual_flip (p := Dual.eval R E) s

-- lemma dual_dual {S : Submodule R E} (hS : S.CoFG) : (dual p.flip (dual p S)).CoFG := by
--   obtain ⟨s, rfl⟩ := hS
--   exact dual_flip_dual_dual_flip (p := Dual.eval R E) s

-- TODO: maybe in this section we can do with less assumptions. Eg Module.Free and something that
--  ensures that submodules are projective. But I don't know.
variable {R : Type*} [Field R]
variable {E : Type*} [AddCommGroup E] [Module R E]
-- variable [Module.Free R E]

lemma exists_finite_span_inf_dual_eq_bot (s : Finset E) :
    ∃ t : Finset (Dual R E), span R s ⊓ dual (M := Dual R E) .id t = ⊥ := by
  classical
  induction s using Finset.induction with
  | empty => use ∅; simp
  | insert w s hws hs =>
    obtain ⟨t, ht⟩ := hs
    by_cases w = 0
    case pos hw => use t; simp [hw, ht]
    case neg hw =>
      --let S' := map (Dual.eval R E) S
      have hr : ∃ r : Dual R E, r w ≠ 0 := by
        by_contra H; push_neg at H
        exact hw <| (forall_dual_apply_eq_zero_iff R w).mp H
      let r := hr.choose
      have hr : r w ≠ 0 := Exists.choose_spec hr
      use insert r t
      rw [Finset.coe_insert, Finset.coe_insert, span_insert, dual_insert]
      ext x
      simp
      constructor
      · intro ⟨hx1, hx2, hx3⟩         -- rw [Module.forall_dual_apply_eq_zero_iff] at hh
        sorry
      · simp +contextual

-- lemma foo' {S : Submodule R E} (hS : S.FG) :
--     ∃ T : Submodule R E, T.CoFG ∧ S ⊓ T = ⊥ := by
--   obtain ⟨s, rfl⟩ := hS
--   obtain ⟨t, ht⟩ := exists_finite_span_inf_dual_eq_bot R s
--   exact ⟨dual .id t.toSet, ⟨t, by simp⟩ , ht⟩

lemma exists_cofg_inf_bot {S : Submodule R E} (hS : S.FG) :
    ∃ T : Submodule R E, T.CoFG ∧ S ⊓ T = ⊥ := by
  obtain ⟨f, hinj⟩ := Module.Dual.exists_embed R E
  use dual .id (map f S)
  constructor
  · exact dual_cofg_of_fg .id (Submodule.FG.map _ hS)
  · ext x
    simp only [map_coe, mem_inf, mem_dual, Set.mem_image, SetLike.mem_coe, LinearMap.id_coe, id_eq,
      forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, mem_bot]
    constructor
    · intro ⟨hx, hSf⟩
      let x' : S := ⟨x, hx⟩
      have h : x = 0 ↔ x' = 0 := by sorry
      rw [h]
      rw [← forall_dual_apply_eq_zero_iff (K := R)]
      intro b
      specialize hSf

      sorry
    · simp +contextual

lemma exists_cofg_sup_top {S : Submodule R E} (hS : S.FG) :
    ∃ T : Submodule R E, T.CoFG ∧ S ⊔ T = ⊤ := by
  obtain ⟨f, hinj⟩ := Module.Dual.exists_embed R E
  use dual .id (map f S)
  constructor
  · exact dual_cofg_of_fg .id (Submodule.FG.map _ hS)
  · ext x
    simp [map_coe, mem_sup]
    -- ???
    sorry

lemma FG.comple_cofg {S T : Submodule R E} (hS : S.FG) (hST : IsCompl S T) : T.CoFG := by

  sorry

lemma FG.exists_isCompl {S : Submodule R E} (hS : S.FG) :
    ∃ T : Submodule R E, T.CoFG ∧ IsCompl S T := by
  -- Submodule.exists_isCompl
  sorry

end Dual

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
