/-
Copyright (c) 2025 Martin Winter, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter, Yaël Dillies
-/
import Polyhedral.Mathlib.LinearAlgebra.BilinearMap

import Polyhedral.PR.Dual.Dual_PR

/-!
# Dual closed submodules

Given a bilinear pairing `p` between two `R`-modules `M` and `N`, a submodule is dual closed if
it is identical to its own double dual.

In a topological context this states that the submodule us closed in the weak topology. Results
about dual closed submodules hence generalize to the analytic setting.

Other examples of dual closed cones are FG (and DualFG) cones, hence polyhedral cones.

## Implementation notes

...

-/

open Module Function LinearMap Pointwise Set OrderDual

namespace Submodule

variable {R M N : Type*}
  [CommSemiring R]
  [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]
  {p : M →ₗ[R] N →ₗ[R] R} {s t : Set M} {y : N}

variable (p) in
abbrev DualClosed (S : Submodule R M) := dual p.flip (dual p S) = S

@[simp] lemma DualClosed.def {S : Submodule R M} (hS : DualClosed p S) :
     dual p.flip (dual p S) = S := hS

lemma DualClosed.def_iff {S : Submodule R M} :
    DualClosed p S ↔ dual p.flip (dual p S) = S := by rfl

variable (p) in
@[simp] lemma dual_dualClosed (s : Set M) : (dual p s).DualClosed p.flip := by
  simp [DualClosed, flip_flip, dual_dual_flip_dual]

variable (p) in
@[simp] lemma dual_flip_IsDualClosed (s : Set N) : (dual p.flip s).DualClosed p
    := by simp [DualClosed]

lemma DualClosed.dual_inj {S T : Submodule R M} (hS : S.DualClosed p) (hT : T.DualClosed p)
    (hST : dual p S = dual p T) : S = T := by
  rw [← hS, ← hT, hST]

lemma DualClosed.dual_antitone_rev {S T : Submodule R M}
    (hS : S.DualClosed p) (hT : T.DualClosed p)
      (hST : dual p S ≤ dual p T) : T ≤ S := by
  rw [← hS, ← hT]; exact dual_antitone hST

lemma DualClosed.dual_le_of_dual_le {S : Submodule R M} {T : Submodule R N}
    (hS : S.DualClosed p) (hST : dual p S ≤ T) : dual p.flip T ≤ S := by
  rw [← hS]; exact dual_antitone hST

-- NOTE: This is the characterizing property of an antitone GaloisConnection.
lemma dual_le_iff_dual_le_of_dualClosed {S : Submodule R M} {T : Submodule R N}
    (hS : S.DualClosed p) (hT : T.DualClosed p.flip) :
      dual p S ≤ T ↔ dual p.flip T ≤ S
    := ⟨hS.dual_le_of_dual_le, hT.dual_le_of_dual_le⟩

@[simp] lemma DualClosed.dual_inj_iff {S T : Submodule R M} (hS : S.DualClosed p)
    (hT : T.DualClosed p) : dual p S = dual p T ↔ S = T := ⟨dual_inj hS hT, by intro h; congr ⟩

lemma DualClosed.exists_of_dual_flip {S : Submodule R M} (hS : S.DualClosed p) :
    ∃ T : Submodule R N, T.DualClosed p.flip ∧ dual p.flip T = S
  := ⟨dual p S, by simp [DualClosed, hS.def]⟩

lemma DualClosed.exists_of_dual {S : Submodule R N} (hS : S.DualClosed p.flip) :
    ∃ T : Submodule R M, T.DualClosed p ∧ dual p T = S := by
  rw [← flip_flip p]; exact hS.exists_of_dual_flip

variable (p) in
lemma dualClosed_top : DualClosed p ⊤ := by
  rw [DualClosed, le_antisymm_iff, and_comm]
  exact ⟨subset_dual_dual, by simp only [top_coe, le_top]⟩

variable (p) in
@[simp] lemma dual_dual_top : dual p.flip (dual p ⊤) = ⊤
    := dualClosed_top p

variable [Fact p.SeparatingLeft] in
@[simp] lemma dualClosed_bot : DualClosed p ⊥ := by simp [DualClosed]

variable (p) [Fact p.SeparatingLeft] in
-- @[simp]
lemma dual_dual_bot : dual p.flip (dual p 0) = ⊥ := by simp

@[simp] lemma dualClosed_ker : DualClosed p (ker p) := by
  simpa [← dual_flip_univ_ker] using dual_flip_IsDualClosed p _

lemma DualClosed.ker_le {S : Submodule R M} (hS : S.DualClosed p) : ker p ≤ S := by
  rw [← hS]; exact ker_le_dual_flip _

@[simp] lemma dual_dual_ker : dual p.flip (dual p (ker p)) = ker p := by simp [dual_univ_ker]

lemma DualClosed.inf {S T : Submodule R M}
    (hS : S.DualClosed p) (hT : T.DualClosed p) : (S ⊓ T).DualClosed p := by
  rw [← hS, ← hT, DualClosed, ← dual_sup_dual_eq_inf_dual, dual_flip_dual_dual_flip]

alias inf_dualClosed := DualClosed.inf

lemma sInf_dualClosed {s : Set (Submodule R M)} (hS : ∀ S ∈ s, S.DualClosed p) :
    (sInf s).DualClosed p := by
  have hs : s = dual p.flip '' (SetLike.coe '' (dual p '' (SetLike.coe '' s))) := by
    ext T; simp only [mem_image, exists_exists_and_eq_and]
    constructor
    · exact fun hT => ⟨T, hT, hS T hT⟩
    · intro h
      obtain ⟨t, hts, ht⟩ := h
      simpa [← ht, hS t hts] using hts
  rw [hs, ← dual_sSup_sInf_dual]
  exact dual_dualClosed _ _

-- variable (p) in
-- /-- The span of a set `s ⊆ M` is the smallest submodule of M that contains `s`. -/
-- def dualClosure (s : Set M) : Submodule R M := dual p.flip (dual p s)

-- lemma dualClosure_dualClosed (s : Set M) : (dualClosure p s).DualClosed p := by
--   simp [dualClosure, DualClosed, dual_dual_flip_dual]

-- variable (p) in
-- theorem DualClosed.dualClosure_eq_sInf (s : Set M) :
--     dualClosure p s = sInf { S : Submodule R M | S.DualClosed p ∧ s ⊆ S } := by
--   rw [Eq.comm, le_antisymm_iff]
--   constructor
--   · exact sInf_le ⟨dual_IsDualClosed _ _, subset_dual_dual⟩
--   rw [SetLike.le_def]
--   intro x hx
--   simp only [mem_sInf, mem_setOf_eq, and_imp]
--   intro T hT hsT
--   rw [← hT]
--   exact (dual_dual_mono p hsT) hx

-- theorem DualClosed.eq_sInf {S : Submodule R M} (hS : S.DualClosed p) :
--     S = sInf { T : Submodule R M | T.DualClosed p ∧ S ≤ T } := by
--   nth_rw 1 [← hS]; exact dualClosure_eq_sInf p S

/- NOTE: This seems trivial. Perhaps this should not be its own lemma. 1. Find a shorter proof.
  Then replace where it is used (somewhere relating lineal). -/
/-- A dual closed submodule is the infiumum of all dual closed submodules that contain it. -/
theorem DualClosed.eq_sInf {S : Submodule R M} (hS : S.DualClosed p) :
    S = sInf { T : Submodule R M | T.DualClosed p ∧ S ≤ T } := by
  rw [Eq.comm, le_antisymm_iff]
  constructor
  · exact sInf_le ⟨hS, by simp⟩
  simp only [SetLike.le_def, mem_sInf, mem_setOf_eq, and_imp]
  intro x hx T hT hsT
  rw [← hT]; rw [← hS] at hx
  exact (dual_dual_mono p hsT) hx

-- !! Not true: S = ⊤, T = not dual closed
-- protected lemma DualClosed.inf {S T : Submodule R M} (hS : S.DualClosed p) :
--     (S ⊓ T).DualClosed p := by
--   rw [← hS]
--   sorry

-- This seems to be NOT TRUE!
-- lemma DualClosed.sup {S T : Submodule R M} (hS : S.DualClosed p) (hT : T.DualClosed p) :
--     (S ⊔ T).DualClosed p := by
--   obtain ⟨S', hSdc, rfl⟩ := hS.exists_of_dual_flip
--   obtain ⟨T', hTdc, rfl⟩ := hT.exists_of_dual_flip
--   unfold DualClosed
--   sorry

-- alias sup_dualClosed := DualClosed.sup

lemma dual_inf_dual_sup_dual' {S T : Submodule R M} (hS : S.DualClosed p)
    (hT : T.DualClosed p) : dual p (S ∩ T) = dual p S ⊔ dual p T := by
  rw [le_antisymm_iff]
  constructor
  · rw [SetLike.le_def]
    simp [mem_sup]
    intro x hx
    sorry
  · sorry -- easy

  -- refine DualClosed.dual_inj (p := p) hS hT ?_
  -- rw [← DualClosed.dual_inj_iff hS hT]
  -- rw [← hS.def]

lemma dual_inf_dual_sup_dual_of_dualClosed {S T : Submodule R M}
    (hS : S.DualClosed p) (hT : T.DualClosed p) :
    dual p (S ⊓ T : Submodule R M) = dual p S ⊔ dual p T := by

  sorry

-- can be applied to polyhedral cones.
lemma dual_inf_dual_sup_dual_of_dualClosed' (S T : Submodule R M)
    (hS : S.DualClosed p) (hT : T.DualClosed p) (hST : (dual p S ⊔ dual p T).DualClosed p.flip) :
      dual p (S ⊓ T) = dual p S ⊔ dual p T := by
  nth_rw 1 [← hS, ← hT]
  simp only [inf_eq_inter, ← coe_inf, ← dual_union, ← dual_sup]
  nth_rw 1 [← flip_flip p]
  rw [hST]

section WeakDualClosed

variable (p) in
abbrev WeakDualClosed (S : Submodule R M) := dual p.flip (dual p S) = S ⊔ ker p
-- equivalently (but not trivially so): DualClosed p (S ⊔ ker p)

variable {R M N : Type*}
  [CommRing R]
  [AddCommGroup M] [Module R M]
  [AddCommMonoid N] [Module R N]
  {p : M →ₗ[R] N →ₗ[R] R}

/- This can be useful because it is the more abstract version of the one for FG/FGDual cones. -/
lemma dual_inf_dual_sup_dual_of_dualClosed'' (S T : Submodule R M)
    (hS : S.DualClosed p) (hT : T.WeakDualClosed p)
    (hST : (dual p S ⊔ dual p T).WeakDualClosed p.flip) :
      dual p (S ∩ T) = dual p S ⊔ dual p T := by
  rw [← dual_union_ker, ← coe_inf, ← dual_sup, inf_sup_assoc_of_le]
  · nth_rw 1 [← hS, ← hT, ← flip_flip p]
    simp only [← dual_union, ← dual_sup, hST, sup_assoc, ker_le_dual, sup_of_le_left]
  exact hS.ker_le

end WeakDualClosed

---------------------

variable (p) in
lemma dual_dual_eval_le_dual_dual_bilin (s : Set M) :
    dual .id (dual (Dual.eval R M) s) ≤ dual p.flip (dual p s)
  := fun _ hx y hy => @hx (p.flip y) hy

lemma DualClosed.to_eval {S : Submodule R M} (hS : S.DualClosed p)
    : S.DualClosed (Dual.eval R M) := by
  have h := dual_dual_eval_le_dual_dual_bilin p S
  rw [hS] at h
  exact le_antisymm h subset_dual_dual

section Surjective

/- TODO: figure out what are the weakest conditions under which these results are true.
  is `IsPerfPair` really necessary? -/

variable {R M N : Type*}
  [CommRing R]
  [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]
  {p : M →ₗ[R] N →ₗ[R] R} [Fact (Surjective p.flip)]

variable (p) in
lemma dual_dual_bilin_eq_dual_dual_eval (s : Set M) :
    dual p.flip (dual p s) = dual .id (dual (Dual.eval R M) s) := by
  rw [le_antisymm_iff, and_comm]
  constructor
  · exact dual_dual_eval_le_dual_dual_bilin p s
  simp only [SetLike.le_def, mem_dual, SetLike.mem_coe, flip_apply, Dual.eval_apply, id_coe, id_eq]
  intro x hx y hy
  obtain ⟨x', hx'⟩ := (Fact.elim inferInstance : Surjective p.flip) y
  simp only [← hx', flip_apply] at hy
  specialize @hx x' hy
  rw [← flip_apply, hx'] at hx
  exact hx

variable (p) in
lemma DualClosed.to_bilin {S : Submodule R M} (hS : S.DualClosed (Dual.eval R M))
    : S.DualClosed p := by
  rw [DualClosed, dual_dual_bilin_eq_dual_dual_eval]
  exact hS

end Surjective

section Field

variable {R M N : Type*}
  [Field R]
  [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]
  {p : M →ₗ[R] N →ₗ[R] R}

variable (p)

-- TODO: do we need a `[Field R]`, or is `Surjective p` enough?
variable [Fact (Surjective p.flip)] in
/-- A submodule of a vector space is dual closed. -/
lemma dualClosed (S : Submodule R M) : S.DualClosed p := by
  apply DualClosed.to_bilin
  nth_rw 1 [DualClosed, Dual.eval, flip_flip]
  rw [dual_dualCoannihilator, dual_dualAnnihilator]
  exact Subspace.dualAnnihilator_dualCoannihilator_eq

-- -- TODO: do we need a `[Field R]`, or is `Surjective p` enough?
-- variable [Fact (Surjective p)] in
-- /-- Every submodule of a vector space is dual closed. -/
-- lemma dualClosed_flip (S : Submodule R N) : S.DualClosed p.flip := by
--   apply DualClosed.to_bilin
--   nth_rw 1 [DualClosed, Dual.eval, flip_flip]
--   rw [dual_dualCoannihilator, dual_dualAnnihilator]
--   exact Subspace.dualAnnihilator_dualCoannihilator_eq

-- variable [Fact (Surjective p.flip)] in
-- /-- Every submodule of a vector space is dual closed. -/
-- lemma dualClosed (S : Submodule R M) : S.DualClosed p := dualClosed_flip p.flip S

variable [Fact (Surjective p)] in
/-- Every submodule of a vector space is its own double dual. -/
@[simp] lemma dual_dual_flip (S : Submodule R N) : dual p (dual p.flip S) = S :=
    dualClosed p.flip S

variable [Fact (Surjective p.flip)] in
/-- Every submodule of a vector space is its own double dual. -/
@[simp] lemma dual_flip_dual (S : Submodule R M) : dual p.flip (dual p S) = S :=
    dual_dual_flip p.flip S

variable [Fact (Surjective p)] in
lemma exists_set_dual (S : Submodule R N) : ∃ s : Set M, dual p s = S := by
  use dual p.flip S; exact dual_dual_flip p S

-- do we really need perf pair?
-- We need something, but maybe faithful suffices
variable [p.IsPerfPair] in
lemma dual_inf_dual_sup_dual (S T : Submodule R M) :
    dual p (S ∩ T) = dual p S ⊔ dual p T := by
  nth_rw 1 [← dual_flip_dual p S]
  nth_rw 1 [← dual_flip_dual p T]
  rw [← coe_inf]
  rw [← dual_sup_dual_inf_dual]
  exact dual_dual_flip p _



-- ### HIGH PRIORITY! This is needed in the cone theory!

lemma exists_smul_of_ker_le_ker {p q : M →ₗ[R] R} (h : ker p ≤ ker q) :
    ∃ a : R, q = a • p := by
  by_cases H : p = 0
  · exact ⟨0, by simpa [H] using h⟩
  rw [LinearMap.ext_iff] at H
  simp at H
  obtain ⟨x, hx⟩ := H
  use q x / p x
  ext y
  simp
  -- using hx, rewrite goal to
  --   qy px - qx py = 0
  --   q (y px - x py) = 0
  -- which, via h, follows from
  --   p (y px - x px) = 0
  -- which is true because this is just
  --   px py - py px = 0
  sorry

variable [inst : Fact p.SeparatingLeft] in -- ! satisfied by both Dual.eval and .id
lemma dual_flip_dual_singleton (x : M) : dual p.flip (dual p {x}) = span R {x} := by
  ext y
  simp
  rw [mem_span_singleton]
  constructor
  · intro h
    obtain ⟨a, ha⟩ := exists_smul_of_ker_le_ker (fun _ hx => (h hx.symm).symm)
    use a
    rw [← LinearMap.map_smul] at ha
    have inj := inst.elim
    rw [separatingLeft_iff_ker_eq_bot, ker_eq_bot] at inj
    replace ha := inj ha
    exact ha.symm
  · intro h _ hz
    obtain ⟨_, rfl⟩ := h
    simp [← hz]

-- variable [Fact (Injective p)] in
-- lemma DualClosed.singleton (x : M) : (span R {x}).DualClosed p := by
--   sorry -- TODO: derive from `singleton_dual_flip_dual` above

-- variable [Fact p.IsFaithfulPair] in
-- /- NOTE: in a field and with a surjective pairing, every submodule is dual closed. But maybe
--   if the submodule is FG, we don't need the surjective pairing, but a faithful one suffices. -/
-- lemma FG.dual_flip_dual_of_finite (s : Finset M) :
--     dual p.flip (dual p s) = span R s := sorry -- Submodule.dual_flip_dual p S

-- variable [Fact p.IsFaithfulPair] in
-- /- NOTE: in a field and with a surjective pairing, every submodule is dual closed. But maybe
--   if the submodule is FG, we don't need the surjective pairing, but a faithful one suffices. -/
-- lemma FG.dual_flip_dual {S : Submodule R M} (hS : S.FG) :
--     dual p.flip (dual p S) = S := sorry -- Submodule.dual_flip_dual p S

-- variable [Fact p.IsFaithfulPair] in
-- lemma FG.dual_dual_flip {S : Submodule R N} (hS : S.FG) : dual p (dual p.flip S) = S := by sorry

-- variable [Fact p.flip.IsFaithfulPair] in
-- /-- The span of a finite set is dual closed. -/
-- lemma dualClosed_of_finite (s : Finset M) : DualClosed p (span R s) := by

--   sorry

-- variable [Fact p.flip.IsFaithfulPair] in
-- /-- An FG submodule is dual closed. -/
-- lemma FG.dualClosed {S : Submodule R M} (hS : S.FG) : S.DualClosed p := by
--   sorry

end Field

end Submodule
