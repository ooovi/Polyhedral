/-
Copyright (c) 2025 Martin Winter, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter, Yaël Dillies
-/

import Polyhedral.PR.Dual.Dual_PR
import Polyhedral.PR.BilinearMap.Dual_PR

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

section CommSemiring

variable {R M N : Type*}
  [CommSemiring R]
  [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]
  {p : M →ₗ[R] N →ₗ[R] R}

variable (p) in
/-- A submodule is dual closed w.r.t. a bilinear pairing if it is identical to its own double dual
  under this pairing. -/
abbrev DualClosed (S : Submodule R M) := dual p.flip (dual p S) = S

@[simp] lemma DualClosed.dual_dual_eq_self {S : Submodule R M} (hS : DualClosed p S) :
     dual p.flip (dual p S) = S := hS

variable (p) in
/-- The dual of a submlodule is dual closed. -/
@[simp] lemma DualClosed.of_dual (s : Set M) : (dual p s).DualClosed p.flip := by
  simp [DualClosed, flip_flip, dual_dual_flip_dual]

variable (p) in
/-- The dual of a submlodule is dual closed. -/
@[simp] lemma DualClosed.of_dual_flip (s : Set N) : (dual p.flip s).DualClosed p
    := by simp [DualClosed]

/-- The duality operator on dual closed submodules is injective. -/
lemma DualClosed.dual_inj {S T : Submodule R M} (hS : S.DualClosed p) (hT : T.DualClosed p)
    (hST : dual p S = dual p T) : S = T := by
  rw [← hS, ← hT, hST]

lemma DualClosed.dual_anti_rev {S T : Submodule R M}
    (hS : S.DualClosed p) (hT : T.DualClosed p)
      (hST : dual p S ≤ dual p T) : T ≤ S := by
  rw [← hS, ← hT]; exact dual_antitone hST

lemma DualClosed.dual_flip_le_of_dual_le {S : Submodule R M} {T : Submodule R N}
    (hS : S.DualClosed p) (hST : dual p S ≤ T) : dual p.flip T ≤ S := by
  rw [← hS]; exact dual_antitone hST

/-- The characterizing property of `dual` as a Galois connection on dual closed submodules. -/
lemma DualClosed.dual_flip_le_iff_dual_le {S : Submodule R M} {T : Submodule R N}
    (hS : S.DualClosed p) (hT : T.DualClosed p.flip) :
      dual p S ≤ T ↔ dual p.flip T ≤ S
    := ⟨hS.dual_flip_le_of_dual_le, hT.dual_flip_le_of_dual_le⟩

@[simp] lemma DualClosed.dual_inj_iff {S T : Submodule R M} (hS : S.DualClosed p)
    (hT : T.DualClosed p) : dual p S = dual p T ↔ S = T := ⟨dual_inj hS hT, by intro h; congr ⟩

variable (p) in
/-- If the bilinear pairing is separating, then the top submodule is dual closed. -/
lemma DualClosed.top : DualClosed p ⊤ := by
  rw [DualClosed, le_antisymm_iff, and_comm]
  exact ⟨subset_dual_dual, by simp only [top_coe, le_top]⟩

variable (p) in
@[simp] lemma dual_dual_top : dual p.flip (dual p ⊤) = ⊤ := DualClosed.top p

variable [Fact p.SeparatingLeft] in
/-- If the bilinear pairing is separating, then the bottom submodule is dual closed. -/
@[simp] lemma DualClosed.bot : DualClosed p ⊥ := by simp [DualClosed]

variable (p) [Fact p.SeparatingLeft] in
@[simp] lemma dual_dual_bot : dual p.flip (dual p 0) = ⊥ := by simp

@[simp] lemma DualClosed.ker : DualClosed p (ker p) := by
  simpa [← dual_flip_univ_ker] using of_dual_flip p _

lemma DualClosed.ker_le {S : Submodule R M} (hS : S.DualClosed p) : LinearMap.ker p ≤ S := by
  rw [← hS]; exact ker_le_dual_flip _

/-- The intersection of two dual closed submodules is dual closed. -/
lemma DualClosed.inf {S T : Submodule R M}
    (hS : S.DualClosed p) (hT : T.DualClosed p) : (S ⊓ T).DualClosed p := by
  rw [← hS, ← hT, DualClosed, ← dual_sup_dual_eq_inf_dual, dual_flip_dual_dual_flip]

/-- The intersection of a family of dual closed submodules is dual closed. -/
protected lemma DualClosed.sInf {s : Set (Submodule R M)} (hS : ∀ S ∈ s, S.DualClosed p) :
    (sInf s).DualClosed p := by
  have hs : s = dual p.flip '' (SetLike.coe '' (dual p '' (SetLike.coe '' s))) := by
    ext T; simp only [mem_image, exists_exists_and_eq_and]
    constructor
    · exact fun hT => ⟨T, hT, hS T hT⟩
    · intro h
      obtain ⟨t, hts, ht⟩ := h
      simpa [← ht, hS t hts] using hts
  rw [hs, ← dual_sSup_sInf_dual]
  exact of_dual _ _

-------

variable (p) in
lemma dual_id_dual_eval_le_dual_dual (s : Set M) :
    dual .id (dual (Dual.eval R M) s) ≤ dual p.flip (dual p s)
  := fun _ hx y hy => @hx (p.flip y) hy

lemma DualClosed.to_eval {S : Submodule R M} (hS : S.DualClosed p)
    : S.DualClosed (Dual.eval R M) := by
  have h := dual_id_dual_eval_le_dual_dual p S
  rw [hS] at h
  exact le_antisymm h subset_dual_dual

end CommSemiring

section CommRing

/- TODO: figure out what are the weakest conditions under which these results are true.
  is `IsPerfPair` really necessary? -/

variable {R M N : Type*}
  [CommRing R]
  [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]
  (p : M →ₗ[R] N →ₗ[R] R)

variable [Fact (Surjective p.flip)] in
lemma dual_dual_eq_dual_id_dual_eval (s : Set M) :
    dual p.flip (dual p s) = dual .id (dual (Dual.eval R M) s) := by
  rw [le_antisymm_iff, and_comm]
  constructor
  · exact dual_id_dual_eval_le_dual_dual p s
  simp only [SetLike.le_def, mem_dual, SetLike.mem_coe, flip_apply, Dual.eval_apply, id_coe, id_eq]
  intro x hx y hy
  obtain ⟨x', hx'⟩ := (Fact.elim inferInstance : Surjective p.flip) y
  simp only [← hx', flip_apply] at hy
  specialize @hx x' hy
  rw [← flip_apply, hx'] at hx
  exact hx

variable [Fact (Surjective p.flip)] in
lemma DualClosed.iff_dualClosed_eval {S : Submodule R M} :
    S.DualClosed p ↔ S.DualClosed (Dual.eval R M) := by
  simp [DualClosed, Dual.eval, dual_dual_eq_dual_id_dual_eval]

end CommRing

section Field

variable {R M N : Type*}
  [Field R]
  [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]
  (p : M →ₗ[R] N →ₗ[R] R)

-- TODO: do we need a `[Field R]`, or is `Surjective p` enough?
variable [Fact (Surjective p.flip)] in
/-- A submodule of a vector space is dual closed. -/
lemma DualClosed.of_surjective (S : Submodule R M) : S.DualClosed p := by
  rw [DualClosed.iff_dualClosed_eval]
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
    DualClosed.of_surjective p.flip S

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

end Field

end Submodule
