/-
Copyright (c) 2025 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/

import Polyhedral.Mathlib.LinearAlgebra.BilinearMap
import Polyhedral.Mathlib.Algebra.Module.Submodule.Dual
import Polyhedral.Mathlib.Algebra.Module.Submodule.FG

open Module Function LinearMap

namespace Submodule

section CommSemiring

variable {R M N : Type*}
variable [CommRing R]
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R} -- bilinear pairing

variable (p) in
/-- A cone is `FGDual` if it is the dual of a finite set.
  This is in analogy to `FG` (finitely generated) which is the span of a finite set. -/
def FGDual (S : Submodule R N) : Prop := ∃ s : Finset M, dual p s = S

/-- A FGDual cone is the dual of a finite set. -/
lemma FGDual.exists_finset_dual {S : Submodule R N} (hS : S.FGDual p) :
    ∃ s : Finset M, dual p s = S := by
  obtain ⟨s, hs⟩ := hS; use s

/-- A FGDual cone is the dual of a finite set. -/
lemma FGDual.exists_finite_dual {S : Submodule R N} (hS : S.FGDual p) :
    ∃ s : Set M, s.Finite ∧ dual p s = S := by
  obtain ⟨s, hs⟩ := hS; exact ⟨s, s.finite_toSet, hs⟩

/-- A FGDual cone is the dual of an FG cone. -/
lemma FGDual.exists_fg_dual {S : Submodule R N} (hS : S.FGDual p) :
    ∃ T : Submodule R M, T.FG ∧ dual p T = S := by
  obtain ⟨s, hs⟩ := hS; exact ⟨_, Submodule.fg_span s.finite_toSet, by simp [hs]⟩

/-- A FGDual cone is FGDual w.r.t. the standard pairing. -/
lemma FGDual.to_id {S : Submodule R N} (hS : S.FGDual p) : S.FGDual .id
    := by classical
  obtain ⟨s, hs⟩ := hS
  use Finset.image p s
  simp [← dual_id, hs]

variable (p) in
/-- The dual of a `Finset` is co-FG. -/
lemma fgdual_of_finset (s : Finset M) : (dual p s).FGDual p := by use s

variable (p) in
/-- The dual of a finite set is co-FG. -/
lemma fgdual_of_finite {s : Set M} (hs : s.Finite) : (dual p s).FGDual p := by
  use hs.toFinset; simp

variable (p) in
/-- The dual of an FG-cone is co-FG. -/
lemma fgdual_of_fg {S : Submodule R M} (hS : S.FG) : (dual p S).FGDual p := by
  obtain ⟨s, rfl⟩ := hS
  use s; rw [← dual_span]

alias FG.dual_fgdual := fgdual_of_fg

/-- The intersection of two FGDual cones i FGDual. -/
lemma inf_fgdual {S T : Submodule R N} (hS : S.FGDual p) (hT : T.FGDual p) :
    (S ⊓ T).FGDual p := by classical
  obtain ⟨s, rfl⟩ := hS
  obtain ⟨t, rfl⟩ := hT
  use s ∪ t; rw [Finset.coe_union, dual_union]

-- -- ### HIGH PRIORITY! This is needed in the cone theory!
-- -- variable [Fact p.flip.IsFaithfulPair] in
-- lemma sup_fgdual {S T : Submodule R N} (hC : S.FGDual p) (hD : T.FGDual p) : (S ⊔ T).FGDual p := by
--   unfold FGDual

--   sorry

/-- The double dual of a FGDual cone is the cone itself. -/
@[simp]
lemma FGDual.dual_dual_flip {S : Submodule R N} (hS : S.FGDual p) :
    dual p (dual p.flip S) = S := by
  obtain ⟨T, hfgdual, rfl⟩ := exists_fg_dual hS
  exact dual_dual_flip_dual (p := p) T

/-- The double dual of a FGDual cone is the cone itself. -/
@[simp]
lemma FGDual.dual_flip_dual {S : Submodule R M} (hS : S.FGDual p.flip) :
    dual p.flip (dual p S) = S := hS.dual_dual_flip

lemma FGDual.dualClosed {S : Submodule R M} (hS : S.FGDual p.flip) :
    S.DualClosed p := hS.dual_flip_dual

lemma FGDual.dualClosed_flip {S : Submodule R N} (hS : S.FGDual p) :
    S.DualClosed p.flip := hS.dual_dual_flip

@[simp] lemma FGDual.ker_le {S : Submodule R N} (hS : S.FGDual p) : ker p.flip ≤ S := by
  rw [← dual_dual_flip hS]
  exact ker_le_dual _

-- lemma FGDual.sup_ker {S : Submodule R N} (hS : S.FGDual p) : (S ⊔ ker p.flip).FGDual p := by
--   obtain ⟨s, rfl⟩ := hS
--   use s
--   simp [ker_le_dual]

-----

/-- The top submodule is FGDual. -/
lemma fgdual_top : (⊤ : Submodule R N).FGDual p := ⟨⊥, by simp⟩

/-- The bottom submodule is FGDual in finite dimensional space. -/
lemma fgdual_bot [Module.Finite R N] : (⊥ : Submodule R N).FGDual p := by
  -- obtain ⟨s, hs⟩ := fg_top ⊤
  -- use
  sorry

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}

variable (p)

variable [Fact p.IsFaithfulPair] in -- Separating should suffice, no?
/-- For an FG submodule `S`, there exists an FGDual submodule `T` that is disjoint to `S`. -/
lemma FG.exists_fgdual_inf_bot {S : Submodule R N} (hS : S.FG) :
    ∃ T : Submodule R N, T.FGDual p ∧ S ⊓ T = ⊥ := by classical
  obtain ⟨g, hg⟩ : Fact p.IsFaithfulPair := inferInstance
  use dual p (Submodule.map g S)
  constructor
  · exact fgdual_of_fg p (Submodule.FG.map g hS)
  · rw [dual_bilin_dual_id_submodule, ← map_comp, ← dual_bilin_dual_id_submodule]
    ext x
    simp only [mem_inf, mem_dual, SetLike.mem_coe, mem_bot]
    constructor
    · intro hS
      exact (hg x) (hS.2 hS.1).symm
    · simp +contextual

-- lemma fgdual_of_fg_sup_fgdual {C D : Submodule R N} (hC : C.FG) (hD : D.FGDual p) :
    -- (C ⊔ D).FGDual p := by
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
    -- sorry
-- omit [Free R M] [LinearOrder R] [IsStrictOrderedRing R] in
-- lemma FGDual.fgdual_id_of_fgdual_toDual {ι : Type*} [DecidableEq ι] {S : Submodule R M}
--      {b : Basis ι R M} (hS : S.FGDual b.toDual) : S.FGDual .id := by classical
--   obtain ⟨s, rfl⟩ := hS
--   use Finset.image b.toDual s
--   ext x; simp

-- Q: Is this true? If so, also implement with `IsCompl`.
lemma exists_fgdual_sup_top {S : Submodule R N} (hS : S.FG) :
    ∃ T : Submodule R N, T.FGDual p ∧ S ⊔ T = ⊤ := by
  -- classical
  -- obtain ⟨_, b⟩ := Free.exists_basis R M
  -- use dual b.toDual S
  -- constructor
  -- · exact Submodule.fgdual_of_fg _ hS
  -- · ext x
  --   simp only [mem_sup, mem_dual, SetLike.mem_coe, mem_top, iff_true]
  sorry

lemma FG.exists_fgdual_inf_of_le {S S' : Submodule R N} (hS : S.FG) (hS' : S'.FG) (hSS' : S ≤ S') :
    ∃ T : Submodule R N, T.FGDual p ∧ S' ⊓ T = S := by sorry
  -- classical
  -- obtain ⟨s, rfl⟩ := hS
  -- induction s using Finset.induction with
  -- | empty => simp [exists_fgdual_inf_bot hS']
  -- | insert w s hws hs =>
  --   obtain ⟨t, ht⟩ := hs
  --   use (auxGenSet .id t.toSet w).toFinset
  --   simp [span_insert, sup_assoc, ← ht]
  --   exact dual_auxGenSet t.finite_toSet
  --   sorry

section IsNoetherianRing

variable {R M N : Type*}
variable [CommRing R] [IsNoetherianRing R]
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}

-- -- ## PRIORITY
-- lemma sup_fgdual_fg {S : Submodule R N} (T : Submodule R N) (hS : S.FGDual p) : (S ⊔ T).FGDual p :=

--   sorry

lemma FG.exists_fgdual_dual {S : Submodule R N} (hS : S.FG) :
    ∃ T : Submodule R M, T.FGDual p.flip ∧ dual p T = S := by
  use dual p.flip S
  -- constructor
  -- · exact sup_fg_fgdual hfg <| fgdual_of_fg p.flip (ofSubmodule_fg_of_fg hS)
  -- · simp [dual_sup_dual_inf_dual, Submodule.FG.dual_dual_flip hS]
  sorry

end IsNoetherianRing


section Field

variable {R M N : Type*}
variable [Field R] [IsNoetherianRing R]
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}

end Field

end CommRing

section Function

variable {R : Type*} [CommSemiring R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {M' : Type*} [AddCommGroup M'] [Module R M']
variable {N' : Type*} [AddCommGroup N'] [Module R N']
variable {p : M →ₗ[R] N →ₗ[R] R} {p' : M' →ₗ[R] N' →ₗ[R] R}

/- TODO: generalize to arbitrary pairings. -/

lemma map_dual (f : M →ₗ[R] M') (C : Submodule R M) :
    dual (Dual.eval R M') (map f C) = comap f.dualMap (dual (Dual.eval R M) C) := by
  ext x; simp

-- lemma map_dual' (f : (Dual R M) →ₗ[R] (Dual R E')) (C : Submodule R (Dual R M)) :
--     dual .id (map f C) = comap f.dualMap (dual .id C) := by
--   ext x; simp

end Function


-- ## COFG

section IsNoetherianRing

variable {R : Type*} [CommRing R] [IsNoetherianRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}

theorem FGDual.cofg {S : Submodule R N} (hS : S.FGDual p) : S.CoFG := by
  obtain ⟨s, rfl⟩ := hS.exists_finset_dual
  exact dual_finset_cofg p s

variable (p) in
theorem FG.dual_cofg {S : Submodule R M} (hS : S.FG) : (dual p S).CoFG := (hS.dual_fgdual p).cofg

theorem fg_of_isCompl_fgdual {S T : Submodule R N} (hST : IsCompl S T) (hS : S.FGDual p) :
    T.FG := CoFG.fg_of_isCompl hST (FGDual.cofg hS)

end IsNoetherianRing


section Field

variable {R : Type*} [Field R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}

variable (p) [Fact p.SeparatingRight] in
/-- For an FG submodule `S`, there exists an FGDual submodule `T` so that `S ⊓ T = ⊥`. -/
lemma FG.exists_fgdual_disjoint {S : Submodule R N} (hS : S.FG) :
    ∃ T : Submodule R N, T.FGDual p ∧ Disjoint S T := by
  obtain ⟨V, hfg, hV⟩ := (hS.dual_cofg p.flip).exists_fg_codisjoint
  use dual p V
  constructor
  · exact hfg.dual_fgdual _
  · exact disjoint_dual_of_codisjoint_dual p.flip hV

-- WARNING: CoFG.disjoint_fg is not yet proven
-- Does this need Field?
theorem fg_of_disjoint_fgdual {S T : Submodule R N} (hST : Disjoint S T) (hS : S.FGDual p) :
    T.FG := CoFG.disjoint_fg hST (FGDual.cofg hS)

variable (p) [p.IsPerfPair] in
theorem fgdual_of_isCompl_fg' {S T : Submodule R N} (hST : IsCompl S T) (hS : S.FG) :
    T.FGDual p := by
  have hST := IsCompl.dual p.flip hST
  have hS := FG.dual_fgdual p.flip hS
  simpa [Submodule.dual_dual_flip] using fgdual_of_fg p (fg_of_isCompl_fgdual hST hS)

variable (p) [Fact (Surjective p)] [Fact p.flip.IsFaithfulPair] in
theorem fgdual_of_isCompl_fg'' {S T : Submodule R N} (hST : Codisjoint S T) (hS : S.FG) :
    T.FGDual p := by
  have hST := disjoint_dual_of_codisjoint p.flip hST
  have hS := FG.dual_fgdual p.flip hS
  simpa [Submodule.dual_dual_flip] using fgdual_of_fg p (fg_of_disjoint_fgdual hST hS)

-- example {S T : Submodule R (Dual R M)} (hST : Codisjoint S T) (hS : S.FG) :
--   T.FGDual .id := cofg_of_isCompl_fg'' _ hST hS

example {ι : Type*} [DecidableEq ι] [Finite ι] (b : Basis ι R M) (s : Set ι) :
  IsCompl (span R ((fun i => b i )'' s)) (dual .id ((fun i => b.dualBasis i) '' sᶜ))
  := sorry

-- The proof can maybe be much shorter, see above
variable (p) [Fact (Surjective p)] in
/-- A complement of an FG submodule is FGDual. -/
theorem fgdual_of_isCompl_fg {S T : Submodule R N} (hST : IsCompl S T) (hS : S.FG) :
    T.FGDual p := by classical
  obtain ⟨s, ⟨b⟩⟩ := Basis.exists_basis R S
  haveI := Module.Finite.iff_fg.mpr hS
  haveI := Module.Finite.finite_basis b
  let proj := linearProjOfIsCompl S T hST
  have hp : Surjective p := Fact.elim inferInstance
  let f := fun i => surjInv hp (Basis.dualBasis b i ∘ₗ proj)
  use (Set.finite_range f).toFinset
  ext x
  simp only [Set.Finite.coe_toFinset, mem_dual, Set.mem_range, forall_exists_index]
  constructor
  · intro h
    replace h := fun x => Eq.symm (h x rfl)
    simp only [f, surjInv_eq hp] at h
    simp only [coe_comp, Function.comp_apply, Basis.coe_dualBasis] at h
    rw [← linearProjOfIsCompl_ker hST, mem_ker]
    exact b.forall_coord_eq_zero_iff.mp h
  · intro hxT y z rfl
    rw [surjInv_eq hp]
    rw [coe_comp, Function.comp_apply]
    rw [linearProjOfIsCompl_apply_right' _ _ hxT]
    rw [map_zero]

variable (p) [Fact (Surjective p)] in -- [Fact p.IsFaithfulPair] in
theorem CoFG.exists_finset_dual {S : Submodule R N} (hS : S.CoFG) :
    ∃ s : Finset M, dual p s = S := by
  obtain ⟨T, hST⟩ := exists_isCompl S
  have h := disjoint_fg hST.disjoint hS
  exact fgdual_of_isCompl_fg p hST.symm h

variable (p) [Fact (Surjective p)] in -- or maybe we need `Surjective p`, not sure yet
theorem CoFG.fgdual {S : Submodule R N} (hS : S.CoFG) : S.FGDual p := by
  obtain ⟨s, hs⟩ := exists_finset_dual p hS; use s

-- variable (p) [Fact (Surjective p)] in
-- /-- For an FG submodule `S`, there exists a FGDual submodule `T` so that `S ⊓ T = ⊥`. -/
-- lemma FG.exists_fgdual_inf_bot' {S : Submodule R N} (hS : S.FG) :
--     ∃ T : Submodule R N, T.FGDual p ∧ S ⊓ T = ⊥ := by
--   obtain ⟨T, hT⟩ := exists_isCompl S
--   use T
--   constructor
--   · exact fgdual_of_isCompl_fg p hT hS
--   · exact hT.disjoint.eq_bot

end Field

end Submodule
