/-
Copyright (c) 2025 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/
module

public import Polyhedral.Mathlib.LinearAlgebra.BilinearMap
public import Polyhedral.Mathlib.Algebra.Module.Submodule.Dual.DualClosed
public import Polyhedral.Mathlib.Algebra.Module.Submodule.FG
public import Polyhedral.Mathlib.RingTheory.Finiteness.Cofinite

/-! This file introduces the notion `DualFG` for submodules. A submodule is `DualFG` if it
is the dual of a finitely generated submodule. Over fields this is the same as being both
`CoFG` and closed under double duality. -/

@[expose] public section

open Module Function LinearMap

namespace Submodule

section CommSemiring

variable {R M N : Type*}
variable [CommRing R]
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]

variable {p : M →ₗ[R] N →ₗ[R] R}

variable (p) in
/-- A cone is `DualFG` if it is the dual of a finite set.
  This is in analogy to `FG` (finitely generated) which is the span of a finite set. -/
def DualFG (S : Submodule R N) : Prop := ∃ s : Finset M, dual p s = S

/-- A DualFG cone is the dual of a finite set. -/
lemma DualFG.exists_finset_dual {S : Submodule R N} (hS : S.DualFG p) :
    ∃ s : Finset M, dual p s = S := by
  obtain ⟨s, hs⟩ := hS; use s

/-- A DualFG cone is the dual of a finite set. -/
lemma DualFG.exists_finite_dual {S : Submodule R N} (hS : S.DualFG p) :
    ∃ s : Set M, s.Finite ∧ dual p s = S := by
  obtain ⟨s, hs⟩ := hS
  exact ⟨s, s.finite_toSet, hs⟩

/-- A DualFG cone is the dual of an FG cone. -/
lemma DualFG.exists_fg_dual {S : Submodule R N} (hS : S.DualFG p) :
    ∃ T : Submodule R M, T.FG ∧ dual p T = S := by
  obtain ⟨s, hs⟩ := hS
  exact ⟨_, Submodule.fg_span s.finite_toSet, by simp [hs]⟩

/-- A DualFG cone is DualFG w.r.t. the standard pairing. -/
lemma DualFG.to_id {S : Submodule R N} (hS : S.DualFG p) : S.DualFG .id
    := by classical
  obtain ⟨s, hs⟩ := hS
  use Finset.image p s
  simp [← dual_id, hs]

variable (p) in
/-- The dual of a `Finset` is co-FG. -/
lemma dualfg_of_finset (s : Finset M) : (dual p s).DualFG p := by use s

variable (p) in
/-- The dual of a finite set is co-FG. -/
lemma dualfg_of_finite {s : Set M} (hs : s.Finite) : (dual p s).DualFG p := by
  use hs.toFinset; simp

variable (p) in
/-- The dual of an FG-cone is co-FG. -/
lemma dual_of_fg {S : Submodule R M} (hS : S.FG) : (dual p S).DualFG p := by
  obtain ⟨s, rfl⟩ := hS
  use s; rw [← dual_span]

alias FG.dual_dualfg := dual_of_fg

/-- The intersection of two DualFG cones i DualFG. -/
lemma inf_dualfg {S T : Submodule R N} (hS : S.DualFG p) (hT : T.DualFG p) :
    (S ⊓ T).DualFG p := by classical
  obtain ⟨s, rfl⟩ := hS
  obtain ⟨t, rfl⟩ := hT
  use s ∪ t; rw [Finset.coe_union, dual_union]

/-- The double dual of a DualFG cone is the cone itself. -/
@[simp]
lemma DualFG.dual_dual_flip {S : Submodule R N} (hS : S.DualFG p) :
    dual p (dual p.flip S) = S := by
  obtain ⟨T, hdualfg, rfl⟩ := exists_fg_dual hS
  exact dual_dual_flip_dual (p := p) T

/-- The double dual of a DualFG cone is the cone itself. -/
@[simp]
lemma DualFG.dual_flip_dual {S : Submodule R M} (hS : S.DualFG p.flip) :
    dual p.flip (dual p S) = S := hS.dual_dual_flip

lemma DualFG.dualClosed {S : Submodule R M} (hS : S.DualFG p.flip) :
    S.DualClosed p := hS.dual_flip_dual

lemma DualFG.dualClosed_flip {S : Submodule R N} (hS : S.DualFG p) :
    S.DualClosed p.flip := hS.dual_dual_flip

@[simp] lemma DualFG.ker_le {S : Submodule R N} (hS : S.DualFG p) : ker p.flip ≤ S := by
  rw [← dual_dual_flip hS]
  exact ker_le_dual _

lemma DualFG.sup_ker {S : Submodule R N} (hS : S.DualFG p) : (S ⊔ ker p.flip).DualFG p := by
  obtain ⟨s, rfl⟩ := hS
  use s
  simp [ker_le_dual]

/-- The top submodule is DualFG. -/
lemma dualfg_top : (⊤ : Submodule R N).DualFG p := ⟨⊥, by simp⟩

-- This statement is AI generated and might need review
/-- The bottom submodule is DualFG in a finite module over a Noetherian ring when the pairing
separates points on the right. -/
lemma dualfg_bot [IsNoetherianRing R] [Module.Finite R N] [Fact p.SeparatingRight] :
    (⊥ : Submodule R N).DualFG p := by classical
  let g : range p → M := (·.2.choose)
  have hg (f : range p) : p (g f) = f := f.2.choose_spec
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule R (range p)).FG)
  refine ⟨s.image g, eq_bot_iff.mpr fun x hx ↦ ?_⟩
  apply (Fact.elim (inferInstance : Fact p.SeparatingRight)) x
  intro y
  rw [mem_dual] at hx
  have hx' : x ∈ dual (range p).subtype (span R (s : Set (range p))) := by
    rw [dual_span, mem_dual]
    intro f hf
    simpa [hg] using hx (Finset.mem_image.mpr ⟨f, hf, rfl⟩)
  rw [mem_dual] at hx'
  simpa using (hx' (x := ⟨p y, mem_range.mpr ⟨y, rfl⟩⟩) (hs ▸ mem_top)).symm

end CommSemiring

-- ## COFG

section IsNoetherianRing

variable {R : Type*} [CommRing R] [IsNoetherianRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}

theorem DualFG.cofg {S : Submodule R N} (hS : S.DualFG p) : S.CoFG := by
  obtain ⟨s, rfl⟩ := hS.exists_finset_dual
  exact dual_finset_cofg p s

variable (p) in
theorem FG.dual_cofg {S : Submodule R M} (hS : S.FG) : (dual p S).CoFG :=
  (hS.dual_dualfg p).cofg

theorem fg_of_isCompl_dualfg {S T : Submodule R N} (hST : IsCompl S T) (hS : S.DualFG p) :
    T.FG := CoFG.fg_of_isCompl hST (DualFG.cofg hS)

end IsNoetherianRing

section IsNoetherianRing

variable {R : Type*} [CommRing R] [IsNoetherianRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}

variable (p) [Fact p.SeparatingRight] in
/-- For an FG submodule `S`, there exists a DualFG submodule disjoint from `S`. -/
lemma FG.exists_dualfg_disjoint {S : Submodule R N} (hS : S.FG) :
    ∃ T : Submodule R N, T.DualFG p ∧ Disjoint S T := by
  obtain ⟨V, hfg, hV⟩ := (hS.dual_cofg p.flip).exists_fg_codisjoint
  exact ⟨dual p V, hfg.dual_dualfg _, disjoint_dual_of_codisjoint_dual _ hV⟩

theorem fg_of_disjoint_dualfg {S T : Submodule R N} (hST : Disjoint S T)
    (hS : S.DualFG p) : T.FG :=
  CoFG.disjoint_fg hST (DualFG.cofg hS)

end IsNoetherianRing

section Field

variable {R : Type*} [Field R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}

variable (p) [Fact (Surjective p)] [Fact p.SeparatingLeft] in
theorem dualfg_of_codisjoint_fg {S T : Submodule R N} (hST : Codisjoint S T) (hS : S.FG) :
    T.DualFG p := by
  have hST := disjoint_dual_of_codisjoint p.flip hST
  have hS := FG.dual_dualfg p.flip hS
  simpa [Submodule.dual_dual_flip] using dual_of_fg p (fg_of_disjoint_dualfg hST hS)

-- The proof can maybe be much shorter, see `dualfg_of_codisjoint_fg`
variable (p) [Fact (Surjective p)] in
/-- A complement of an FG submodule is DualFG. -/
theorem dualfg_of_isCompl_fg {S T : Submodule R N} (hST : IsCompl S T) (hS : S.FG) :
    T.DualFG p := by classical
  obtain ⟨s, ⟨b⟩⟩ := Basis.exists_basis R S
  have := Module.Finite.iff_fg.mpr hS
  have := Module.Finite.finite_basis b
  let proj := projectionOnto S T hST
  let f : N →ₗ[R] (s → R) := .pi fun i ↦ Basis.dualBasis b i ∘ₗ proj
  obtain ⟨t, ht⟩ := exists_finset_dual_ker p f
  refine ⟨t, ht.trans ?_⟩
  rw [← ker_projectionOnto hST]
  ext x
  simp only [mem_ker]
  constructor <;> intro hx
  · rw [← b.forall_coord_eq_zero_iff]
    exact fun i => by simpa [f, proj] using congrFun hx i
  · funext i
    rw [← b.forall_coord_eq_zero_iff] at hx
    simpa [f, proj] using hx i

variable (p) [Fact (Surjective p)] in
lemma FG.exists_dualfg_isCompl {S : Submodule R N} (hS : S.FG) :
    ∃ T : Submodule R N, T.DualFG p ∧ IsCompl S T := by
  obtain ⟨T, hST⟩ := exists_isCompl S
  exact ⟨T, dualfg_of_isCompl_fg p hST hS, hST⟩

variable (p) [Fact (Surjective p)] in
theorem CoFG.exists_finset_dual {S : Submodule R N} (hS : S.CoFG) :
    ∃ s : Finset M, dual p s = S := by
  obtain ⟨T, hST⟩ := exists_isCompl S
  have h := disjoint_fg hST.disjoint hS
  exact dualfg_of_isCompl_fg p hST.symm h

variable (p) [Fact (Surjective p)] in
theorem CoFG.dualfg {S : Submodule R N} (hS : S.CoFG) : S.DualFG p := by
  obtain ⟨s, hs⟩ := exists_finset_dual p hS; use s

end Field

end Submodule
