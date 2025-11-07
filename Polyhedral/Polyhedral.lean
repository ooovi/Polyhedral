/-
Copyright (c) 2025 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Order.Partition.Basic

import Polyhedral.Mathlib.Algebra.Module.Submodule.CoFG'
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Field
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Face.Basic
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Face.Lattice
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Field
import Polyhedral.Halfspace
import Polyhedral.Faces2

open Function Module OrderDual LinearMap
open Submodule hiding span dual IsDualClosed
open PointedCone



/- WISHLIST:
 * fg cones are polyhedral
 * in finite dim, fg = polyhedral
 * faces are polyhedral
 * quotients are polyhedral
 * submodules are polyhedral
 * halfspaces are polyhedral
 * lattice of polyhedral cones
 * coFG cones are polyhedral
 * dual of polyhedral cone is polyhedral
 * finitely many faces / finite face lattice
 * dual closed
-/



namespace PointedCone

variable {R : Type*} [Ring R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {C C₁ C₂ F : PointedCone R M}

/-- A cone is polyhedral if its salient quotient is finitely generated. -/
abbrev IsPolyhedral (C : PointedCone R M) := FG C.salientQuot

lemma isPolyhedral_def : C.IsPolyhedral ↔ FG C.salientQuot := by rfl

lemma Submodule.isPolyhedral (S : Submodule R M) : (S : PointedCone R M).IsPolyhedral := by
  simp [IsPolyhedral, salientQuot_of_submodule, fg_bot]

lemma FG.isPolyhedral (hC : C.FG) : C.IsPolyhedral := salientQuot_fg hC

lemma IsPolyhedral.salientQuot (hC : C.IsPolyhedral) : C.salientQuot.IsPolyhedral :=
    FG.isPolyhedral hC

lemma IsPolyhedral.fg_inf_of_isCompl (hC : C.IsPolyhedral)
    {S : Submodule R M} (hS : IsCompl C.lineal S) : FG (C ⊓ S) :=
  hC.linearEquiv <| IsCompl.map_mkQ_equiv_inf hS C.lineal_le

/- If the quotient by any contained submodule is FG, then the cone is polyhedral. -/
lemma isPolyhedral_of_quot_fg {S : Submodule R M} (hS : S ≤ C) (hC : FG (C.quot S)) :
    C.IsPolyhedral := by
  simp only [IsPolyhedral, salientQuot, quot, map,
    ← factor_comp_mk <| submodule_le_lineal hS, restrictScalars_comp, map_comp]
  exact FG.map _ hC

lemma IsPolyhedral.exists_finset_span_quot_lineal (hC : C.IsPolyhedral) :
    ∃ s : Finset M, (span R s).quot C.lineal = C.salientQuot := by classical
  obtain ⟨s, hs⟩ := hC
  use Finset.image (surjInv <| mkQ_surjective _) s
  simp only [map_span, Finset.coe_image, Set.image_image, surjInv_eq, Set.image_id', hs]

lemma IsPolyhedral.exists_finset_inter_span_quot_lineal (hC : C.IsPolyhedral) :
    ∃ s : Finset M, (s : Set M) ∩ C.lineal = ∅ ∧ (span R s).quot C.lineal = C.salientQuot := by
  classical
  obtain ⟨s, hs⟩ := exists_finset_span_quot_lineal hC
  use {x ∈ s | x ∉ C.lineal}
  constructor
  · ext; simp
  · rw [← hs]
    simp
    ext x
    simp [mem_sup]
    sorry

lemma IsPolyhedral.exists_finset_sup_lineal (hC : C.IsPolyhedral) :
    ∃ s : Finset M, span R s ⊔ C.lineal = C := by classical
  obtain ⟨s, hs⟩ := exists_finset_span_quot_lineal hC
  use s
  simpa [quot_eq_iff_sup_eq] using hs

structure PolyhedralDecomposition (hC : C.IsPolyhedral) where
  core : PointedCone R M
  coreFG : core.FG
  coreSalient : core.Salient
  coreSupLineal : core ⊔ C.lineal = C

-- lemma IsPolyhedral.exists_finset_sup_lineal' (hC : C.IsPolyhedral) :
--     ∃ s : Finset M, span R (s ∪ C.lineal) = C := by classical
--   obtain ⟨s, hs⟩ := hC
--   let f := surjInv (mkQ_surjective C.lineal)
--   use Finset.image f s
--   rw [span_union]
--   simp
--   sorry

lemma IsPolyhedral.exists_fg_sup_lineal (hC : C.IsPolyhedral) :
    ∃ D : PointedCone R M, D.FG ∧ D ⊔ C.lineal = C := by
  obtain ⟨s, hs⟩ := hC.exists_finset_sup_lineal
  use span R s
  exact ⟨fg_span s.finite_toSet, hs⟩

lemma IsPolyhedral.fg_of_fg_lineal (hC : C.IsPolyhedral) (hlin : FG C.lineal) : C.FG := by
  obtain ⟨D, hD, hD'⟩ := hC.exists_fg_sup_lineal
  rw [← hD']
  exact sup_fg hD hlin

lemma IsPolyhedral.fg_iff_fg_lineal {hC : C.IsPolyhedral} : C.FG ↔ C.lineal.FG :=
  ⟨FG.lineal_fg, hC.fg_of_fg_lineal⟩

lemma IsPolyhedral.fg_of_salient (hC : C.IsPolyhedral) (hsal : C.Salient) : C.FG :=
  hC.fg_of_fg_lineal (by simpa [salient_iff_lineal_bot.mp hsal] using fg_bot)

lemma isPolyhedral_iff_FG_of_salient (hC : C.Salient) : C.IsPolyhedral ↔ C.FG :=
  ⟨(IsPolyhedral.fg_of_salient · hC), FG.isPolyhedral⟩

section DivisionRing

variable {R : Type*} [DivisionRing R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {C C₁ C₂ F : PointedCone R M}

lemma IsPolyhedral.exists_fg_salient_sup_lineal (hC : C.IsPolyhedral) :
    ∃ D : PointedCone R M, D.FG ∧ D.Salient ∧ D ⊔ C.lineal = C := by
  obtain ⟨s, hs', hs⟩ := hC.exists_finset_inter_span_quot_lineal
  use span R s
  constructor
  · exact fg_span (Finset.finite_toSet _)
  constructor
  · rw [salient_iff_lineal_bot]
    rw [← ofSubmodule_inj]
    rw [← span_inter_lineal_eq_lineal]
    simp at hs
    rw [← hs] at hs'
    have hh := lineal_sup_le (M := M) (span R s) C.lineal
    simp only [lineal_submodule, -sup_le_iff] at hh
    have hh := Set.inter_subset_inter_right s hh
    rw [hs'] at hh
    simp at hh
    -- rw [Set.sup_eq_union] at hh
    -- rw [lineal_sup]
    -- simp at hs'
    sorry -- use hs'
  · simpa [span_union, span_coe_eq_restrictScalars] using hs

end DivisionRing

lemma isPolyhedral_of_fg_sup_submodule (hC : C.FG) (S : Submodule R M) :
    (C ⊔ S).IsPolyhedral := by
  refine isPolyhedral_of_quot_fg le_sup_right ?_
  simpa [sup_quot_eq_quot] using quot_fg hC S

lemma IsPolyhedral.sup (h₁ : C₁.IsPolyhedral) (h₂ : C₂.IsPolyhedral) :
    (C₁ ⊔ C₂).IsPolyhedral := by
  obtain ⟨D₁, hD₁, hD₁'⟩ := h₁.exists_fg_sup_lineal
  obtain ⟨D₂, hD₂, hD₂'⟩ := h₂.exists_fg_sup_lineal
  rw [← hD₁', ← hD₂', sup_assoc]
  nth_rw 2 [sup_comm]
  rw [sup_assoc, ← sup_assoc, ← coe_sup]
  exact isPolyhedral_of_fg_sup_submodule (sup_fg hD₁ hD₂) _

section DivisionRing

variable {R : Type*} [DivisionRing R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {C C₁ C₂ F : PointedCone R M}

-- lemma IsPolyhedral.exists_fg_salient_sup_lineal' (hC : C.IsPolyhedral) :
--     ∃ D : PointedCone R M, D.FG ∧ D.Salient ∧ D ⊔ C.lineal = C := by
--   obtain ⟨S, hS⟩ := C.lineal.exists_isCompl
--   exact ⟨C ⊓ S, hC.fg_inf_of_isCompl hS,
--     inf_salient hS.disjoint, inf_sup_lineal hS.codisjoint⟩

end DivisionRing

lemma IsPolyhedral.fg_of_inf_fg (hC : C.IsPolyhedral)
    {S : Submodule R M} (hS : FG S) : FG (C ⊓ S) := by

  sorry

lemma IsPolyhedral.inf (h₁ : C₁.IsPolyhedral) (h₂ : C₂.IsPolyhedral) :
    (C₁ ⊓ C₂).IsPolyhedral := sorry

lemma IsPolyhedral.map (hC : C.IsPolyhedral) (f : M →ₗ[R] N) : (C.map f).IsPolyhedral := by
  unfold IsPolyhedral PointedCone.salientQuot PointedCone.quot PointedCone.map
  -- simp
  sorry

lemma IsPolyhedral.comap (hC : C.IsPolyhedral) (f : N →ₗ[R] M) : (C.comap f).IsPolyhedral := sorry

lemma IsPolyhedral.neg (hC : C.IsPolyhedral) : (-C).IsPolyhedral := by
  have H : -C = PointedCone.map (-.id) C := sorry
  simpa [H] using hC.map _

lemma IsPolyhedral.face (hC : C.IsPolyhedral) (hF : F.IsFaceOf C) : F.IsPolyhedral := sorry


lemma IsPolyhedral.quot (hC : C.IsPolyhedral) (S : Submodule R M) : (C.quot S).IsPolyhedral :=
    sorry

section CommRing

variable {R : Type*} [CommRing R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}
variable {C C₁ C₂ F : PointedCone R M}

section Field

variable {R : Type*} [Field R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}
variable {C C₁ C₂ F : PointedCone R M}

variable (p) in
lemma isPolyhedral_dual_of_finset (s : Finset M) : (dual p s).IsPolyhedral := by
  obtain ⟨D, hfg, hD⟩ := exists_fg_sup_dual p s
  rw [← hD]
  exact isPolyhedral_of_fg_sup_submodule hfg _

variable (p) in
lemma isPolyhedral_dual_of_fg (hC : C.FG) : (dual p C).IsPolyhedral := by
  obtain ⟨D, hfg, hD⟩ := FG.exists_fg_sup_dual p hC
  rw [← hD]
  exact isPolyhedral_of_fg_sup_submodule hfg _

variable (p) in
lemma IsPolyhedral.dual (hC : C.IsPolyhedral) : (dual p C).IsPolyhedral := by
  obtain ⟨D, hfg, hD⟩ := hC.exists_fg_sup_lineal
  rw [← hD]
  rw [dual_sup_dual_inf_dual]
  obtain ⟨E, hfg, hE⟩ := (isPolyhedral_dual_of_fg p hfg).exists_fg_sup_lineal
  rw [← hE]
  simp only [Submodule.coe_restrictScalars, dual_eq_submodule_dual]
  rw [← sup_inf_assoc_of_le_submodule]
  · rw [← PointedCone.coe_inf]
    exact isPolyhedral_of_fg_sup_submodule hfg _
  · rw [dual_span_lineal_dual] at hE
    -- rw [right_eq_sup] at hE
    ----
    rw [← hD]
    --rw [dual_sup_dual_eq_inf_dual]
    rw [IsDualClosed.dual_lineal_span_dual]
    ·
      sorry
    · sorry
    -- exact left_eq_sup.mp hE.symm

end Field

end CommRing

section Module.Finite

variable [Module.Finite R M]

lemma IsPolyhedral.FG (hC : C.IsPolyhedral) : C.FG := sorry

lemma isPolyhedral_iff_FG : C.IsPolyhedral ↔ C.FG := ⟨IsPolyhedral.FG, FG.isPolyhedral⟩

end Module.Finite


end PointedCone





variable {R : Type*} [Ring R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [AddCommGroup N] [Module R N]

variable (R M) in
/-- A cone is polyhedral if its salient quotient is finitely generated. -/
structure PolyhedralCone extends PointedCone R M where
  isPolyhedral : IsPolyhedral toSubmodule

namespace PolyhedralCone

-- ## BOILERPLATE

@[coe] abbrev toPointedCone (C : PolyhedralCone R M) : PointedCone R M := C.toSubmodule

instance : Coe (PolyhedralCone R M) (PointedCone R M) := ⟨toPointedCone⟩

lemma toPointedCone_injective :
    Injective (toPointedCone : PolyhedralCone R M → PointedCone R M) :=
  sorry -- fun ⟨_, _⟩ _ ↦ by congr!

instance : SetLike (PolyhedralCone R M) M where
  coe C := C.toPointedCone
  coe_injective' := SetLike.coe_injective.comp toPointedCone_injective

@[simp] lemma coe_toPointedCone (C : PolyhedralCone R M) :
    (C.toPointedCone : Set M) = C := rfl


-- ## FG

variable {C C₁ C₂ : PolyhedralCone R M}

/-- A finitely generated cone is polyhedral. -/
def of_FG {C : PointedCone R M} (hC : C.FG) : PolyhedralCone R M
    := ⟨C, FG.isPolyhedral hC⟩

def finspan (s : Finset M) : PolyhedralCone R M := of_FG (Submodule.fg_span <| s.finite_toSet)

variable [Module.Finite R M]
/-- A polyhedral cone in a finite dimensional vector space is finitely generated. -/
def FG {C : PolyhedralCone R M} : C.FG := C.isPolyhedral.FG


-- ## COFG

-- /-- A co-finitely generated cone is polyhedral. -/
-- def of_CoFG {C : PointedCone R M} (hC : C.CoFG) : PolyhedralCone R M := sorry


-- ## TOP / BOT

def bot : PolyhedralCone R M := ⟨_, Submodule.isPolyhedral ⊥⟩
def top : PolyhedralCone R M := ⟨_, Submodule.isPolyhedral ⊤⟩

-- alias lineal := bot

instance : OrderBot (PolyhedralCone R M) where
  bot := bot
  bot_le := sorry

instance : OrderTop (PolyhedralCone R M) where
  top := top
  le_top := sorry

instance : Min (PolyhedralCone R M) where
  min C D := ⟨_, C.isPolyhedral.inf D.isPolyhedral⟩

instance : Max (PolyhedralCone R M) where
  max C D := ⟨_, C.isPolyhedral.sup D.isPolyhedral⟩


-- ## FACE

instance : CoeOut (Face (C : PointedCone R M)) (PolyhedralCone R M) where
  coe F := ⟨F, C.isPolyhedral.face F.isFaceOf⟩

instance {C : PolyhedralCone R M} : Finite (Face (C : PointedCone R M)) := sorry

def atomFaces : Set (Face (C : PointedCone R M)) := sorry

alias rays := atomFaces

def coatomFaces : Set (Face (C : PointedCone R M)) := sorry

alias facets := coatomFaces

/- TODO:
 * face lattice is graded
 * all faces exposed
-/

-- lemma face_exposed (F : Face C) : F.IsExposed := sorry


-- ## DUAL

section CommRing

variable {R : Type*} [CommRing R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}
variable {C C₁ C₂ F : PolyhedralCone R M}

-- variable (p) in
-- def dual (C : PolyhedralCone R M) : PolyhedralCone R N := ⟨_, C.isPolyhedral.dual p⟩

variable (p) [Fact p.flip.IsFaithfulPair] in
lemma isDualClosed (C : PolyhedralCone R M) : IsDualClosed p C := sorry

variable (p) in
lemma isDualClosed_iff (C : PolyhedralCone R M) :
  IsDualClosed p C ↔ (lineal C).IsDualClosed p := sorry

-- Duality flips the face lattice

end CommRing


-- ## SUBMODULE

instance : Coe (Submodule R M) (PolyhedralCone R M) where
  coe S := ⟨_, S.isPolyhedral⟩

-- instance : Coe (HalfspaceOrTop R M) (PolyhedralCone R M) := sorry

-- instance : Coe (Halfspace R M) (PolyhedralCone R M) := sorry

-- instance : Coe (HyperplaneOrTop R M) (PolyhedralCone R M) := sorry

-- instance : Coe (Hyperplane R M) (PolyhedralCone R M) := sorry


-- ## MAP

def map (f : M →ₗ[R] N) (C : PolyhedralCone R M) : PolyhedralCone R N :=
  ⟨_, C.isPolyhedral.map f⟩

def comap (f : M →ₗ[R] N) (C : PolyhedralCone R N) : PolyhedralCone R M :=
  ⟨_, C.isPolyhedral.comap f⟩


-- ## QUOT

def quot (S : Submodule R M) : PolyhedralCone R (M ⧸ S) := ⟨_, C.isPolyhedral.quot S⟩

def salientQuot : PolyhedralCone R (M ⧸ (C : PointedCone R M).lineal) :=
    ⟨_, C.isPolyhedral.salientQuot⟩


-- ## NEG

instance : InvolutiveNeg (PolyhedralCone R M) where
  neg C := ⟨_, C.isPolyhedral.neg⟩
  neg_neg := sorry

end PolyhedralCone
