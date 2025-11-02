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

import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Field
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Face.Basic
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Face.Lattice
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

lemma IsPolyhedral.FG_of_salient (hC : C.Salient) (hC' : C.IsPolyhedral) : C.FG := by
  rw [salient_iff_lineal_bot] at hC
  rw [isPolyhedral_def] at *
  have h := quotEquivOfEqBot _ hC
  -- rw [hC] at hC'
  sorry

lemma IsPolyhedral.salientQuot (hC : C.IsPolyhedral) : C.salientQuot.IsPolyhedral :=
    FG.isPolyhedral hC

lemma IsPolyhedral.quot (hC : C.IsPolyhedral) (S : Submodule R M) : (C.quot S).IsPolyhedral :=
    sorry

lemma isPolyhedral_iff_FG_of_salient (hC : C.Salient) : C.IsPolyhedral ↔ C.FG :=
  ⟨IsPolyhedral.FG_of_salient hC, FG.isPolyhedral⟩

lemma IsPolyhedral.fg_of_inf_isCompl (hC : C.IsPolyhedral)
    {S : Submodule R M} (hS : IsCompl S C.lineal) : FG (C ⊓ S) := sorry

lemma IsPolyhedral.fg_of_inf_fg (hC : C.IsPolyhedral)
    {S : Submodule R M} (hS : FG S) : FG (C ⊓ S) := sorry

lemma IsPolyhedral.exists_fg_sup_submodule (hC : C.IsPolyhedral) :
    ∃ D : PointedCone R M, D.FG ∧ D ⊓ C.lineal = ⊥ ∧ D ⊔ C.lineal = C := by
  sorry

lemma IsPolyhedral.sup (h₁ : C₁.IsPolyhedral) (h₂ : C₂.IsPolyhedral) :
    (C₁ ⊔ C₂).IsPolyhedral := sorry

lemma IsPolyhedral.inf (h₁ : C₁.IsPolyhedral) (h₂ : C₂.IsPolyhedral) :
    (C₁ ⊓ C₂).IsPolyhedral := sorry

lemma IsPolyhedral.face (hC : C.IsPolyhedral) (hF : F.IsFaceOf C) : F.IsPolyhedral := sorry

lemma IsPolyhedral.map (hC : C.IsPolyhedral) (f : M →ₗ[R] N) : (C.map f).IsPolyhedral := sorry

lemma IsPolyhedral.comap (hC : C.IsPolyhedral) (f : N →ₗ[R] M) : (C.comap f).IsPolyhedral := sorry

lemma IsPolyhedral.neg (hC : C.IsPolyhedral) : (-C).IsPolyhedral := sorry

section CommRing

variable {R : Type*} [CommRing R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}
variable {C C₁ C₂ F : PointedCone R M}

variable (p) in
lemma IsPolyhedral.dual (hC : C.IsPolyhedral) : (dual p C).IsPolyhedral := sorry

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

variable (p) in
def dual (C : PolyhedralCone R M) : PolyhedralCone R N := ⟨_, C.isPolyhedral.dual p⟩

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
