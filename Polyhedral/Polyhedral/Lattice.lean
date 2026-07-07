/-
Copyright (c) 2025 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/

import Polyhedral.Polyhedral.Basic

/-! ... -/

open Function Module OrderDual LinearMap
open Submodule hiding dual DualClosed
open PointedCone

variable {R : Type*} [Ring R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]

variable (R M) in
/-- A cone is polyhedral if its salient quotient is finitely generated. -/
structure PolyhedralCone extends PointedCone R M where
  isPolyhedral : IsPolyhedral toSubmodule

namespace PolyhedralCone

-- ## BOILERPLATE

@[coe] abbrev toPointedCone (C : PolyhedralCone R M) : PointedCone R M := C.toSubmodule

instance : Coe (PolyhedralCone R M) (PointedCone R M) := ⟨toPointedCone⟩

--set_option linter.unusedSectionVars false in
lemma toPointedCone_injective :
    Injective (toPointedCone : PolyhedralCone R M → PointedCone R M) :=
  fun C D h => by cases C; cases D; cases h; rfl

instance : SetLike (PolyhedralCone R M) M where
  coe C := C.toPointedCone
  coe_injective' := SetLike.coe_injective.comp toPointedCone_injective

instance : PartialOrder (PolyhedralCone R M) := .ofSetLike (PolyhedralCone R M) M

@[simp] lemma coe_toPointedCone (C : PolyhedralCone R M) :
    (C.toPointedCone : Set M) = C := rfl


-- ## FG

variable {C C₁ C₂ : PolyhedralCone R M}

/-- A finitely generated cone is polyhedral. -/
def of_FG {C : PointedCone R M} (hC : C.FG) : PolyhedralCone R M
    := ⟨C, FG.isPolyhedral hC⟩

variable (R) in
/-- The hull of finitely many elements as a polyhedral cone. -/
def finhull (s : Finset M) : PolyhedralCone R M := ⟨_, .of_hull_finset R s⟩

@[simp] lemma finhull_eq_hull (s : Finset M) : finhull R s = hull (E := M) R s := rfl

def finhull_lineal (s : Finset M) (S : Submodule R M) : PolyhedralCone R M :=
  ⟨hull R s ⊔ S, IsPolyhedral.sup (.of_hull_finset R s) (by simp)⟩

variable [IsNoetherian R M] in
/-- A polyhedral cone is finitely generated. -/
def FG {C : PolyhedralCone R M} : C.FG := C.isPolyhedral.fg



-- ## ORDER

def bot : PolyhedralCone R M := ⟨_, .of_submodule ⊥⟩
def top : PolyhedralCone R M := ⟨_, .of_submodule ⊤⟩

-- alias lineal := bot

instance : OrderBot (PolyhedralCone R M) where
  bot := bot
  bot_le P := sorry

instance : OrderTop (PolyhedralCone R M) where
  top := top
  le_top := sorry

instance : Max (PolyhedralCone R M) where
  max C D := ⟨_, C.isPolyhedral.sup D.isPolyhedral⟩

section Field

variable {R : Type*} [Field R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

instance : Min (PolyhedralCone R M) where
  min C D := ⟨_, C.isPolyhedral.inf D.isPolyhedral⟩

end Field


-- ## DUAL

section CommRing

variable {R : Type*} [CommRing R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}
variable {C C₁ C₂ F : PolyhedralCone R M}

variable (p) [Fact (Surjective p.flip)] in
lemma dualClosed (C : PolyhedralCone R M) : DualClosed p C :=
  sorry -- C.isPolyhedral.dualClosed p

-- variable (p) in
-- lemma dualClosed_iff (C : PolyhedralCone R M) :
--   DualClosed p C ↔ (lineal C).DualClosed p := sorry

-- Duality flips the face lattice

section Field

variable {R : Type*} [Field R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}

variable (p) in
/-- The dual of a finite set interpreted as a polyhedral cone. -/
def findual (s : Finset M) : PolyhedralCone R N := ⟨dual p s, .of_dual_of_finset p s⟩

variable (p) in
@[simp] lemma findual_eq_dual (s : Finset M) : findual p s = dual p s := rfl

variable (p) in
/-- The dual cone of a polyhedral cone. -/
def dual (P : PolyhedralCone R M) : PolyhedralCone R N := ⟨_, P.isPolyhedral.dual p⟩

variable (p) in
@[simp] lemma coe_dual (P : PolyhedralCone R M) : P.dual p = PointedCone.dual p P := rfl

end Field

end CommRing


-- ## SUBMODULE

instance : Coe (Submodule R M) (PolyhedralCone R M) where
  coe S := ⟨_, .of_submodule S⟩

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

-- def salientQuot : PolyhedralCone R (M ⧸ (C : PointedCone R M).lineal) := sorry
--     -- ⟨_, C.isPolyhedral.salientQuot⟩


-- ## NEG

open Pointwise in
instance : InvolutiveNeg (PolyhedralCone R M) where
  neg C := ⟨_, C.isPolyhedral.neg⟩
  neg_neg := by simp

open Pointwise in
@[simp] lemma neg_coe (C : PolyhedralCone R M) :
    (-C : PolyhedralCone R M) = -(C : PointedCone R M) := rfl


end PolyhedralCone
