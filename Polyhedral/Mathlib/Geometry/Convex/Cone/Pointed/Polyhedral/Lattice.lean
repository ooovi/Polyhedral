/-
Copyright (c) 2025 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/

import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Polyhedral.Basic

/-! This file defines `PolyhedralCone` as a bundled object. -/

open Function Module OrderDual LinearMap Pointwise
open Submodule hiding dual DualClosed
open PointedCone

variable {R M M₁ M₂ N : Type*}

variable (R) [Ring R] [PartialOrder R] [IsOrderedRing R] in
variable (M) [AddCommMonoid M] [Module R M] in
/-- A cone is polyhedral if it is the sum of a finitly generated cone and a submodule. -/
structure PolyhedralCone extends toPointedCone : PointedCone R M where
  isPolyhedral : IsPolyhedral toPointedCone

attribute [coe] PolyhedralCone.toPointedCone

namespace PolyhedralCone

section Ring_PartialOrder

variable [Ring R] [PartialOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M]

variable {C C₁ C₂ : PolyhedralCone R M}

instance : Coe (PolyhedralCone R M) (PointedCone R M) := ⟨toPointedCone⟩

lemma toPointedCone_injective :
    Injective (toPointedCone : PolyhedralCone R M → PointedCone R M) :=
  fun C D h => by cases C; cases D; cases h; rfl

instance : SetLike (PolyhedralCone R M) M where
  coe C := C.toPointedCone
  coe_injective := SetLike.coe_injective.comp toPointedCone_injective

variable (C) in
@[simp] lemma carrier_eq_coe : C.toPointedCone = C := rfl

@[ext] theorem ext (h : ∀ x, x ∈ C₁ ↔ x ∈ C₂) : C₁ = C₂ := SetLike.ext h

@[simp] theorem mem_mk {s h x} : x ∈ (⟨s, h⟩ : PolyhedralCone R M) ↔ x ∈ s := .rfl

@[simp] theorem mk_eq {s h} : (⟨s, h⟩ : PolyhedralCone R M) = s := by ext; simp

instance : PartialOrder (PolyhedralCone R M) := .ofSetLike (PolyhedralCone R M) M

@[simp] lemma coe_toPointedCone (C : PolyhedralCone R M) :
    (C.toPointedCone : Set M) = C := rfl

-- # FG

/-- A finitely generated cone is polyhedral. -/
def of_FG (hC : C.FG) : PolyhedralCone R M
    := ⟨C, FG.isPolyhedral hC⟩

variable (R) in
/-- The hull of finitely many elements as a polyhedral cone. -/
def hull (s : Finset M) : PolyhedralCone R M := ⟨_, .of_hull_finset R s⟩

@[simp] lemma coe_hull (s : Finset M) : hull R s = PointedCone.hull R (s : Set M) := rfl

def hull_sup_submodule (s : Finset M) (S : Submodule R M) : PolyhedralCone R M :=
  ⟨hull R s ⊔ S, IsPolyhedral.sup (.of_hull_finset R s) (by simp)⟩


end Ring_PartialOrder

section Ring_LinearOrder

-- TODO: generalize to `PartialOrder` where possible.

variable [Ring R] [LinearOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M]

variable {C : PolyhedralCone R M}

variable [IsNoetherian R M] in
/-- A polyhedral cone is finitely generated. -/
protected lemma fg : C.FG := C.isPolyhedral.fg

-- # ORDER

instance : OrderBot (PolyhedralCone R M) where
  bot := ⟨_, .of_submodule ⊥⟩
  bot_le C x := by
    change _ → x ∈ (C : PointedCone R M)
    simp +contextual

instance : OrderTop (PolyhedralCone R M) where
  top := ⟨_, .of_submodule ⊤⟩
  le_top C x := by simp

instance : Max (PolyhedralCone R M) where
  max C D := ⟨_, C.isPolyhedral.sup D.isPolyhedral⟩

-- # SUBMODULE

instance : Coe (Submodule R M) (PolyhedralCone R M) where
  coe S := ⟨_, .of_submodule S⟩

-- instance : Coe (HalfspaceOrTop R M) (PolyhedralCone R M) := sorry

-- instance : Coe (Halfspace R M) (PolyhedralCone R M) := sorry

-- instance : Coe (HyperplaneOrTop R M) (PolyhedralCone R M) := sorry

-- instance : Coe (Hyperplane R M) (PolyhedralCone R M) := sorry

-- # MAP

variable [AddCommMonoid M₁] [Module R M₁]
variable [AddCommMonoid M₂] [Module R M₂]

def map (f : M₁ →ₗ[R] M₂) (C : PolyhedralCone R M₁) : PolyhedralCone R M₂ :=
  ⟨_, C.isPolyhedral.map f⟩

-- # QUOT

def quot (S : Submodule R M) : PolyhedralCone R (M ⧸ S) := ⟨_, C.isPolyhedral.quot S⟩

-- # NEG

instance : InvolutiveNeg (PolyhedralCone R M) where
  neg C := ⟨_, C.isPolyhedral.neg⟩
  neg_neg := by simp

@[simp] lemma neg_coe (C : PolyhedralCone R M) :
    (-C : PolyhedralCone R M) = -(C : PointedCone R M) := rfl

end Ring_LinearOrder

section Field

variable {R : Type*} [Field R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

instance : Min (PolyhedralCone R M) where
  min C D := ⟨_, C.isPolyhedral.inf D.isPolyhedral⟩

variable [AddCommGroup M₁] [Module R M₁]
variable [AddCommGroup M₂] [Module R M₂]

def comap (f : M₁ →ₗ[R] M₂) (C : PolyhedralCone R M₂) : PolyhedralCone R M₁ :=
  ⟨_, C.isPolyhedral.comap f⟩

end Field

-- # DUAL

section CommRing

variable [Field R] [LinearOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]

variable {p : M →ₗ[R] N →ₗ[R] R}
variable {C : PolyhedralCone R M}

variable (p) in
/-- The dual cone of a polyhedral cone. -/
def dual (P : PolyhedralCone R M) : PolyhedralCone R N := ⟨_, P.isPolyhedral.dual p⟩

variable (p) in
@[simp] lemma coe_dual (P : PolyhedralCone R M) : P.dual p = PointedCone.dual p P := rfl

variable (p) [Fact (Surjective p.flip)] in
lemma dualClosed (C : PolyhedralCone R M) : DualClosed p C :=
  C.isPolyhedral.dualClosed p

variable (p) in
lemma dualClosed_iff (C : PolyhedralCone R M) :
  DualClosed p C ↔ (lineal C).DualClosed p := C.isPolyhedral.dualClosed_iff_lineal p

end CommRing

end PolyhedralCone
