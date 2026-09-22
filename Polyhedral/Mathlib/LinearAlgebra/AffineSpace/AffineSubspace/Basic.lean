/-
Copyright (c) 2026 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import Polyhedral.Mathlib.Algebra.Group.Pointwise.SetLike.Basic

/-!
This file adds features for affine spaces.
-/

public section

noncomputable section

open Affine

open Set
open scoped Pointwise

variable {R V A : Type*}

section AddTorsor

variable [Ring R]
variable [AddCommGroup V] [Module R V]
variable [AddTorsor V A]

instance : IsConcreteBot (AffineSubspace R A) A := ⟨rfl⟩

instance : EmptyCollection (AffineSubspace R A) where
  emptyCollection := {
    carrier := ∅
    smul_vsub_vadd_mem' _ _ _ _ := by simp }

instance : IsConcreteEmpty (AffineSubspace R A) A := ⟨rfl⟩

lemma AffineSubspace.affineSpan_empty : affineSpan R (∅ : Set A) = ∅ := by simp

instance : Singleton A (AffineSubspace R A) where
  singleton x := {
    carrier := {x}
    smul_vsub_vadd_mem' _ _ _ _ := by simp +contextual }

instance : IsConcreteSingleton (AffineSubspace R A) A := ⟨fun _ => rfl⟩

@[simp]
lemma AffineSubspace.affineSpan_singleton (x : A) : affineSpan R ({x} : Set A) = {x} := by
  ext; simp

instance : IsConcreteTop (AffineSubspace R A) A := ⟨rfl⟩

end AddTorsor

section Module

variable [Ring R]
variable [AddCommGroup V] [Module R V]

instance : Neg (AffineSubspace R V) where
  neg p := {
    carrier := -p
    smul_vsub_vadd_mem' := by
      intro r x y z hx hy hz
      rw [mem_neg] at *
      rw [vsub_eq_sub, vadd_eq_add, neg_add_rev, SetLike.mem_coe, ← smul_neg, neg_sub']
      simpa [add_comm] using p.smul_vsub_vadd_mem r hx hy hz }

instance : IsConcreteNeg (AffineSubspace R V) V := ⟨fun _ => rfl⟩

end Module
