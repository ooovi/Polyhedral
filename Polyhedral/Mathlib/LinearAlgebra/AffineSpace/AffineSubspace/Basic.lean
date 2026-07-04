/-
Copyright (c) 2020 ... . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ...
-/

import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic

import Polyhedral.Mathlib.Algebra.Group.Pointwise.SetLike.Basic

/-!
# Affine spaces
...
-/

noncomputable section

open Affine

open Set
open scoped Pointwise

variable {R V A : Type*}

section AddTorsor

variable [Ring R]
variable [AddCommGroup V] [Module R V]
variable [AddTorsor V A]

instance : Singleton A (AffineSubspace R A) where
  singleton x := {
    carrier := {x}
    smul_vsub_vadd_mem _ _ _ _ := by simp +contextual }

instance : IsConcreteSingleton (AffineSubspace R A) A := ⟨fun _ => rfl⟩

end AddTorsor

section Module

variable [Ring R]
variable [AddCommGroup V] [Module R V]

open Pointwise in
instance : Neg (AffineSubspace R V) where
  neg p := {
    carrier := -p
    smul_vsub_vadd_mem := by
      intro r x y z hx hy hz
      rw [mem_neg] at *
      rw [vsub_eq_sub, vadd_eq_add, neg_add_rev, SetLike.mem_coe, ← smul_neg, neg_sub']
      simpa [add_comm] using p.smul_vsub_vadd_mem r hx hy hz }

instance : IsConcreteNeg (AffineSubspace R V) V := ⟨fun _ => rfl⟩

end Module
