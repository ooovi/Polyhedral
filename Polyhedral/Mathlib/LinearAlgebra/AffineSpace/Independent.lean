/-
Copyright (c) 2026 Vlad Tsyrklevich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vlad Tsyrklevich
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.Independent

/-! Affine independence lemmas -/

@[expose] public section

open Affine

section DivisionRing

variable (k : Type*) (V : Type*) {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
variable [AffineSpace V P]

theorem exists_affineIndepOn (s : Set P) :
    ∃ t ⊆ s, affineSpan k t = affineSpan k s ∧ AffineIndepOn k id t :=
  exists_affineIndependent k V s

end DivisionRing
