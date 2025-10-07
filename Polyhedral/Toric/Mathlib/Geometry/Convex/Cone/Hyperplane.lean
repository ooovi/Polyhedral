/-
Copyright (c) 2025 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.LinearAlgebra.SesquilinearForm

import Polyhedral.Toric.Mathlib.Geometry.Convex.Cone.Submodule_Dual
import Polyhedral.Toric.Mathlib.Geometry.Convex.Cone.Line

/-!
# Polyhedral cones

...
-/

open Function Module

variable {R 𝕜 M N M' N' : Type*}

namespace Submodule

section Hyperplane

-- ### HyperplaneOrTop

variable {R : Type*} [CommRing R] -- [CommSemiring R]
  {M : Type*} [AddCommMonoid M] [Module R M]
  {M' : Type*} [AddCommMonoid M'] [Module R M']

def IsHyperplaneOrTop (S : Submodule R M) := ∃ x : (Dual R M), dual .id {x} = S
    -- := ∃ L : LineOrBot R M, S ⊔ L = ⊤

lemma IsHyperplaneOrTop.top : IsHyperplaneOrTop (⊤ : Submodule R M)
    := by use 0; ext x; simp

variable (R M) in
structure HyperplaneOrTop extends Submodule R M where
  isHyperplaneOrTop : IsHyperplaneOrTop toSubmodule

namespace HyperplaneOrTop

instance : Coe (HyperplaneOrTop R M) (Submodule R M) where
  coe := toSubmodule

abbrev of_isHyperplaneOrTop {S : Submodule R M} (hS : S.IsHyperplaneOrTop) : HyperplaneOrTop R M
    := ⟨S, hS⟩

lemma toSubmodule_injective :
    Injective (toSubmodule : HyperplaneOrTop R M → Submodule R M) :=
  fun ⟨_, _⟩ _ ↦ by congr!

instance : SetLike (HyperplaneOrTop R M) M where
  coe C := C.toSubmodule
  coe_injective' := SetLike.coe_injective.comp toSubmodule_injective

@[simp] lemma coe_toSubmodule (C : HyperplaneOrTop R M) : (C.toSubmodule : Set M) = C := rfl

-- QUESTION: do I really need to implement this by hand? (I use this in `mem_of_dual_pt`),
--  but in the non-simp direction
@[simp] lemma mem_coe {x : M} {H : HyperplaneOrTop R M} : x ∈ H.toSubmodule ↔ x ∈ H := by rfl

abbrev of_dual_pt (x : Dual R M) : HyperplaneOrTop R M := ⟨dual .id {x}, by use x⟩

@[simp]
lemma mem_of_dual_pt {x : Dual R M} {y : M} : y ∈ of_dual_pt x ↔ 0 = x y := by simp [← mem_coe]

def top : HyperplaneOrTop R M := of_isHyperplaneOrTop IsHyperplaneOrTop.top

instance : Top (HyperplaneOrTop R M) := ⟨top⟩

@[simp]
lemma top_coe : (⊤ : HyperplaneOrTop R M) = (⊤ : Submodule R M) := by rfl

end HyperplaneOrTop

-- ### Line

def IsHyperplane (S : Submodule R M) := ∃ x : (Dual R M), x ≠ 0 ∧ dual .id {x} = S
    -- := ∃ L : Line R M, IsCompl (L : Submodule R M) S

variable (R M) in
structure Hyperplane extends Submodule R M where
  isHyperplane : IsHyperplane toSubmodule

namespace Hyperplane

instance : Coe (Hyperplane R M) (Submodule R M) where
  coe := toSubmodule

def of_isHyperplane {S : Submodule R M} (hS : S.IsHyperplane) :
    Hyperplane R M := ⟨S, hS⟩

lemma toSubmodule_injective :
    Injective (toSubmodule : Hyperplane R M → Submodule R M) :=
  fun ⟨_, _⟩ _ ↦ by congr!

instance : SetLike (Hyperplane R M) M where
  coe C := C.toSubmodule
  coe_injective' := SetLike.coe_injective.comp toSubmodule_injective

@[simp] lemma coe_toSubmodule (C : Hyperplane R M) : (C.toSubmodule : Set M) = C := rfl

end Hyperplane

end Hyperplane

end Submodule
