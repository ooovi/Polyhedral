/-
Copyright (c) 2025 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Polyhedral cones

...
-/

open Function Module

variable {R 𝕜 M N M' N' : Type*}

namespace Submodule

section Line

-- ### LineOrBot

variable {R : Type*} [Semiring R]
  {M : Type*} [AddCommMonoid M] [Module R M]
  {M' : Type*} [AddCommMonoid M'] [Module R M']

def IsLineOrBot (S : Submodule R M) := ∃ x : M, span R {x} = S

variable (R M) in
structure LineOrBot extends Submodule R M where
  isPreLine : IsLineOrBot toSubmodule

namespace LineOrBot

instance : Coe (LineOrBot R M) (Submodule R M) where
  coe := toSubmodule

-- -- NOTE: coercion to polyhedral cone is now already automatic
-- variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
--   {M : Type*} [AddCommGroup M] [Module 𝕜 M] [Module.Finite 𝕜 M] in
-- example (L : LineOrBot 𝕜 M) : PolyhedralCone 𝕜 M := L

def of_isLineOrBot {S : Submodule R M} (hS : S.IsLineOrBot) : LineOrBot R M := ⟨S, hS⟩

lemma toSubmodule_injective :
    Injective (toSubmodule : LineOrBot R M → Submodule R M) :=
  fun ⟨_, _⟩ _ ↦ by congr!

instance : SetLike (LineOrBot R M) M where
  coe C := C.toSubmodule
  coe_injective' := SetLike.coe_injective.comp toSubmodule_injective

@[simp] lemma coe_toSubmodule (C : LineOrBot R M) : (C.toSubmodule : Set M) = C := rfl

end LineOrBot

-- ### Line

def IsLine (S : Submodule R M) := ∃ x : M, x ≠ 0 ∧ span R {x} = S

variable (R M) in
structure Line extends Submodule R M where
  isLine : IsLine toSubmodule

namespace Line

instance : Coe (Line R M) (Submodule R M) where
  coe := toSubmodule

def of_isLine {S : Submodule R M} (hS : S.IsLine) : Line R M := ⟨S, hS⟩

lemma toSubmodule_injective :
    Injective (toSubmodule : Line R M → Submodule R M) :=
  fun ⟨_, _⟩ _ ↦ by congr!

instance : SetLike (Line R M) M where
  coe C := C.toSubmodule
  coe_injective' := SetLike.coe_injective.comp toSubmodule_injective

@[simp] lemma coe_toSubmodule (C : Line R M) : (C.toSubmodule : Set M) = C := rfl

end Line

end Line

end Submodule
