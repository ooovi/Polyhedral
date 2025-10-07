/-
Copyright (c) 2025 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Geometry.Convex.Cone.Pointed
import Polyhedral.Toric.Mathlib.Geometry.Convex.Cone.Pointed

/-!
# Ray

...
-/

open Function Module

variable {R 𝕜 M N M' N' : Type*}

namespace PointedCone

section Ray

-- ### LineOrBot

variable {R : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R]
  {M : Type*} [AddCommMonoid M] [Module R M]
  {M' : Type*} [AddCommMonoid M'] [Module R M']

def IsRayOrBot (P : PointedCone R M) := ∃ x : M, span R {x} = P

variable (R M) in
structure RayOrBot extends PointedCone R M where
  isRayOrBot : IsRayOrBot toSubmodule

namespace RayOrBot

instance : Coe (RayOrBot R M) (PointedCone R M) where
  coe := toSubmodule

def of_isRayOrBot {P : PointedCone R M} (hS : P.IsRayOrBot) : RayOrBot R M := ⟨P, hS⟩

lemma toSubmodule_injective :
    Injective (toSubmodule : RayOrBot R M → PointedCone R M) :=
  fun ⟨_, _⟩ _ ↦ by congr!

instance : SetLike (RayOrBot R M) M where
  coe C := C.toSubmodule
  coe_injective' := SetLike.coe_injective.comp toSubmodule_injective

@[simp] lemma coe_toSubmodule (C : RayOrBot R M) : (C.toSubmodule : Set M) = C := rfl

end RayOrBot

-- ### Line

def IsRay (P : PointedCone R M) := ∃ x : M, x ≠ 0 ∧ span R {x} = P

variable (R M) in
structure Ray extends PointedCone R M where
  isRay : IsRay toSubmodule

namespace Ray

instance : Coe (Ray R M) (PointedCone R M) where
  coe := toSubmodule

def of_isLine {P : PointedCone R M} (hS : P.IsRay) : Ray R M := ⟨P, hS⟩

lemma toSubmodule_injective :
    Injective (toSubmodule : Ray R M → PointedCone R M) :=
  fun ⟨_, _⟩ _ ↦ by congr!

instance : SetLike (Ray R M) M where
  coe C := C.toSubmodule
  coe_injective' := SetLike.coe_injective.comp toSubmodule_injective

@[simp] lemma coe_toSubmodule (C : Ray R M) : (C.toSubmodule : Set M) = C := rfl

end Ray

end Ray

end PointedCone
