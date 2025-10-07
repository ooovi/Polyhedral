/-
Copyright (c) 2025 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.LinearAlgebra.Dimension.Finite

import Polyhedral.Toric.Mathlib.Geometry.Convex.Cone.Corank

/-!
# Submodules of bounded rank

...
-/

open Function Module

variable {R 𝕜 M N M' N' : Type*}

namespace Submodule

section OfRank

-- ### OfRankLe

open Module

variable {R : Type*} [Semiring R]
  {M : Type*} [AddCommMonoid M] [Module R M]
  {M' : Type*} [AddCommMonoid M'] [Module R M']
  {k : Nat}

variable (R M k) in
/-- Submodules of rank at most k. -/
structure OfRankLe extends Submodule R M where
  rankLe : Module.rank R toSubmodule ≤ k

namespace OfRankLe

def of_rankLe {S : Submodule R M} (hS : Module.rank R S ≤ k) : OfRankLe R M k := ⟨S, hS⟩

instance : CoeOut (OfRankLe R M k) (Submodule R M) where
  coe := OfRankLe.toSubmodule

-- instance {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] (S : OfRankLe R M k)
  -- [Free R S] :
--     Module.Finite R S := by
--   obtain ⟨_, _, h⟩ := Cardinal.exists_nat_eq_of_le_nat S.rankLe
--   exact Module.finite_of_rank_eq_nat h

-- lemma Cardinal.ofNat_le_ofNat {n m : Nat} : (n : Cardinal) ≤ (m : Cardinal) ↔ n ≤ m := by simp

-- instance {k : Nat} : Coe (OfRankLe R M k) (OfRankLe R M k.succ) where
--   coe S := of_rankLe (k := k.succ) (S := S) (by
--   exact le_trans S.rankLe <| Cardinal.ofNat_le_ofNat.mp <| Nat.le_succ k
-- )

-- -- NOTE: coercion to polyhedral cone is now already automatic
-- variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
--   {M : Type*} [AddCommGroup M] [Module 𝕜 M] [Module.Finite 𝕜 M] in
-- example (L : LineOrBot 𝕜 M) : PolyhedralCone 𝕜 M := L

lemma toSubmodule_injective :
    Injective (toSubmodule : OfRankLe R M k → Submodule R M) :=
  fun ⟨_, _⟩ _ ↦ by congr!

instance : SetLike (OfRankLe R M k) M where
  coe C := C.toSubmodule
  coe_injective' := SetLike.coe_injective.comp toSubmodule_injective

@[simp] lemma coe_toSubmodule (C : OfRankLe R M k) : (C.toSubmodule : Set M) = C := rfl

end OfRankLe

-- ### OfRank

variable (R M k) in
/-- Submodules of rank k. -/
structure OfRank extends Submodule R M where
  rankEq : Module.rank R toSubmodule = k

namespace OfRank

def of_rankEq {S : Submodule R M} (hS : Module.rank R S = k) : OfRank R M k := ⟨S, hS⟩

instance : CoeOut (OfRank R M k) (Submodule R M) where
  coe := OfRank.toSubmodule

lemma toSubmodule_injective :
    Injective (toSubmodule : OfRank R M k → Submodule R M) :=
  fun ⟨_, _⟩ _ ↦ by congr!

instance : SetLike (OfRank R M k) M where
  coe C := C.toSubmodule
  coe_injective' := SetLike.coe_injective.comp toSubmodule_injective

@[simp] lemma coe_toSubmodule (C : OfRank R M k) : (C.toSubmodule : Set M) = C := rfl

instance : Coe (OfRank R M k) (OfRankLe R M k) where
  coe S := OfRankLe.of_rankLe <| le_of_eq S.rankEq

end OfRank

abbrev LineOrBot := OfRankLe R M 1
abbrev Line := OfRank R M 1

end OfRank

section OfCorank

-- ### OrCorankLe

variable {R : Type*} [Semiring R]
  {M : Type*} [AddCommMonoid M] [Module R M]
  {M' : Type*} [AddCommMonoid M'] [Module R M']
  {k : Nat}

variable (R M k) in
/-- Submodules of rank at most k. -/
structure OfCorankLe extends Submodule R M where
  corankLe : corank toSubmodule ≤ k

namespace OfCorankLe

def of_corankLe {S : Submodule R M} (hS : corank S ≤ k) : OfCorankLe R M k := ⟨S, hS⟩

instance : CoeOut (OfCorankLe R M k) (Submodule R M) where
  coe := OfCorankLe.toSubmodule

lemma toSubmodule_injective :
    Injective (toSubmodule : OfCorankLe R M k → Submodule R M) :=
  fun ⟨_, _⟩ _ ↦ by congr!

instance : SetLike (OfCorankLe R M k) M where
  coe C := C.toSubmodule
  coe_injective' := SetLike.coe_injective.comp toSubmodule_injective

@[simp] lemma coe_toSubmodule (C : OfCorankLe R M k) : (C.toSubmodule : Set M) = C := rfl

end OfCorankLe

-- ### OfRank

variable (R M k) in
/-- Submodules of rank k. -/
structure OfCorank extends Submodule R M where
  corankEq : corank toSubmodule = k

namespace OfCorank

def of_corankEq {S : Submodule R M} (hS : corank S = k) : OfCorank R M k := ⟨S, hS⟩

instance : CoeOut (OfCorank R M k) (Submodule R M) where
  coe := OfCorank.toSubmodule

lemma toSubmodule_injective :
    Injective (toSubmodule : OfCorank R M k → Submodule R M) :=
  fun ⟨_, _⟩ _ ↦ by congr!

instance : SetLike (OfCorank R M k) M where
  coe C := C.toSubmodule
  coe_injective' := SetLike.coe_injective.comp toSubmodule_injective

@[simp] lemma coe_toSubmodule (C : OfCorank R M k) : (C.toSubmodule : Set M) = C := rfl

instance : Coe (OfCorank R M k) (OfCorankLe R M k) where
  coe S := OfCorankLe.of_corankLe <| le_of_eq S.corankEq

end OfCorank

abbrev HyperplaneOrTop := OfCorankLe R M 1
abbrev Hyperplane := OfCorank R M 1

end OfCorank

end Submodule
