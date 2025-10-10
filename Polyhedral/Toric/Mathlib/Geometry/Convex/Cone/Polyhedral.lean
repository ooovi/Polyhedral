/-
Copyright (c) 2025 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.LinearAlgebra.SesquilinearForm

import Polyhedral.Toric.Mathlib.Geometry.Convex.Cone.Dual
import Polyhedral.Toric.Mathlib.Geometry.Convex.Cone.Pointed_FG

/-!
# Polyhedral cones

...
-/

open Function Module
open Submodule hiding span

variable {𝕜 M N : Type*}

-- Now we are ready to define PolyhedralCone, because from here on we assume V=H.
-- From here on we also mke no use any longer of the precise pairing.

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup M] [AddCommGroup N]
  [Module 𝕜 M] [Module.Finite 𝕜 M] -- {p : M →ₗ[𝕜] N →ₗ[𝕜] 𝕜} [p.IsPerfPair]

/-- Abbreviation for PointedCone.FG. Intended for use in contexts with V=H. -/
abbrev PointedCone.IsPolyhedral (C : PointedCone 𝕜 M) := C.FG

-- this definition allows to prove certain statement immediately from FG.
example {C C' : PointedCone 𝕜 M} (hC : C.IsPolyhedral) (hC' : C'.IsPolyhedral) :
    (C ⊔ C').IsPolyhedral := Submodule.FG.sup hC hC'

variable {C C' : PointedCone 𝕜 M} (hC : C.IsPolyhedral) (hC' : C'.IsPolyhedral)

alias IsPolyhedral.map := Submodule.FG.map
-- alias IsPolyhedral.fg_of_fg_map := Submodule.fg_of_fg_map

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup M] [AddCommGroup N]
  [Module 𝕜 M]

variable (𝕜 M) in
structure PolyhedralCone extends PointedCone 𝕜 M where
  isFG : FG toSubmodule

namespace PolyhedralCone

@[coe] abbrev toPointedCone (C : PolyhedralCone 𝕜 M) : PointedCone 𝕜 M := C.toSubmodule

instance : Coe (PolyhedralCone 𝕜 M) (PointedCone 𝕜 M) where
  coe := toPointedCone

def of_FG {C : PointedCone 𝕜 M} (hC : C.FG) : PolyhedralCone 𝕜 M := ⟨C, hC⟩

lemma toPointedCone_injective :
    Injective (toPointedCone : PolyhedralCone 𝕜 M → PointedCone 𝕜 M) :=
  fun ⟨_, _⟩ _ ↦ by congr!

variable [Module.Finite 𝕜 M]

instance : SetLike (PolyhedralCone 𝕜 M) M where
  coe C := C.toPointedCone
  coe_injective' := SetLike.coe_injective.comp toPointedCone_injective

@[simp] lemma coe_toPointedCone (C : PolyhedralCone 𝕜 M) : (C.toPointedCone : Set M) = C := rfl

def span (s : Finset M) : PolyhedralCone 𝕜 M := of_FG (Submodule.fg_span <| s.finite_toSet)

def span_of_finite {S : Set M} (hfin : S.Finite) : PolyhedralCone 𝕜 M
  := of_FG (Submodule.fg_span hfin)

def ray (x : M) : PolyhedralCone 𝕜 M := span {x}

instance : Bot (PolyhedralCone 𝕜 M) := ⟨of_FG fg_bot⟩
instance : Top (PolyhedralCone 𝕜 M) := ⟨of_FG Module.Finite.fg_top⟩

instance : Min (PolyhedralCone 𝕜 M) where
  min C D := of_FG <| PointedCone.inf_fg C.isFG D.isFG
instance : Max (PolyhedralCone 𝕜 M) where
  max C D := of_FG <| PointedCone.sup_fg C.isFG D.isFG
-- NOTE: on cones, ⊔ also acts as Minkowski sum

lemma sup_is_Msum (C D : PolyhedralCone 𝕜 M) : C ⊔ D = { c + d | (c ∈ C) (d ∈ D) } := by
  sorry

variable {𝕜 M N : Type*}
  [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup M] [Module 𝕜 M] [Module.Finite 𝕜 M]
  [AddCommGroup N] [Module 𝕜 N] -- [Module.Finite 𝕜 M]

variable [Module.Finite 𝕜 N]
variable (p : M →ₗ[𝕜] N →ₗ[𝕜] 𝕜) [p.IsPerfPair]

def dual (C : PolyhedralCone 𝕜 M) : PolyhedralCone 𝕜 N
  := of_FG (PointedCone.dual_fg p C.isFG)

def dual_of_fg (C : PointedCone 𝕜 M) (hC : C.FG) : PolyhedralCone 𝕜 N
  := dual p (of_FG hC)

def dual_of_finset (s : Finset M) : PolyhedralCone 𝕜 N
  := dual p (of_FG <| Submodule.fg_span s.finite_toSet)

def dual_of_finite (S : Set M) (hS : S.Finite) : PolyhedralCone 𝕜 N
  := dual p (of_FG <| Submodule.fg_span hS)

variable [Module.Finite 𝕜 N]
variable {p : M →ₗ[𝕜] N →ₗ[𝕜] 𝕜} [p.IsPerfPair]

-- probably needs assumptions, such as perfect pairing maybe?
lemma dual_dual_flip (C : PolyhedralCone 𝕜 N) : dual p (dual p.flip C) = C := by
  sorry
lemma dual_flip_dual (C : PolyhedralCone 𝕜 M) : dual p.flip (dual p C) = C := by
  sorry

section Map

variable {𝕜 : Type*} [Semiring 𝕜] [PartialOrder 𝕜] [IsOrderedRing 𝕜]
variable {M N M' N' : Type*}
  [AddCommMonoid M] [Module 𝕜 M]
  -- [AddCommGroup N] [Module 𝕜 N]
  [AddCommMonoid M'] [Module 𝕜 M'] [Module.Finite 𝕜 M']
  -- [AddCommGroup N'] [Module 𝕜 N'] [Module.Finite 𝕜 N']

variable (f : M →ₗ[𝕜] M')

theorem _root_.Submodule.FG.comap {S : Submodule 𝕜 M'} (hs : S.FG) : (S.comap f).FG := by
  sorry

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {M N M' N' : Type*}
  [AddCommGroup M] [Module 𝕜 M]
  -- [AddCommGroup N] [Module 𝕜 N]
  [AddCommGroup M'] [Module 𝕜 M'] [Module.Finite 𝕜 M']
  -- [AddCommGroup N'] [Module 𝕜 N'] [Module.Finite 𝕜 N']

variable (f : M →ₗ[𝕜] M')

def map (C : PolyhedralCone 𝕜 M) : PolyhedralCone 𝕜 M'
  := of_FG <| Submodule.FG.map (f.restrictScalars _) C.isFG

local notation3 "𝕜≥0" => {c : 𝕜 // 0 ≤ c}

def comap (C : PolyhedralCone 𝕜 M') : PolyhedralCone 𝕜 M
  := of_FG <| Submodule.FG.comap (f.restrictScalars _) C.isFG

variable [Module.Finite 𝕜 M]

lemma map_dual (C : PolyhedralCone 𝕜 M) :
    dual (Dual.eval 𝕜 M') (map f C) = comap f.dualMap (dual (Dual.eval 𝕜 M) C) := by
  sorry -- ext x; simp

instance : Neg (PolyhedralCone 𝕜 M) where
  neg C := of_FG <| Submodule.FG.map (-.id) C.isFG

instance : Coe (Submodule 𝕜 M) (PolyhedralCone 𝕜 M) where
  coe S := of_FG <| PointedCone.ofSubmodule.fg_of_fg
    <| (Submodule.fg_iff_finiteDimensional S).mpr inferInstance


-- /-- A linear subspace is a polyhedral cone -/
-- lemma IsPolyhedral.submodule (S : Submodule 𝕜 M) : (S : PointedCone 𝕜 M).FG
--   := PointedCone.ofSubmodule.FG_of_FG
--     <| (Submodule.fg_iff_finiteDimensional S).mpr inferInstance

end Map

end PolyhedralCone

-- namespace PolyhedralCone

-- variable {R M N : Type*}
--   [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
--   [AddCommGroup M] [Module R M] [Module.Finite R M] [Projective R M]
--   [AddCommGroup N] [Module R N] -- [Module.Finite 𝕜 M]

-- instance : Bot (PolyhedralCone R M) := ⟨⊥, .bot⟩

-- instance uniqueBot : Unique (⊥ : PolyhedralCone R M) :=
--   inferInstanceAs <| Unique (⊥ : PointedCone R M)

-- instance : Top (PolyhedralCone R M) := ⟨ ⊤, .top ⟩

-- instance : Min (PolyhedralCone R M) where
--   min C C' := ⟨C ⊓ C', C.isPolyhedral.inf C'.isPolyhedral⟩

-- @[simp, norm_cast] lemma coe_inf (C D : PolyhedralCone R M) :
--     (C ⊓ D).toPointedCone = C.toPointedCone ⊓ D.toPointedCone := rfl

-- instance : SemilatticeInf (PolyhedralCone R M) :=
--   PolyhedralCone.toPointedCone_injective.semilatticeInf _ coe_inf

-- -- TODO: add simp lemmas

-- variable {𝕜 M N : Type*}
--   [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
--   [AddCommGroup M] [Module 𝕜 M] [Module.Finite 𝕜 M]
--   [AddCommGroup N] [Module 𝕜 N] -- [Module.Finite 𝕜 M]

-- def of_IsPolyhedral {C : PointedCone 𝕜 M} (hC : C.IsPolyhedral) : PolyhedralCone 𝕜 M := ⟨ C, hC ⟩
-- def of_fg {C : PointedCone 𝕜 M} (hC : C.FG) : PolyhedralCone 𝕜 M := of_IsPolyhedral (.of_fg 𝕜 hC)

-- def span {S : Set M} (hfin : S.Finite) : PolyhedralCone 𝕜 M := of_IsPolyhedral (.span hfin)

-- variable (p : M →ₗ[𝕜] N →ₗ[𝕜] 𝕜) [p.IsPerfPair]
-- variable [Module.Finite 𝕜 N]
-- variable {p : M →ₗ[𝕜] N →ₗ[𝕜] 𝕜} [p.IsPerfPair]

-- instance : Max (PolyhedralCone 𝕜 M) where
--   max C C' := ⟨C ⊔ C', C.isPolyhedral.sup C'.isPolyhedral⟩

-- @[simp, norm_cast] lemma coe_sup (C D : PolyhedralCone 𝕜 M) :
--     (C ⊔ D).toPointedCone = C.toPointedCone ⊔ D.toPointedCone := rfl

-- instance : SemilatticeSup (PolyhedralCone 𝕜 M) :=
--   PolyhedralCone.toPointedCone_injective.semilatticeSup _ coe_sup

-- lemma dual_inf {C C' : PolyhedralCone 𝕜 M} : dual p (C ⊓ C') = dual p C ⊔ dual p C' :=
--   sorry

-- lemma dual_sup {C C' : PolyhedralCone 𝕜 M} : dual p (C ⊔ C') = dual p C ⊓ dual p C' :=
--   sorry

-- end PolyhedralCone

-- /- Lattice structure -/

-- namespace PolyhedralCone

-- variable [Field 𝕜] [LinearOrder 𝕜] [IsOrderedRing 𝕜] [AddCommGroup M] [Module 𝕜 M] {s : Set (Dual 𝕜 M)} {w : M}

-- def ofSubmodule (S : Submodule 𝕜 M) : PolyhedralCone 𝕜 M := ⟨ S, .submodule S ⟩

-- instance : Coe (Submodule 𝕜 M) (PolyhedralCone 𝕜 M) := ⟨ .ofSubmodule ⟩

-- instance completeLattice : CompleteLattice (PolyhedralCone 𝕜 M) :=
--   { (inferInstance : OrderTop (PolyhedralCone 𝕜 M)),
--     (inferInstance : OrderBot (PolyhedralCone 𝕜 M)) with
--     sup := fun a b ↦ sInf { x | a ≤ x ∧ b ≤ x }
--     le_sup_left := fun _ _ ↦ le_sInf' fun _ ⟨h, _⟩ ↦ h
--     le_sup_right := fun _ _ ↦ le_sInf' fun _ ⟨_, h⟩ ↦ h
--     sup_le := fun _ _ _ h₁ h₂ ↦ sInf_le' ⟨h₁, h₂⟩
--     inf := (· ⊓ ·)
--     le_inf := fun _ _ _ ↦ Set.subset_inter
--     inf_le_left := fun _ _ ↦ Set.inter_subset_left
--     inf_le_right := fun _ _ ↦ Set.inter_subset_right
--     sSup S := sInf {sm | ∀ s ∈ S, s ≤ sm}
--     le_sSup := fun _ _ hs ↦ le_sInf' fun _ hq ↦ by exact hq _ hs
--     sSup_le := fun _ _ hs ↦ sInf_le' hs
--     le_sInf := fun _ _ ↦ le_sInf'
--     sInf_le := fun _ _ ↦ sInf_le' }

-- end PolyhedralCone
