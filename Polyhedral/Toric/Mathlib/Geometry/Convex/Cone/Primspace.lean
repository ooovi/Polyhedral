/-
Copyright (c) 2025 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.LinearAlgebra.SesquilinearForm

import Polyhedral.Toric.Mathlib.Geometry.Convex.Cone.Polyhedral

/-!
# Polyhedral cones

...
-/

open Function Module

variable {𝕜 M N M' N' : Type*}

-- Now we are ready to define PolyhedralCone, because from here on we assume V=H.
-- From here on we also mke no use any longer of the precise pairing.

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup M] [Module 𝕜 M] [Module.Finite 𝕜 M]
  [AddCommGroup N] [Module 𝕜 N] [Module.Finite 𝕜 N]
  [AddCommGroup M'] [Module 𝕜 M'] [Module.Finite 𝕜 M']
  [AddCommGroup N'] [Module 𝕜 N'] [Module.Finite 𝕜 N']
  -- {p : M →ₗ[𝕜] N →ₗ[𝕜] 𝕜} [p.IsPerfPair]

namespace PolyhedralCone

def IsPrimspace (P : PolyhedralCone 𝕜 M) := ∃ x : Dual 𝕜 M, dual .id (ray x) = P
  -- := ∃ x : Dual 𝕜 M, dual_of_finset .id {x} = P

lemma IsPrimspace.of_map {f : M →ₗ[𝕜] N} (hf : Surjective f)
    {P : PolyhedralCone 𝕜 M} (hP : P.IsPrimspace) : (map f P).IsPrimspace := by
  unfold IsPrimspace
  obtain ⟨x, hx⟩ := hP
  -- use f.dualMap x
  sorry

variable (𝕜 M) in
abbrev Primspace := { P : PolyhedralCone 𝕜 M // P.IsPrimspace }

namespace Primspace

def map {f : M →ₗ[𝕜] M'} (P : Primspace 𝕜 M) (hf : Surjective f) : Primspace 𝕜 M'
  := ⟨_, IsPrimspace.of_map hf P.2⟩

-- TODO: comap

lemma id_surj : Surjective (LinearMap.id : M →ₗ[𝕜] M) := by
  intro x
  use x
  rfl

lemma neg_id_surj : Surjective (-LinearMap.id : M →ₗ[𝕜] M) := by
  intro x
  use -x
  simp

def opposite (P : Primspace 𝕜 M) := map P neg_id_surj

def boundary (P : Primspace 𝕜 M) : Submodule 𝕜 M where
  carrier := P ⊓ P.opposite
  add_mem' := sorry
  zero_mem' := sorry
  smul_mem' := sorry

end Primspace

-- NOTE: not generally true: p needs to be not zero.
-- lemma ray_dual (x : M) : ((ray x).dual p).IsPrimspace

end PolyhedralCone
