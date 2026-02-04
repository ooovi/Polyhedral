/-
Copyright (c) 2025 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Order.Partition.Basic

import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.MinkowskiWeyl
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Face.Lattice
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Face.Dual
import Polyhedral.Halfspace

open Function Module OrderDual LinearMap
open Submodule hiding span dual DualClosed
open PointedCone

-- ## RELINT

namespace PointedCone

variable {R : Type*} [Field R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {C : PointedCone R M}
-- variable {p : M →ₗ[R] N →ₗ[R] R}
variable {C F F₁ F₂ : PointedCone R M}

/- A non-topological variant of the relative interior.
  Below two definitions are given. If they are not equivalent, then the more general one should
  be chose and equivalence should be proven when it holds.
-/

-- def IsFaceOf.peal (hF : F.IsFaceOf C) : ConvexCone R M where
--   carrier := C \ F
--   smul_mem' c hc x h := sorry
--   add_mem' x hx y hy := sorry

-- lemma face_iff_dif_cone (C F : PointedCone R M) :
--     F.IsFaceOf C ↔ ∃ D : ConvexCone R M, (C \ F : Set M) = D := sorry

/-- The algeraic relative interior of a pointed cone `C` consists of all the points of `C`
  that do not lie in any proper face of `C`. This definition agrees with the topological
  relative interior in many cases. -/
def relint (C : PointedCone R M) : ConvexCone R M where
  carrier := {x ∈ C | ∀ F : Face C, x ∈ F → F = C}
  smul_mem' c hc x hx := by
    constructor
    · exact C.smul_mem (le_of_lt hc) hx.1
    · intro F hcF
      have h := F.smul_mem ⟨_, le_of_lt <| inv_pos_of_pos hc⟩ hcF
      rw [Nonneg.mk_smul, ← smul_assoc, smul_eq_mul,
        inv_mul_cancel₀ <| (ne_of_lt hc).symm, one_smul] at h
      exact hx.2 F h
  add_mem' x hx y hy := by
    constructor
    · exact add_mem hx.1 hy.1
    · intro F hxy
      exact hx.2 F (F.isFaceOf.mem_of_add_mem hx.1 hy.1 hxy)

lemma mem_relint {C : PointedCone R M} {x : M} :
    x ∈ relint C ↔ x ∈ C ∧ ∀ F : Face C, x ∈ F → F = C := by rfl

lemma relint_le (C : PointedCone R M) : C.relint ≤ C := fun _ h => (C.mem_relint.mp h).1

lemma relint_submodule (S : Submodule R M) : relint (S : PointedCone R M) = S := sorry

-- theorem relint_def_sInf (C : PointedCone R M) :
--     C.relint = sInf {s | dual p.flip (dual p s) = C} := sorry

-- def min_face {x : M} (h : x ∈ C) : Face C := sorry -- sInf {F : Face C | x ∈ F}

-- theorem relint_def_min (C : PointedCone R M) :
--     C.relint = { x ∈ C | C.min_face (x := x) sorry = C } := sorry

lemma IsFaceOf.self_of_le_linSpan (hF : F.IsFaceOf C) (h : C.linSpan ≤ F.linSpan) :
    F = C := sorry

-- NOTE: in infinite dimensions, there are cones with an empty relative interior!
-- Consider e.g. the positive orthant in the space of finitely supported vectors.
-- TODO: generalize to cones with `FinSalRank`
/-- The relative interior is non-empty. -/
lemma relint_nonempty {C : PointedCone R M} (hC : C.FinRank) : Nonempty C.relint := by
  haveI := Module.Finite.iff_fg.mpr hC
  obtain ⟨f, hf, hfC, hind⟩ := exists_fun_fin_finrank_span_eq R (C : Set M)
  use ∑ i, f i
  constructor
  · exact sum_mem (fun c _ => hf c)
  intro ⟨F, hF'⟩ hF
  replace hF := hF'.mem_of_sum_mem hf hF
  refine hF'.self_of_le_linSpan ?_
  simp only [← hfC]
  intro x h
  rw [mem_span_range_iff_exists_fun] at h
  obtain ⟨g, rfl⟩ := h
  exact (linSpan F).sum_mem fun i _ =>
    (linSpan F).smul_mem (g i) <| Submodule.le_span (hF i)

variable (p : M →ₗ[R] N →ₗ[R] R) in
theorem FinSalRank.dual (hC : C.FinSalRank) : FinSalRank (.dual p C) := sorry

-- variable {p : M →ₗ[R] N →ₗ[R] R} in
-- theorem foo_''' (hC : C.FinSalRank) :
--     ∃ φ : N, ∀ x ∈ C, 0 < p x φ ∧ (p x φ = 0 → x ∈ C.lineal) := by
--   have h := hC.dual p
--   have h := relint_nonempty (C := dual p C) sorry
--   obtain ⟨φ, hφ⟩ := h
--   use φ
--   simp [relint] at hφ
--   sorry

-- -- 2. version of Farkas lemma for finite sets
-- variable (p : M →ₗ[R] N →ₗ[R] R) in
-- lemma farkas' (hC : C.FinRank) {x : M} (hx : x ∉ C) (hx' : -x ∉ C) :
--     ∃ φ : N, p x φ = 0 ∧ ∀ y ∈ C, 0 ≤ p y φ ∧ (p y φ = 0 → y = 0) := by
--   obtain ⟨f, hf, h⟩ := PointedCone.farkas hx
--   obtain ⟨g, hg⟩ := exists_dual_pos p hs /- this lemma is not trivial. It proves that a pointed
--     (i.e. salient) cone is contained in some halfspace. g is the normal vector of that halfspace.
--     This lemma is not yet proven, but all the machinery is there. -/
--   use f - (p x f / p x g) • g
--   simp
--   have hgx : 0 < p x g := sorry
--   constructor
--   · simp [ne_of_gt hgx]
--   · intro y hy

--     -- use that f x < 0 but g x and all other f y are >= 0
--     sorry

/-- The relative interior is non-empty. -/
lemma relint_nonempty' (C : PointedCone R M) : C.relint ≠ ⊥ := sorry

lemma relint_disj (F₁ F₂ : Face C) :
    F₁ ≠ F₂ ↔ Disjoint (relint F₁) (relint F₂) (α := ConvexCone R M) := sorry

lemma relint_cover (C : PointedCone R M) :
    ⋃ F : Face C, (relint F : ConvexCone R M) = (C : Set M) := sorry

def relint_partition (C : PointedCone R M) : Partition (C : Set M) where
  parts := { relint (F : PointedCone R M) | (F : Face C) }
  sSupIndep' := sorry
  bot_notMem' := by
    simp only [Set.bot_eq_empty, Set.mem_setOf_eq, ConvexCone.coe_eq_empty, not_exists]
    exact fun F => relint_nonempty' (F : PointedCone R M)
  sSup_eq' := by
    ext x
    -- simp; exact relint_partition C
    sorry

-- Should we introduce a topology/metric before proving lemmas such as the below?

lemma relint_foo (x y : M) (hx : x ∈ relint C) (hy : y ∈ C) :
    ∃ ε > 0, ∀ δ > 0, δ < ε → δ • x + y ∈ relint C := sorry

lemma relint_foo'' (x v : M) (hx : x ∈ relint C) (hy : v ∈ C.linSpan) :
    ∃ ε > 0, ∀ δ ≥ 0, δ < ε → x + δ • v ∈ C := by
  by_contra h
  push_neg at h
  sorry

lemma relint_foo''' (x y : M) (hx : x ∈ relint C) (hy : y ∈ C.linSpan) :
    ∃ ε > 0, ∀ δ ≥ 0, δ < ε → x + δ • y ∈ relint C := sorry

lemma relint_foo' (x y : M) (hx : x ∈ relint C) (hy : y ∈ C) : ∃ z ∈ relint C, z + y = x := sorry

end PointedCone
