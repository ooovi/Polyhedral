/-
Copyright (c) 2026 Vlad Tsyrklevich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vlad Tsyrklevich
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs

/-! AffineSpace lemmas -/

@[expose] public section

open Set
open scoped Pointwise

namespace Submodule

variable {k V : Type*} [Ring k] [AddCommGroup V] [Module k V]

@[simp]
theorem coe_toAffineSubspace (p : Submodule k V) : (p.toAffineSubspace : Set V) = (p : Set V) :=
  rfl

/-- Reinterprets a `p : AffineSubspace k V` that includes `0` as a `Submodule k V`. -/
def ofAffineSubspace {p : AffineSubspace k V} (hp : 0 ∈ p) : Submodule k V where
  carrier := p
  add_mem' ha hb := by simpa using p.smul_vsub_vadd_mem' 1 ha hp hb
  zero_mem' := by simpa
  smul_mem' c x hx := by simpa using p.smul_vsub_vadd_mem' c hx hp hp

@[simp]
theorem ofAffineSubspace_toAffineSubspace {p : AffineSubspace k V} (hp : 0 ∈ p) :
    ↑(ofAffineSubspace hp) = p := rfl

@[simp]
theorem toAffineSubspace_ofAffineSubspace {p : Submodule k V} (hp : 0 ∈ p) :
    ↑(ofAffineSubspace (p := p) hp) = p := rfl

instance : CanLift (AffineSubspace k V) (Submodule k V) toAffineSubspace (0 ∈ ·) where
  prf _ hp := ⟨ofAffineSubspace hp, ofAffineSubspace_toAffineSubspace hp⟩

end Submodule

namespace AffineSubspace

variable {k V : Type*} [Ring k] [AddCommGroup V] [Module k V]

@[simp]
theorem toAffineSubspace_ne_bot (p : Submodule k V) : p.toAffineSubspace ≠ ⊥ :=
  (AffineSubspace.nonempty_iff_ne_bot _).mp ⟨0, p.zero_mem⟩

end AffineSubspace

section AffineSpace'

variable {k : Type*} {V : Type*} [Ring k] [AddCommGroup V] [Module k V]

-- TODO: Delete once mathlib PR #43582 lands
@[simp]
lemma affineSpan_insert_zero' (s : Set V) :
    affineSpan k (insert 0 s) = Submodule.span k s := by
  rw [AffineSubspace.ext_iff, ← Submodule.span_insert_zero]
  refine affineSpan_subset_span.antisymm ?_
  rw [← vectorSpan_add_self, vectorSpan_def]
  refine Subset.trans ?_ <| subset_add_left _ <| mem_insert ..
  gcongr
  exact subset_sub_left <| mem_insert ..

theorem affineSpan_eq_span_iff_zero_mem {s : Set V} :
    affineSpan k s = ↑(Submodule.span k s) ↔ 0 ∈ affineSpan k s := by
  refine ⟨by simp +contextual, fun h ↦ ?_⟩
  rw [← affineSpan_insert_eq_affineSpan _ h, affineSpan_insert_zero']

alias ⟨_, affineSpan_eq_span_of_zero_mem⟩ := affineSpan_eq_span_iff_zero_mem

end AffineSpace'
