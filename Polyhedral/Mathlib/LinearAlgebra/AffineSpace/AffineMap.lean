import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Face.Basic
import Mathlib.Geometry.Convex.ConvexSpace.AffineSpace
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Basic
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Lattice
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Hull
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.AffineSpace

open Affine Module

section

namespace AffineMap

variable {k : Type*} {V : Type*} {P : Type*} {V2 : Type*} {P2 : Type*}
  [Ring k] [AddCommGroup V] [Module k V]
  [AffineSpace V P] [AddCommGroup V2] [Module k V2] [AffineSpace V2 P2]

/-- The range of an affine map is an affine subspace. -/
def range (f : P →ᵃ[k] P2) : AffineSubspace k P2 where
  carrier := Set.range f
  smul_vsub_vadd_mem := by
    simp only [Set.mem_range, forall_exists_index]
    intro c _ _ _ x₁ h₁ x₂ h₂ x₃ h₃
    exact ⟨c • (x₁ -ᵥ x₂) +ᵥ x₃, by simp [map_vadd, ← h₁, ← h₂, ← h₃]⟩

instance instNonemptyRange (f : P →ᵃ[k] P2) : Nonempty (range f) :=
  Set.instNonemptyRange f

@[simp]
theorem mem_range (f : P →ᵃ[k] P2) (x : P2) : x ∈ f.range ↔ ∃ (y : P), f y = x :=
  Iff.rfl

lemma range_direction (f : P →ᵃ[k] P2) : f.range.direction = f.linear.range := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro _ ⟨p₁, h₁, p₂, h₂, h⟩
    simp only [SetLike.mem_coe, mem_range] at h₁ h₂
    obtain ⟨p₁, rfl⟩ := h₁
    obtain ⟨p₂, rfl⟩ := h₂
    exact ⟨p₁ -ᵥ p₂, h ▸ f.linearMap_vsub _ _⟩
  · apply Submodule.span_le.mp
    intro v hv
    rw [Submodule.span_coe_eq_restrictScalars] at hv
    obtain ⟨w, rfl⟩ := hv
    apply Submodule.subset_span
    simp only [Set.mem_vsub, SetLike.mem_coe, mem_range, exists_exists_eq_and]
    exact ⟨(w +ᵥ Classical.arbitrary P), (Classical.arbitrary P), by simp⟩

def rangeRestrict (f : P →ᵃ[k] P2) : P →ᵃ[k] f.range where
  toFun p := ⟨f p, p, rfl⟩
  linear := (LinearEquiv.ofEq _ _ f.range_direction.symm).toLinearMap ∘ₗ f.linear.rangeRestrict
  map_vadd' _ _ := by ext; simp [map_vadd]

lemma rangeRestrict_injective_iff (f : P →ᵃ[k] P2) :
    (rangeRestrict f).toFun.Injective ↔ f.toFun.Injective := by
  simp [Function.Injective, rangeRestrict]

variable [PartialOrder k] [IsStrictOrderedRing k] in
attribute [local instance] AddTorsor.toConvexSpace in
open Convexity in
lemma range_isConvexSet (f : P →ᵃ[k] P2) : IsConvexSet k (f.range : Set P2) := by
  simpa [range, SetLike.coe, ← Set.image_univ] using IsConvexSet.univ.image (f.isAffineMap)

end AffineMap

end
