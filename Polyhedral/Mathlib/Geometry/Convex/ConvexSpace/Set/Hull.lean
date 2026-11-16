module

public import Polyhedral.Mathlib.Geometry.Convex.AffineMap.Module
public import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.AffineSpace
public import Polyhedral.Mathlib.Geometry.Convex.Hull
public import Mathlib.Geometry.Convex.Segment

public section

open Set
open scoped Pointwise

namespace Convexity

variable {R V A : Type*}

section AddCommMonoid

variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [AddCommMonoid V] [Module R V] [ConvexSpace R V] [IsModuleConvexSpace R V]

@[simp]
theorem span_convexHull (s : Set V) :
    Submodule.span R (convexHull R s : Set V) = Submodule.span R s := by
  ext x
  grind [Submodule.mem_span, mem_convexHull_iff, isConvexSet_coe]

end AddCommMonoid

section AddCommGroup
variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [AddCommGroup V] [Module R V] [ConvexSpace R V] [IsModuleConvexSpace R V]

@[simp] lemma convexHull_neg (s : Set V) : -convexHull R s = convexHull R (-s) := by
  ext x
  simp only [mem_neg, mem_convexHull_iff]
  constructor <;> intro h t hst hcvx
  · exact neg_mem_neg.mp <| h (-t) (neg_subset.mp hst) hcvx.neg
  · exact mem_neg.mp <| h (-t) (neg_subset_neg.mpr hst) hcvx.neg

end AddCommGroup

section Ring
variable [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [AddCommGroup V] [Module R V]
variable [AddTorsor V A] [ConvexSpace R A] [IsAffineConvexSpace R V A]

@[simp]
theorem affineSpan_convexHull (s : Set A) :
    affineSpan R (convexHull R s : Set A) = affineSpan R s := by
  refine le_antisymm ?_ (affineSpan_mono R subset_convexHull_self)
  grw [affineSpan_mono, affineSpan_le_of_subset_coe le_rfl]
  exact convexHull_min (subset_affineSpan R s) (AffineSubspace.isConvexSet _)

@[simp]
theorem vectorSpan_convexHull (s : Set A) :
    vectorSpan R (convexHull R s : Set A) = vectorSpan R s := by
  rw [← direction_affineSpan, affineSpan_convexHull, direction_affineSpan]

variable [ConvexSpace R V] [IsModuleConvexSpace R V]

/-- The convex hull of a Minkowski sum is the Minkowski sum of the convex hulls, since
translation is an affine map on the product convex space (`isAffineMap_vadd`). -/
lemma convexHull_vadd (s₁ : Set V) (s₂ : Set A) :
    convexHull R (s₁ +ᵥ s₂) = convexHull R s₁ +ᵥ convexHull R s₂ := by
  rw [← Set.vadd_image_prod, ← Set.vadd_image_prod, ← convexHull_prod]
  exact (isAffineMap_vadd.image_convexHull _).symm

end Ring

section Field

variable {𝕜 E : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [ConvexSpace 𝕜 E]
  {s t : Set E} {x : E}

protected theorem IsConvexSet.convexHull_union (hs : IsConvexSet 𝕜 s) (ht : IsConvexSet 𝕜 t)
    (hs₀ : s.Nonempty) (ht₀ : t.Nonempty) :
    convexHull 𝕜 (s ∪ t) = ⋃ (x ∈ s) (y ∈ t), Icc 𝕜 x y := by
  refine (convexHull_min (union_subset ?_ ?_) ?_).antisymm ?_
  · exact fun _ hx ↦ mem_iUnion₂.2 ⟨_, hx, mem_iUnion₂.2 ⟨_, ht₀.choose_spec, left_mem_Icc _ _ _⟩⟩
  · exact fun _ hy ↦ mem_iUnion₂.2 ⟨_, hs₀.choose_spec, mem_iUnion₂.2 ⟨_, hy, right_mem_Icc _ _ _⟩⟩
  · refine of_convexCombPair_mem fun _ _ ha hb hab _ hz₁ _ hz₂ => ?_
    simp only [mem_iUnion, exists_prop] at hz₁ hz₂ ⊢
    obtain ⟨_, hx₁, _, hy₁, ⟨_, _, ha₁, hb₁, hab₁, rfl⟩⟩ := hz₁
    obtain ⟨_, hx₂, _, hy₂, ⟨a₂, b₂, ha₂, hb₂, hab₂, rfl⟩⟩ := hz₂
    rw [convexCombPair_convexCombPair_convexCombPair_comm ha hb hab ha₁ hb₁ hab₁ ha₂ hb₂ hab₂]
    exact ⟨_, hs.iConvexComb_mem (by simp [hx₁, hx₂]), _, ht.iConvexComb_mem (by simp [hy₁, hy₂]),
      convexCombPair_mem_Icc (by positivity) (by positivity) (by grind)⟩
  · refine iUnion₂_subset fun x hx => iUnion₂_subset fun y hy => Convexity.Icc_subset_iff.mpr ?_
    refine fun _ _ ↦ (IsConvexSet.convexHull.convexCombPair_mem ?_ ?_)
    · exact (subset_union_left.trans <| subset_convexHull_self ..) hx
    · exact (subset_union_right.trans <| subset_convexHull_self ..) hy

theorem convexHull_union (hs : s.Nonempty) (ht : t.Nonempty) :
    convexHull 𝕜 (s ∪ t) = ⋃ (x ∈ convexHull 𝕜 s) (y ∈ convexHull 𝕜 t), Icc 𝕜 x y := by
  rw [← convexHull_convexHull_union, ← convexHull_union_convexHull]
  apply IsConvexSet.convexHull.convexHull_union .convexHull (convexHull_nonempty.mpr hs)
  exact (convexHull_nonempty.mpr ht)

theorem convexHull_insert (hs : s.Nonempty) :
    convexHull 𝕜 (insert x s) = ⋃ y ∈ convexHull 𝕜 s, Icc 𝕜 x y := by
  rw [insert_eq, convexHull_union (singleton_nonempty _) hs, convexHull_singleton]
  simp

end Field

end Convexity
