import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Face.Basic
import Polyhedral.Mathlib.LinearAlgebra.ConvexSpace

open Affine Module

section

namespace AffineMap

variable {k : Type*} {V1 : Type*} {P1 : Type*} {V2 : Type*} {P2 : Type*}
  [Ring k] [AddCommGroup V1] [Module k V1]
  [AffineSpace V1 P1] [AddCommGroup V2] [Module k V2] [AffineSpace V2 P2]

def range (f : P1 →ᵃ[k] P2) : AffineSubspace k P2 where
  carrier := Set.range f
  smul_vsub_vadd_mem := by
    simp only [Set.mem_range, forall_exists_index]
    intro c _ _ _ x₁ h₁ x₂ h₂ x₃ h₃
    exact ⟨c • (x₁ -ᵥ x₂) +ᵥ x₃, by simp [AffineMap.map_vadd, ← h₁, ← h₂, ← h₃]⟩

@[simp]
theorem mem_range (f : P1 →ᵃ[k] P2) (x : P2) : x ∈ f.range ↔ ∃ (y : P1), f y = x :=
  Iff.rfl

end AffineMap

end

section Ordered

open ConvexSpace

namespace AffineMap

variable {k V1 P1 : Type*} [Ring k] [PartialOrder k] [IsStrictOrderedRing k]
variable [AddCommGroup V1] [Module k V1] [AffineSpace V1 P1]
variable {W : Type*} [AddCommGroup W] [Module k W]
variable {f : P1 →ᵃ[k] W}

open Finsupp Function in
theorem affineMap_convexComboPair_of_injective {a : k} {b hs ht h x y}
    (finj : Injective f) :
    f (convexComboPair a b hs ht h x y) = convexComboPair a b hs ht h (f x) (f y) := by
  simp only [convexComboPair, convexCombination, AddTorsor.convexCombination,
    StdSimplex.duple, Finsupp.coe_add]
  by_cases! ha : a = 0
  · subst ha; simp at h
    simp [h, support_single_ne_zero, Finset.affineCombination]
  by_cases! hb : b = 0
  · subst hb; simp at h
    simp [h, support_single_ne_zero, Finset.affineCombination]
  by_cases! hne : x = y
  · simp [hne, ← single_add, h, support_single_ne_zero, Finset.affineCombination]
  · rw [Finset.map_affineCombination _ _ _ _ f]
    classical
    · have fhne : f x ≠ f y := Ne.intro fun a ↦ hne (finj a)
      rw [support_single_add_single hne ha hb, support_single_add_single fhne ha hb]
      · simp [Finset.affineCombination_apply, Finset.sum_pair hne, single_apply, hne, hne.symm,
          Finset.sum_pair fhne, fhne, fhne.symm]
    · simp only [support_single_add_single hne ha hb, Pi.add_apply, single_apply, reduceIte,
        Finset.sum_pair hne]
      split_ifs with h'
      · exact (hne h'.symm).elim
      · simp [h]

-- probably useful, but annoying to prove
-- open Finsupp Function in
-- theorem affineMap_convexCombination_of_injective {a : k} {w} (finj : Injective f) :
--     f (AddTorsor.instConvexSpace.convexCombination w) =
--     AddTorsor.instConvexSpace.convexCombination (StdSimplex.map (R := k) f w) := by sorry

/-- Injective affine maps are convex, i.e. they map convex sets to convex sets. -/
theorem convex_of_injective {s : Set P1} (finj : Function.Injective f)
    (hs : IsConvex k s) : IsConvex k (f '' s) := by
  intro x xs y ys a b ao bo ab
  use convexComboPair a b ao bo ab xs.choose ys.choose
  refine ⟨hs xs.choose_spec.1 ys.choose_spec.1 _ _ _, ?_⟩
  simp [affineMap_convexComboPair_of_injective finj, xs.choose_spec, ys.choose_spec]

lemma range_convex_of_injective (finj : Function.Injective f) :
    IsConvex k (f.range : Set W) := by
  simpa [range, SetLike.coe, ← Set.image_univ] using convex_of_injective finj (isConvex_univ k)

theorem preimage_convex_of_injective {s : Set W}
    (finj : Function.Injective f)
    (hs : IsConvex k s) : IsConvex k (f ⁻¹' s) := by
  intro x xs y ys a b ao bo ab
  simp only [Set.mem_preimage, affineMap_convexComboPair_of_injective finj]
  exact hs (Set.mem_preimage.mp xs) (Set.mem_preimage.mp ys) ao bo ab

/-- Injective affine maps commute with the convex hull. -/
theorem convexHull (finj : Function.Injective f)
    (s : Set P1) : ConvexSpace.convexHull k (f '' s) = f '' (convexHull k s) := by
  simp only [ConvexSpace.convexHull, ClosureOperator.ofCompletePred_apply, Set.le_eq_subset,
    Set.iInf_eq_iInter]
  ext x
  simp only [Set.mem_iInter, Subtype.forall, Set.image_subset_iff, and_imp, Set.mem_image]
  constructor
  · intro h
    have : x ∈ f.range :=
      h f.range (by simp [range, SetLike.coe, Set.preimage_range]) (range_convex_of_injective finj)
    obtain ⟨x', hx'⟩ := (mem_range f x).mp this
    use x'
    subst hx'
    simp only [and_true]
    intro a' ha' hca'
    refine finj.mem_set_image.mp <| h (f '' a') ?_ (f.convex_of_injective finj hca')
    simp [Set.preimage_image_eq _ finj, ha']
  · intro h a hfa hc
    obtain ⟨x, hx, rfl⟩ := h
    refine Set.mem_preimage.mp (hx _ hfa (AffineMap.preimage_convex_of_injective finj ?_))
    simp [hc]

def _root_.ConvexSpace.IsConvex.preimage {s : Set W} (hs : IsConvex k s)
    (finj : Function.Injective f) :
    ConvexSpace.ConvexSet k P1 :=
  ⟨_, AffineMap.preimage_convex_of_injective finj hs⟩

open AffineMap in
theorem _root_.ConvexSpace.IsConvex.preimage_isFaceOf {F C : PointedCone k W} (hf : F.IsFaceOf C)
    (finj : Function.Injective f) :
    ((pointedCone_convex F).preimage finj).IsFaceOf ((pointedCone_convex C).preimage finj) where
  subset := Set.preimage_mono hf.le
  left_mem_of_mem_openSegment  := by
    rintro x hx y hy z hz ⟨a, b, ha, hb, hab, hzo⟩
    refine hf.mem_of_smul_add_mem hx (C.smul_mem hb.le hy) ha ?_
    rwa [← convexComboPair_eq_smul_add_smul ha.le hb.le hab,
      ← affineMap_convexComboPair_of_injective finj, hzo]

end AffineMap

end Ordered
