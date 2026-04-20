import Mathlib.Analysis.Convex.Basic
import Mathlib.LinearAlgebra.ConvexSpace.AffineSpace
import Polyhedral.Mathlib.LinearAlgebra.ConvexSpace

open Affine Module

section

namespace AffineMap

variable {k : Type*} {V1 : Type*} {P1 : Type*} {V2 : Type*} {P2 : Type*}
  [Ring k] [AddCommGroup V1] [Module k V1]
  [AffineSpace V1 P1] [AddCommGroup V2] [Module k V2] [AffineSpace V2 P2]

def range (f : P1 →ᵃ[k] P2) : AffineSubspace k P2 where
  carrier := {f x | (x : P1)}
  smul_vsub_vadd_mem := by
    simp only [Set.mem_setOf_eq, forall_exists_index]
    intro c _ _ _ x₁ h₁ x₂ h₂ x₃ h₃
    exact ⟨c • (x₁ -ᵥ x₂) +ᵥ x₃, by simp [AffineMap.map_vadd, ← h₁, ← h₂, ← h₃]⟩

@[simp]
theorem mem_range (f : P1 →ᵃ[k] P2) (x : P2) : x ∈ f.range ↔ ∃ (y : P1), f y = x :=
  Iff.rfl

end AffineMap

end

section Convex

namespace Affine

variable {𝕜 E P : Type*} [Ring 𝕜] [PartialOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup E]
   [Module 𝕜 E]

-- we need affine space for convexCombo_eq_sum but we can probably do better
lemma convexComboPair_eq_smul_add_smul {x y a b ab} (a0 : (0 : 𝕜) ≤ a) (b0 : (0 : 𝕜) ≤ b) :
    convexComboPair (M := E) a b a0 b0 ab x y = a • x + b • y := by
  classical
  simp only [convexComboPair, convexCombination_eq_sum (StdSimplex.duple x y a0 b0 ab)]
  unfold StdSimplex.duple
  rw [Finsupp.sum_add_index]
  · simp [Finsupp.sum_single_index]
  · exact (fun i j => zero_smul _ _)
  · simp [add_smul]

/-- In a vector space, convexity is equivalent to star-convexity at all points. -/
theorem Convex_iff_StarConvex (s : Set E) :
    ConvexSpace.Convex 𝕜 s ↔ ∀ ⦃x : E⦄, x ∈ s → StarConvex 𝕜 x s := by
  simp [ConvexSpace.Convex, StarConvex, convexComboPair_eq_smul_add_smul]

end Affine

end Convex

section Ordered

variable {k : Type*} {V1 : Type*} {P1 : Type*} {V2 : Type*} {P2 : Type*}
  [Ring k] [AddCommGroup V1] [Module k V1]
  [AffineSpace V1 P1] [AddCommGroup V2] [Module k V2] [AffineSpace V2 P2]

variable [PartialOrder k] [IsStrictOrderedRing k]
variable {W : Type*} [AddCommGroup W] [Module k W]

open Finsupp Function in
theorem affineMap_convexComboPair (f : P1 →ᵃ[k] W) (finj : Injective f) {a : k} {b hs ht h x y} :
    f (convexComboPair a b hs ht h x y) = convexComboPair a b hs ht h (f x) (f y) := by
  simp only [convexComboPair, ConvexSpace.convexCombination, AddTorsor.convexCombination,
    StdSimplex.duple, Finsupp.coe_add]
  by_cases! ha : a = 0
  · subst ha; simp at h
    simp [h, support_single_ne_zero, Finset.affineCombination]
  by_cases! hb : b = 0
  · subst hb; simp at h
    simp [h, support_single_ne_zero, Finset.affineCombination]
  by_cases! hne : x = y
  · simp [hne, ← single_add, h, support_single_ne_zero, Finset.affineCombination]
  · rw [Finset.map_affineCombination _ id _ _ f]
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

theorem AffineMap.convex_of_injective {f : P1 →ᵃ[k] W} {s : Set P1} (finj : Function.Injective f)
    (hs : ConvexSpace.Convex k s) : Convex k (f '' s) := by
  intro x xs y ys a b ao bo ab
  use convexComboPair a b ao bo ab xs.choose ys.choose
  refine ⟨hs xs.choose_spec.1 ys.choose_spec.1 _ _ _, ?_⟩
  simp [← convexComboPair_eq_smul_add_smul ao bo (ab := ab), affineMap_convexComboPair _ finj,
    xs.choose_spec, ys.choose_spec]

theorem AffineMap.preimage_convex_of_injective {f : P1 →ᵃ[k] W} {s : Set W}
    (finj : Function.Injective f)
    (hs : Convex k s) : ConvexSpace.Convex k (f ⁻¹' s) := by
  intro x xs y ys a b ao bo ab
  simp only [Set.mem_preimage, affineMap_convexComboPair _ finj,
    convexComboPair_eq_smul_add_smul ao bo]
  exact hs (Set.mem_preimage.mp xs) (Set.mem_preimage.mp ys) ao bo ab

end Ordered
