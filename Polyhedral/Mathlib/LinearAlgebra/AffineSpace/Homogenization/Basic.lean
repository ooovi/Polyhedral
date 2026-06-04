import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Convexity
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Face.Lattice
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Face
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.AffineSpace
import Polyhedral.Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Polyhedral.Mathlib.LinearAlgebra.AffineSpace.Homogenization.Canonical
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Module


namespace Affine

section Ring

open Function Submodule

variable {R : Type*} [Ring R]
variable {V : Type*} [AddCommGroup V] [Module R V]
variable {A : Type*} [AddTorsor V A]
variable {W : Type*} [AddCommGroup W] [Module R W]

variable (R A W) in
/-- An embedding of an affine space `A` into a vector space `W` s.t. the image of `A` is exactly the
weight-1 hyperplane under a given linear weight map.
Follows Definition 4.2 in https://www.cis.upenn.edu/~jean/gma-v2-root.pdf -/
class Homogenization extends ofPoint : A →ᵃ[R] W where
  ofPoint_injective : Injective ofPoint
  weight : W →ₗ[R] R
  ofPoint_range_eq_preimage_weight_one : ofPoint.range = weight ⁻¹' {1}

open CanonicalHomogenization in
/-- The canonical homogenization is a homogenization. -/
instance : Homogenization R A (CanonicalHomogenization R A) where
  ofPoint := ofPoint
  ofPoint_injective := ofPoint_injective
  weight := weight
  ofPoint_range_eq_preimage_weight_one := ofPoint_range_eq_preimage_weight_one

namespace Homogenization

variable [hom : Homogenization R A W]

abbrev ofVector := hom.ofPoint.linear

theorem linear_inj : Injective hom.ofVector := by
  simp [hom.ofPoint_injective]

/-- Embedding the underlying vector space is exactly the weight-0 hyperplane. -/
theorem ofPoint_linear_range_eq_weight_ker : hom.ofVector.range = hom.weight.ker := by
  ext x
  let a₀ := Classical.arbitrary A
  simp only [LinearMap.mem_range, LinearMap.mem_ker]
  have : (∃ y, hom.ofVector y = x) ↔ ∃ a b : A, hom.ofVector (a -ᵥ b) = x :=
    ⟨fun ⟨y, hy⟩ => ⟨y +ᵥ a₀, a₀, by simp [vadd_vsub, hy]⟩, fun ⟨a, b, hab⟩ => ⟨a -ᵥ b, hab⟩⟩
  rw [this]
  have hh := Set.ext_iff.mp hom.ofPoint_range_eq_preimage_weight_one
  constructor
  · rintro ⟨a, b, hab⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hh
    simp [← hab, map_sub, (hh (ofPoint b)).mp ⟨b, rfl⟩, (hh (ofPoint a)).mp ⟨a, rfl⟩]
  · intro h
    have ha := Set.mem_preimage.mp <| (hh (hom.ofPoint a₀)).mp (by simp)
    obtain ⟨b, hb⟩ : x + hom.ofPoint a₀ ∈ (hom.ofPoint.range : Set W) := by
      simpa [hom.ofPoint_range_eq_preimage_weight_one, Set.mem_preimage, map_add, h]
    exact ⟨b, a₀, by simp [AffineMap.linearMap_vsub, hb]⟩

/-- The homogenization of a point in `A` has weight 1. -/
lemma weight_one (a₀ : A) : hom.weight (hom.ofPoint a₀) = 1 := by
  convert Set.ext_iff.mp hom.ofPoint_range_eq_preimage_weight_one (hom.ofPoint a₀)
  simp [SetLike.mem_coe, AffineMap.mem_range, exists_apply_eq_apply, Set.mem_preimage,
    Set.mem_singleton_iff, true_iff]

variable [Nontrivial R] in
theorem ofPoint_ne_zero (x : A) : hom.ofPoint x ≠ (0 : W) := by
  intro hn
  have := congrArg hom.weight hn
  simp [weight_one x] at this

/-- The homogenization of a point in `V` has weight 0. -/
lemma weight_zero (v : V) : hom.weight (hom.ofVector v) = 0 := by
  simp [LinearMap.mem_ker.mp, ← ofPoint_linear_range_eq_weight_ker]

theorem span_range_ofPoint : span R (hom.ofPoint.range : Set W) = ⊤ := by
  refine eq_top_iff'.mpr (fun x ↦ ?_)
  let a₀ := Classical.arbitrary A
  -- projecting x to weight 0 along a₀ gives sth in the span of image of ofPoint
  have hlin : x - hom.weight x • hom.ofPoint a₀ ∈ Submodule.span R hom.ofPoint.range := by
    obtain ⟨v, hv⟩ : x - hom.weight x • hom.ofPoint a₀ ∈ hom.ofVector.range := by
      simp [ofPoint_linear_range_eq_weight_ker, weight_one a₀]
    have : hom.ofVector v = hom.ofPoint (v +ᵥ a₀) - hom.ofPoint a₀ := by simp
    rw [← hv, this]
    apply Submodule.sub_mem <;> apply Submodule.subset_span
    · exact ⟨v +ᵥ a₀, rfl⟩
    · exact ⟨a₀, rfl⟩
  simpa using
    Submodule.add_mem _ hlin <| smul_mem _ (hom.weight x) (subset_span ⟨a₀, rfl⟩)

open CanonicalHomogenization HomogenizationExpr in
/-- Every homogenization is linearly equivalent to the canonical homogenization. -/
noncomputable def canonEquiv : W ≃ₗ[R] CanonicalHomogenization R A where
  toFun x := by
    -- pick an arbitrary base point
    let a₀ := Classical.arbitrary A
    -- project x to weight zero along a₀
    have v : x - hom.weight x • hom.ofPoint a₀ ∈ hom.ofVector.range := by
        simp [ofPoint_linear_range_eq_weight_ker, weight_one a₀]
    -- for v the preimage of the projected x, we have x = v + (weight x) * a₀
    exact .mk (.mk ((LinearEquiv.ofInjective _ hom.linear_inj).invFun ⟨_, v⟩) (hom.weight x) a₀)
  map_add' x y := by
    simp [CanonicalHomogenization.mk_add_mk, add_smul, ← LinearEquiv.map_add]
    abel_nf
  map_smul' c x := by
    simp only [map_smul, smul_assoc, LinearEquiv.invFun_eq_symm, RingHom.id_apply, smul_mk,
      ← LinearEquiv.map_smul, SetLike.mk_smul_mk]
    abel_nf
    simp
  invFun v := CanonicalHomogenization.lift hom.ofPoint v
  left_inv x := by simp [CanonicalHomogenization.lift]
  right_inv v := by
    obtain ⟨v, rfl⟩ := Quotient.exists_rep v
    rcases v with ⟨v, c, p⟩ | v <;> apply Quotient.sound
    · have : hom.weight (lift hom.ofPoint ⟦.mk v c p⟧) = c := by
        simp [lift, lift.aux, weight_zero, weight_one]
      simp only [this, LinearEquiv.invFun_eq_symm]
      refine Equiv.mk_mk (hom.linear_inj ?_)
      simp [smul_sub, lift, lift.aux]
      abel
    · have : (LinearEquiv.ofInjective _ hom.linear_inj).symm ⟨_, Set.mem_range_self v⟩ = v :=
        (LinearEquiv.symm_apply_eq (LinearEquiv.ofInjective ofPoint.linear hom.linear_inj)).mpr rfl
      simpa [lift, lift.aux, weight_zero, this] using Equiv.mk_ofVector

theorem canonEquiv_canonical_ofPoint :
    hom.canonEquiv ∘ hom.ofPoint = CanonicalHomogenization.ofPoint := by
  ext x
  simp only [canonEquiv, LinearEquiv.invFun_eq_symm, LinearEquiv.coe_mk, LinearMap.coe_mk,
    AddHom.coe_mk, comp_apply, weight_one, one_smul]
  apply Quotient.sound ∘ HomogenizationExpr.Equiv.mk_mk
  exact ((Equiv.ofInjective _ hom.linear_inj).injective (by simp))

theorem weight_canonEquiv : CanonicalHomogenization.weight ∘ hom.canonEquiv = hom.weight := by
  sorry

-- proving the universal property using the equiv
/-- A homogenization `W` of `A` satisfies the universal property that every affine map from `A` into
any vector space extends uniquely to a linear map from `W` to the vector space. -/
theorem extend (U : Type*) [AddCommGroup U] [Module R U]
    (f : A →ᵃ[R] U) :
    ∃! (F : W →ₗ[R] U), F ∘ hom.ofPoint = f := by
  obtain ⟨F, hF, uF⟩ := CanonicalHomogenization.extend U f
  use LinearMap.comp F hom.canonEquiv.toLinearMap
  simp only [← hom.canonEquiv_canonical_ofPoint] at hF
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, comp_assoc, hF, true_and]
  intro g hg
  have := uF (g ∘ₗ hom.canonEquiv.symm.toLinearMap) ?_
  · rw [← this, LinearMap.comp_assoc]
    simp
  · ext x
    simp [← hg, ← hom.canonEquiv_canonical_ofPoint]

theorem hom_ext {U : Type*} [AddCommGroup U] [Module R U] {f g : W →ₗ[R] U}
    (h : ∀ x, f (hom.ofPoint x) = g (hom.ofPoint x)) : f = g := by
  rw [← LinearMap.eqLocus_eq_top, eq_top_iff, ← span_range_ofPoint (A := A), Submodule.span_le]
  apply Set.range_subset_iff.mpr
  simpa

open AffineMap LinearEquiv in
/-- The linear equivalence between the underlying vector space and its embedding. -/
noncomputable def homLinearRangeEquiv : LinearEquiv (RingHom.id R) V hom.ofVector.range := {
  toFun v := ⟨hom.ofVector v, hom.ofVector.mem_range_self v⟩
  map_add' v w := by simp
  map_smul' r v := by simp
  invFun :=
    (ofInjective hom.ofVector (linear_injective_iff _ |>.mpr ofPoint_injective)).invFun
  left_inv :=
    (ofInjective hom.ofVector (linear_injective_iff _ |>.mpr ofPoint_injective)).left_inv
  right_inv v' := by simp
}

/-- The affine equivalence between the affine space space and its embedding. -/
public noncomputable def homRangeEquiv : AffineEquiv R A hom.ofPoint.range :=
  .ofBijective
    ⟨hom.ofPoint.rangeRestrict_injective_iff.mpr hom.ofPoint_injective, fun ⟨_, a, rfl⟩ => ⟨a, rfl⟩⟩

lemma apply_homRangeEquiv_symm (x : hom.ofPoint.range) :
    hom.ofPoint (homRangeEquiv.symm x) = x := by
  rw [← homRangeEquiv.right_inv x]
  congr; exact homRangeEquiv.symm_apply_apply _

end Homogenization

end Ring

section Field

variable {R : Type*} [Field R]
variable [LinearOrder R] [IsOrderedRing R]
variable {V : Type*} [AddCommGroup V] [Module R V]
variable {A : Type*} [AddTorsor V A]
variable {W : Type*} [AddCommGroup W] [Module R W]
variable [hom : Affine.Homogenization R A W]

namespace Homogenization

open Convexity

/-- If homogenizing a point `q` yields a positive combination of the homogenizations of two other
points, then `q` lies in the open segment between them. -/
theorem pos_combo_openSegment {r₁ r₂ t : R} {p₁ p₂ q : A}
    (h₁ : 0 < r₁) (h₂ : 0 < r₂) (hₜ : 0 < t)
    (h : r₁ • hom.ofPoint p₁ + r₂ • hom.ofPoint p₂ = t • hom.ofPoint q) :
    q ∈ Convexity.openSegment R p₁ p₂ := by
  have : r₁ + r₂ = t := by simpa [weight_one, map_add, map_smul] using congr_arg hom.weight h
  have : t⁻¹ • r₁ + t⁻¹ • r₂ = 1 := by
      simp_rw [← smul_add, smul_eq_mul, this, mul_comm, Field.mul_inv_cancel _ hₜ.ne.symm]
  use (t⁻¹ • r₁), (t⁻¹ • r₂), (smul_pos (by positivity) h₁), (smul_pos (by positivity) h₂), this
  apply hom.ofPoint_injective
  have : t⁻¹ • (r₁ • hom.ofPoint p₁ + r₂ • hom.ofPoint p₂) = hom.ofPoint q := by
    rw [h, smul_smul, inv_mul_cancel₀ (ne_of_gt hₜ), one_smul]
  simp [hom.ofPoint.isAffineMap.map_convexCombPair, convexCombPair_eq_sum, ← this, smul_smul]


end Homogenization

end Field

end Affine
