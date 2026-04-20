import Polyhedral.Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.Geometry.Convex.Cone.Pointed
import Polyhedral.Mathlib.LinearAlgebra.ConvexSpace
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Face.Lattice

open Function Submodule

namespace Affine

section Ring

variable {R : Type*} [Ring R]
variable {V : Type*} [AddCommGroup V] [Module R V]
variable {A : Type*} [AddTorsor V A]
variable {W : Type*} [AddCommGroup W] [Module R W]

variable (R A W) in
/-- An embedding of an affine space `A` into a vector space `W` s.t. the image of `A` is exactly the
height-1 hyperplane under a given linear height map. -/
class Homogenization extends embed : A →ᵃ[R] W where
  inj : embed.toFun.Injective
  height : W →ₗ[R] R
  embed_height : embed.range = height ⁻¹' {1}
  extend (U : Type*) [AddCommGroup U] [Module R U] (f : A →ᵃ[R] U) :
    ∃! (F : W →ₗ[R] U), F ∘ embed = f

namespace Homogenization

variable [hom : Homogenization R A W]

/-- Embedding the underlying vector space is exactly the height-0 hyperplane. -/
theorem embed_linear_range_eq_height_ker : hom.linear.range = hom.height.ker := by
  ext x
  let a₀ := Classical.arbitrary A
  simp only [LinearMap.mem_range, LinearMap.mem_ker]
  have : (∃ y, hom.linear y = x) ↔ ∃ a b : A, embed.linear (a -ᵥ b) = x :=
    ⟨fun ⟨y, hy⟩ => ⟨y +ᵥ a₀, a₀, by simp [vadd_vsub, hy]⟩, fun ⟨a, b, hab⟩ => ⟨a -ᵥ b, hab⟩⟩
  rw [this]
  have hh := Set.ext_iff.mp hom.embed_height
  constructor
  · rintro ⟨a, b, hab⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hh
    simp [← hab, map_sub, (hh (embed b)).mp ⟨b, rfl⟩, (hh (embed a)).mp ⟨a, rfl⟩]
  · intro h
    have ha := Set.mem_preimage.mp <| (hh (hom.embed a₀)).mp (by simp)
    obtain ⟨b, hb⟩ : x + hom.embed a₀ ∈ (hom.embed.range : Set W) := by
      simpa [hom.embed_height, Set.mem_preimage, map_add, h]
    exact ⟨b, a₀, by simp [AffineMap.linearMap_vsub, hb]⟩

/-- The homogenization of a point in `A` has height 1. -/
lemma height_one (a₀ : A) : hom.height (hom.embed a₀) = 1 := by
    convert Set.ext_iff.mp hom.embed_height (hom.embed a₀)
    simp [SetLike.mem_coe, AffineMap.mem_range, exists_apply_eq_apply, Set.mem_preimage,
      Set.mem_singleton_iff, true_iff]

variable [Nontrivial R] in
theorem embed_ne_zero (x : A) : hom.embed x ≠ (0 : W) := by
  intro hn
  have := congrArg hom.height hn
  simp [height_one x] at this

/-- The homogenization of a point in `V` has height 0. -/
lemma height_zero (v : V) : hom.height (hom.linear v) = 0 := by
    simp [LinearMap.mem_ker.mp, ← embed_linear_range_eq_height_ker]

-- projecting x to height 0 along a₀ gives sth in the span of image of embed
lemma hlin (x : W) (a₀ : A) :
    x - hom.height x • hom.embed a₀ ∈ Submodule.span R hom.embed.range := by
  obtain ⟨v, hv⟩ : x - hom.height x • hom.embed a₀ ∈ hom.linear.range := by
    simp [embed_linear_range_eq_height_ker, height_one a₀]
  have : hom.linear v = hom.embed (v +ᵥ a₀) - hom.embed a₀ := by simp
  rw [← hv, this]
  apply Submodule.sub_mem <;> apply Submodule.subset_span
  · exact ⟨v +ᵥ a₀, rfl⟩
  · exact ⟨a₀, rfl⟩

theorem embed_range_isSpanning : span R (hom.embed.range : Set W) = ⊤ := by
  refine eq_top_iff'.mpr (fun x ↦ ?_)
  let a₀ := Classical.arbitrary A
  simpa using
    Submodule.add_mem _ (hlin x a₀) <| smul_mem _ (hom.height x) (subset_span ⟨a₀, rfl⟩)

section HomCone

variable [PartialOrder R] [IsStrictOrderedRing R]

open ConvexSpace

variable (R W)
def cone (P : ConvexSpace.ConvexSet R A) := PointedCone.hull R (hom.embed '' P)

def homogenizationHom :
    OrderHom (ConvexSet R A) (PointedCone R W) where
  toFun P := cone R W P
  monotone' _ _ PlQ := Submodule.span_mono <| Set.image_mono PlQ

theorem empty_homogenization : cone R W (⟨∅, empty_convex _⟩ : ConvexSet R A) = ⊥ := by
  simp [cone, SetLike.coe]

end HomCone

end Homogenization

end Ring

section Field

variable {R A : Type*}
variable [LinearOrder R] [Field R] [IsStrictOrderedRing R]
variable {W : Type*} [AddCommGroup W] [Module R W]
variable {V : Type*} [AddCommGroup V] [Module R V]
variable [AddTorsor V A]
variable [hom : Affine.Homogenization R A W]

namespace Homogenization

open ConvexSpace

theorem cone_salient {P : ConvexSet R A} : PointedCone.Salient (cone R W P) := by
  simp [cone]
  -- use salient_of_pos_linearMap with hom.height
  -- issue #33
  sorry

/-- If homogenizing a point `q` yields a positive combination of the homogenizations of two other
points, then `q` lies in the open segment between them. -/
theorem pos_combo_openSegment {r₁ r₂ t : R} {p₁ p₂ q : A}
    (h₁ : 0 < r₁) (h₂ : 0 < r₂) (hₜ : 0 < t)
    (h : r₁ • hom.embed p₁ + r₂ • hom.embed p₂ = t • hom.embed q) :
    q ∈ ConvexSpace.openSegment R p₁ p₂ := by
  have : r₁ + r₂ = t := by simpa [hom.height_one, map_add, map_smul] using congr_arg hom.height h
  have : t⁻¹ • r₁ + t⁻¹ • r₂ = 1 := by
      simp_rw [← smul_add, smul_eq_mul, this, mul_comm, Field.mul_inv_cancel _ hₜ.ne.symm]
  use (t⁻¹ • r₁), (t⁻¹ • r₂), (smul_pos (by positivity) h₁), (smul_pos (by positivity) h₂), this
  apply hom.inj
  have : t⁻¹ • (r₁ • hom.embed p₁ + r₂ • hom.embed p₂) = hom.embed q := by
    rw [h, smul_smul, inv_mul_cancel₀ (ne_of_gt hₜ), one_smul]
  simp [affineMap_convexComboPair _ hom.inj, Affine.convexComboPair_eq_smul_add_smul, ← this,
    smul_smul]

open Set Pointwise ConvexSpace PointedCone

variable {P F : ConvexSet R A}

open AffineMap in
theorem homogenization_isFaceOf (he : F.IsFaceOf P) :
    (cone R W F).IsFaceOf (cone R W P) where
  le := (hom.homogenizationHom).monotone' he.subset
  mem_of_smul_add_mem := by
    intro v w a hv hw ha hvw
    by_cases hnf : F.carrier.Nonempty
    · have cF := convex_of_injective hom.inj F.convex
      apply (mem_hull_of_convex (hnf.image _) cF).mpr
      by_cases hv0 : v = 0
      · exact ⟨0, le_rfl, Set.mem_smul_set.mpr (by simpa [hv0] using hnf)⟩
      · by_cases hw0 : w = 0
        · obtain ⟨r', _, _, ⟨r, ⟨hr, hrm⟩⟩, hra⟩ :=
            (mem_hull_of_convex (hnf.image _) (convex_of_injective hom.inj F.convex)).mp hvw
          simp only [hw0, add_zero, mem_smul_set, mem_image, exists_exists_and_eq_and] at ⊢ hra
          use a⁻¹ • r', smul_nonneg (by positivity) (by positivity), r, hr
          rw [hrm, smul_assoc, hra, ← smul_assoc, smul_eq_mul, inv_mul_cancel₀ ha.ne.symm, one_smul]
        · have hnp := (hnf.image hom.embed).mono (image_mono he.subset)
          have cP := convex_of_injective hom.inj P.convex
          obtain ⟨rw, rw0, q, ⟨q', qq, rfl⟩, _, _⟩ := smul_pos_of_mem_hull hnp cP hw hw0
          obtain ⟨rv, rv0, _, ⟨p', pp, rfl⟩, _, _⟩ := smul_pos_of_mem_hull hnp cP hv hv0
          have : a • (rv • hom.embed p') + (rw • hom.embed q') ≠ 0 := by
            have := cone_salient _ hw (smul_ne_zero rw0.ne.symm (embed_ne_zero q'))
            intro hc
            rw [add_eq_zero_iff_neg_eq'.mp hc] at this
            exact this <| PointedCone.smul_mem _ ha.le hv
          obtain ⟨_, rvw0, _, ⟨_, qqp, rfl⟩, pdp⟩ := smul_pos_of_mem_hull (hnf.image _) cF hvw this
          have := he.left_mem_of_mem_openSegment pp qq qqp ?_
          · refine ⟨rv, rv0.le, smul_mem_smul_set <| mem_image_of_mem embed this⟩
          rw [← smul_assoc _ rv] at pdp
          exact pos_combo_openSegment (smul_pos ha rv0) rw0 rvw0 pdp.symm
    · have := not_nonempty_iff_eq_empty.mp hnf
      simp_all only [cone, SetLike.coe, image_empty, span_empty, mem_bot]
      by_contra hxx
      apply cone_salient (R := R) (A := A) _ hv hxx
      have : -v = a⁻¹ • w := by
        simp [← neg_eq_of_add_eq_zero_right hvw, smul_neg, smul_smul, inv_mul_cancel₀ (ne_of_gt ha)]
      rw [this]
      exact PointedCone.smul_mem _ (by positivity) hw

def Face.homogenizationIso : OrderIso P.Face (cone R W P).Face where
  toFun F := ⟨_, hom.homogenization_isFaceOf F.isFaceOf⟩
  invFun F := by sorry
  map_rel_iff' := by sorry
  left_inv := sorry
  right_inv := sorry
  -- monotone' _ _ h := Submodule.span_mono (Set.image_mono h)

end Homogenization

end Field

#exit

section DivisionRing

variable {R : Type*} [DivisionRing R]
variable {V : Type*} [AddCommGroup V] [Module R V]
variable {A : Type*} [AddTorsor V A]
variable {W : Type*} [AddCommGroup W] [Module R W]
variable {U : Type*} [AddCommGroup U] [Module R U]
variable [hom : Homogenization R A W]
variable [hom' : Homogenization R A U]

variable [FiniteDimensional R W] in
noncomputable def Homogenization.uniqueUpToIso : W ≃ U where
  toFun := (hom.extend U hom'.embed).choose -- would be nice to construct
  invFun := (hom'.extend W hom.embed).choose
  left_inv w := sorry
  right_inv u := sorry

end DivisionRing

section Field

variable {R : Type*} [Field R] [PartialOrder R] [IsStrictOrderedRing R]
variable {V : Type*} [AddCommGroup V] [Module R V]
variable {A : Type*} [AddTorsor V A]
variable {W : Type*} [AddCommGroup W] [Module R W]

variable (R A) in
/-- Evaluation map -/
def eval : A →ᵃ[R] ((A →ᵃ[R] R) →ₗ[R] R) where
  toFun a := { toFun f := f a, map_add' _ _ := rfl, map_smul' _ _ := rfl }
  linear :=
    { toFun v := { toFun f := f.linear v, map_add' _ _ := rfl, map_smul' _ _ := rfl }
      map_add' := fun v w => by ext f; simp [map_add]
      map_smul' := fun c v => by ext f; simp [map_smul] }
  map_vadd' _ _ := by ext f; simp [AffineMap.map_vadd]

lemma zero_not_mem_eval_range : 0 ∉ (eval R A).range := by
  intro h
  obtain ⟨x, hx⟩ := h
  simp only [eval, AffineMap.coe_mk, LinearMap.ext_iff, LinearMap.coe_mk,
    AddHom.coe_mk, LinearMap.zero_apply] at hx
  exact absurd (hx (AffineMap.const R A 1)) one_ne_zero

-- abbrev AffineSubspace.Homogenization_of_zero_not_mem {A : AffineSubspace R V} [Nonempty A]
--     (h : 0 ∉ A) : Homogenization R A (span R (A : Set V)) where
--   embed := { toFun := fun a => ⟨a, Submodule.mem_span_of_mem a.2⟩,
--              linear := sorry
--             }
--   ne_zero := sorry
--   span_top := sorry

variable (R A) in
abbrev canonicalHomogenization := (A →ᵃ[R] R) →ₗ[R] R

-- variable (R A) in
-- def canonicalHomogenization := span R ((eval R A).range : Set ((A →ᵃ[R] R) →ₗ[R] R))
lemma eval_range : AffineMap.range (eval R A) = hom.height ⁻¹' {1} := by
  ext φ
  simp only [Set.mem_range, Set.mem_preimage, Set.mem_singleton_iff, height]
  constructor
  · rintro ⟨a, rfl⟩
    simp [eval, AffineMap.const]
  · intro hφ
    refine ⟨b.affineCombination R (fun i => φ (b.coord i)), ?_⟩
    ext f
    have hf : f = b.affineCombination R (fun i => f (b i)) := by
      exact (b.affineCombination_coord f).symm
    conv_lhs => rw [hf]
    simp [eval, AffineBasis.affineCombination, LinearMap.map_sum,
          LinearMap.map_smul, hφ]

instance canonicalHomogenization_Homogenization :
    Homogenization R A (canonicalHomogenization R A) where
  embed := eval R A
  inj a₁ a₂ h := by simp [eval] at h; have := funext_iff.mp h
  height := { toFun x := x (AffineMap.const R A 1)
              map_add' a b := rfl
              map_smul' s a := rfl }
  embed_height := by
    ext φ
    simp [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · rintro ⟨a, rfl⟩
      simp [eval, AffineMap.const]
    · intro hφ
      -- pick a basis
      obtain ⟨ι, b, _⟩ := AffineBasis.exists_affineBasis R V A
      -- make the affine combo of the image of the basis
      refine ⟨Finset.univ.affineCombination R b (fun i => φ (b.coord i)), ?_⟩
      ext f
      have hf : f = b.affineCombination R (fun i => f (b i)) := by
        exact (b.affineCombination_coord f).symm
      conv_lhs => rw [hf]
      simp [eval, AffineBasis.affineCombination, LinearMap.map_sum,
            LinearMap.map_smul, hφ]

      use Classical.arbitrary A
      ext g
      simp
      sorry
  extend := sorry

end Field

-- section DivisionRing

-- variable {R : Type*} [DivisionRing R]
-- variable {V : Type*} [AddCommGroup V] [Module R V]
-- variable {A : Type*} [AddTorsor V A]
-- variable {W : Type*} [AddCommGroup W] [Module R W]
-- variable (hom : Homogenization R A W)

-- def projectivizationEquiv : Projectivization R V ≃ Set.range hom.toAffineMap where
--   toFun := sorry
--   invFun := sorry
--   left_inv := sorry
--   right_inv := sorry

-- end DivisionRing
