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

variable (W) in
/-- The homogenization cone of a convex set in an affine space. -/
def cone (P : ConvexSet R A) := PointedCone.hull R (hom.embed '' P)

-- TODO this urgently needs a better name
variable (A) in
def csection (C : PointedCone R W) := (PointedCone.convex C).preimage hom.inj

def homogenizationHom :
    OrderHom (ConvexSet R A) (PointedCone R W) where
  toFun P := cone W P
  monotone' _ _ PlQ := Submodule.span_mono <| Set.image_mono PlQ

theorem empty_homogenization : cone W (⟨∅, empty_convex _⟩ : ConvexSet R A) = ⊥ := by
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

open Pointwise Set ConvexSpace AffineMap PointedCone

lemma smul_pos_of_mem_cone {P : ConvexSet R A} {x : W} (h : x ∈ cone W P) (hx : x ≠ 0) :
    x ∈ Ioi (0 : R) • hom.embed '' P.carrier :=
  (mem_hull_iff_mem_pos_smul_of_convex_nonzero (convex_of_injective hom.inj P.convex) hx).mp h

lemma height_pos_of {x : W} {P : ConvexSet R A} (h : x ∈ cone W P) (hx : x ≠ 0) :
    0 < hom.height x := by
  obtain ⟨_, r0, ⟨_, ⟨_, _, hy⟩, hry⟩⟩ := smul_pos_of_mem_cone h hx
  apply congrArg hom.height at hy
  by_contra
  simp only [← hry, map_smul, ← hy, height_one, smul_eq_mul, mul_one] at this
  simp_all

lemma height_nonneg_of {x : W} {P : ConvexSet R A} (h : x ∈ cone W P) :
    0 ≤ hom.height x := by
  by_cases hx : x = 0
  · simp [hx]
  · exact (height_pos_of h hx).le

variable (W) in
lemma embed_mem_cone_iff_mem (x : A) (P : ConvexSet R A) :
  hom.embed x ∈ cone W P ↔ x ∈ P := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simpa using mem_span_of_mem (Set.mem_image_of_mem (hom.embed) h)⟩
  obtain ⟨_, _, h'⟩ := smul_pos_of_mem_cone (Set.mem_preimage.mpr h) (embed_ne_zero x)
  obtain ⟨_, ⟨_, _, hyy'⟩, hy'⟩ := Set.mem_smul_set.mp h'
  have := congrArg hom.height hy'
  simp [← hyy', height_one] at this
  simp only [this, Set.mem_image, one_smul, exists_eq_right] at h'
  obtain ⟨_, _, hxx'⟩ := h'
  simpa [← hom.inj hxx']

lemma csection_cone_eq_id (P : ConvexSet R A) : csection A (cone W P) = P := by
  ext x; exact embed_mem_cone_iff_mem _ _ _

theorem cone_salient {P : ConvexSet R A} : PointedCone.Salient (cone W P) := by
  simp [cone]
  -- use salient_of_pos_linearMap with hom.height and height_nonneg_of
  -- issue #33
  sorry

/-- If homogenizing a point `q` yields a positive combination of the homogenizations of two other
points, then `q` lies in the open segment between them. -/
theorem pos_combo_openSegment {r₁ r₂ t : R} {p₁ p₂ q : A}
    (h₁ : 0 < r₁) (h₂ : 0 < r₂) (hₜ : 0 < t)
    (h : r₁ • hom.embed p₁ + r₂ • hom.embed p₂ = t • hom.embed q) :
    q ∈ openSegment R p₁ p₂ := by
  have : r₁ + r₂ = t := by simpa [hom.height_one, map_add, map_smul] using congr_arg hom.height h
  have : t⁻¹ • r₁ + t⁻¹ • r₂ = 1 := by
      simp_rw [← smul_add, smul_eq_mul, this, mul_comm, Field.mul_inv_cancel _ hₜ.ne.symm]
  use (t⁻¹ • r₁), (t⁻¹ • r₂), (smul_pos (by positivity) h₁), (smul_pos (by positivity) h₂), this
  apply hom.inj
  have : t⁻¹ • (r₁ • hom.embed p₁ + r₂ • hom.embed p₂) = hom.embed q := by
    rw [h, smul_smul, inv_mul_cancel₀ (ne_of_gt hₜ), one_smul]
  simp [affineMap_convexComboPair_of_injective hom.inj, Affine.convexComboPair_eq_smul_add_smul,
    ← this, smul_smul]

section Faces

variable {P F : ConvexSet R A}

lemma cone_csection_face_eq_id {P : ConvexSet R A} (F : (cone W P).Face) :
    cone W (csection A (F : PointedCone R W)) = (F : PointedCone R W) := by
  by_cases hF : F = ⊥
  · simp [(F.bot_face cone_salient).mpr hF, cone, csection, Convex.preimage]
  · apply SetLike.ext'
    rw [eq_nonneg_smul_base (fun x hx ↦ height_pos_of (F.isFaceOf.le hx)) zero_lt_one, cone,
      PointedCone.hull_eq_smul]
    · simp only [csection, Convex.preimage, ConvexSet.coe_carrier, image_preimage_eq_inter_range,
        ← hom.embed_height]
      congr
    · refine image_nonempty.mpr ?_
      simp only [Set.Nonempty, csection, Convex.preimage, ConvexSet.coe_carrier, mem_preimage,
        SetLike.mem_coe, PointedCone.Face.mem_coe]
      rw [← F.bot_face cone_salient] at hF
      obtain ⟨y, hyF, hy0⟩ := exists_mem_ne_zero_of_ne_bot hF
      obtain ⟨y', hy'⟩ : (hom.height y)⁻¹ • y ∈ (hom.embed.range : Set W) := by
        simp [hom.embed_height, inv_mul_cancel₀ (height_pos_of (F.isFaceOf.le hyF) hy0).ne.symm]
      use y'
      simp only [hy']
      exact F.toPointedCone.smul_mem (inv_nonneg.mpr (height_nonneg_of (F.isFaceOf.le hyF))) hyF
    · exact hom.convex_of_injective hom.inj (csection _ _).convex
    · intro hF'; exact hF ((F.bot_face cone_salient).mp hF')

theorem homogenization_isFaceOf (he : F.IsFaceOf P) : (cone W F).IsFaceOf (cone W P) where
  le := (hom.homogenizationHom).monotone' he.subset
  mem_of_smul_add_mem := by
    intro v w a hv hw ha hvw
    by_cases hnf : F.carrier.Nonempty
    · have cF := convex_of_injective hom.inj F.convex
      apply (PointedCone.mem_hull_iff_of_convex (hnf.image _) cF _).mpr
      by_cases hv0 : v = 0
      · exact ⟨0, le_rfl, Set.mem_smul_set.mpr (by simpa [hv0] using hnf)⟩
      · by_cases hw0 : w = 0
        · subst hw0
          obtain ⟨r, hr, r', ⟨w, hw, _⟩, hra⟩ :=
            smul_pos_of_mem_cone hvw (by simpa using smul_ne_zero ha.ne.symm hv0)
          simp only [add_zero] at ⊢ hra
          use a⁻¹ • r, (smul_pos (inv_pos.mpr ha) hr).le, r'
          constructor
          · use w, hw
          simp only
          rw [smul_assoc, hra, ← smul_assoc, smul_eq_mul, inv_mul_cancel₀ ha.ne.symm, one_smul]
        · obtain ⟨rw, rw0, q, ⟨q', qq, rfl⟩, _, _⟩ := smul_pos_of_mem_cone hw hw0
          obtain ⟨rv, rv0, _, ⟨p', pp, rfl⟩, _, _⟩ := smul_pos_of_mem_cone hv hv0
          have : a • (rv • hom.embed p') + (rw • hom.embed q') ≠ 0 := by
            intro hc
            have := cone_salient _ hw (smul_ne_zero rw0.ne.symm (embed_ne_zero q'))
            rw [add_eq_zero_iff_neg_eq'.mp hc] at this
            exact this <| PointedCone.smul_mem _ ha.le hv
          obtain ⟨_, rvw0, _, ⟨_, qqp, rfl⟩, pdp⟩ := smul_pos_of_mem_cone hvw this
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

variable (A) in
theorem csection_isFaceOf {F C : PointedCone R W} (hf : F.IsFaceOf C) :
    (csection A F).IsFaceOf (csection A C) where
  subset := preimage_mono hf.le
  left_mem_of_mem_openSegment  := by
    rintro x hx y hy z hz ⟨a, b, ha, hb, hab, hzo⟩
    refine hf.mem_of_smul_add_mem hx (C.smul_mem hb.le hy) ha ?_
    rwa [← convexComboPair_eq_smul_add_smul ha.le hb.le hab,
      ← affineMap_convexComboPair_of_injective hom.inj, hzo]

def Face.homogenizationIso : OrderIso P.Face (cone W P).Face where
  toFun F := ⟨_, hom.homogenization_isFaceOf F.isFaceOf⟩
  invFun F := ⟨_, by simpa [csection_cone_eq_id] using csection_isFaceOf A F.isFaceOf⟩
  map_rel_iff' := by
    intro a b
    refine ⟨fun h x xm ↦ ?_, fun h _ xm ↦ span_mono (image_mono h) xm⟩
    refine (embed_mem_cone_iff_mem W x b.toConvexSet).mp (h ?_)
    exact (embed_mem_cone_iff_mem W x a.toConvexSet).mpr xm
  left_inv a := by simp [csection_cone_eq_id]
  right_inv a := by simp [cone_csection_face_eq_id a]

end Faces

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
