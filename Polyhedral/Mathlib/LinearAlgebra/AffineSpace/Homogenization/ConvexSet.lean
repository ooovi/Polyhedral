import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Convexity
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Face.Lattice
import Polyhedral.Mathlib.LinearAlgebra.AffineSpace.Homogenization.Basic

namespace Affine.Homogenization

section Ring

open Convexity

variable {R : Type*} [Ring R]
variable [PartialOrder R] [IsStrictOrderedRing R]
variable {V : Type*} [AddCommGroup V] [Module R V]
variable {A : Type*} [AddTorsor V A]
variable {W : Type*} [AddCommGroup W] [Module R W]
variable [hom : Affine.Homogenization R A W]
variable [IsModuleConvexSpace R W]

variable (W) in
/-- The homogenization cone of a convex set in an affine space. -/
def homogenize (P : ConvexSet R A) := PointedCone.hull R (hom.ofPoint '' P)

lemma homogenize_bot_eq_bot : homogenize W (⊥ : ConvexSet R A) = ⊥ := by
  simp [homogenize, Bot.bot]

def homogenizationHom :
    OrderHom (ConvexSet R A) (PointedCone R W) where
  toFun P := homogenize W P
  monotone' _ _ PlQ := Submodule.span_mono <| Set.image_mono PlQ

theorem homogenize_empty_eq_bot : homogenize W (⟨∅, IsConvexSet.empty⟩ : ConvexSet R A) = ⊥ := by
  simp [homogenize, SetLike.coe]

variable (A) in
def dehomogenize (C : PointedCone R W) : ConvexSet R A :=
  ⟨_, C.isConvexSet.preimage hom.ofPoint.isAffineMap⟩

lemma ofPoint_dehomogenize_eq_inter_ofPoint (C : PointedCone R W) :
    hom.ofPoint '' (dehomogenize A C) = (C : Set W) ∩ hom.ofPoint.range := by
  ext x
  simp only [dehomogenize, Set.mem_image, SetLike.mem_coe, Set.mem_inter_iff,
    AffineMap.mem_range]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨hy, by use y⟩
  · rintro ⟨hxC, y, rfl⟩
    use y
    simpa

end Ring

section Field

open Pointwise Set Convexity PointedCone Submodule

variable {R : Type*} [Field R]
variable [LinearOrder R] [IsOrderedRing R]
variable {V : Type*} [AddCommGroup V] [Module R V]
variable {A : Type*} [AddTorsor V A]
variable {W : Type*} [AddCommGroup W] [Module R W]
variable [hom : Affine.Homogenization R A W]
variable [IsModuleConvexSpace R W]

theorem homogenize_salient {P : ConvexSet R A} : PointedCone.Salient (homogenize W P) := by
  simp [homogenize]
  -- use salient_of_pos_linearMap with hom.weight and weight_nonneg_of_mem_homogenize
  -- issue #33
  sorry

lemma smul_pos_of_mem_homogenize {P : ConvexSet R A} {x} (h : x ∈ homogenize W P) (hx : x ≠ 0) :
    x ∈ Ioi (0 : R) • hom.ofPoint '' (P : Set A) :=
  (mem_hull_iff_mem_pos_smul_of_convex_nonzero (P.isConvexSet.image ofPoint.isAffineMap) hx).mp h

lemma weight_pos_of_mem_homogenize {x} {P : ConvexSet R A} (h : x ∈ homogenize W P) (hx : x ≠ 0) :
    0 < hom.weight x := by
  obtain ⟨_, r0, ⟨_, ⟨_, _, hy⟩, hry⟩⟩ := smul_pos_of_mem_homogenize h hx
  apply congrArg hom.weight at hy
  by_contra
  simp only [← hry, map_smul, ← hy, weight_one, smul_eq_mul, mul_one] at this
  simp_all

lemma weight_nonneg_of_mem_homogenize {x : W} {P : ConvexSet R A} (h : x ∈ homogenize W P) :
    0 ≤ hom.weight x := by
  by_cases hx : x = 0
  · simp [hx]
  · exact (weight_pos_of_mem_homogenize h hx).le

variable (W) in
lemma ofPoint_mem_homogenize_iff_mem (x : A) (P : ConvexSet R A) :
  hom.ofPoint x ∈ homogenize W P ↔ x ∈ P := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simpa using mem_span_of_mem (Set.mem_image_of_mem ofPoint h)⟩
  obtain ⟨_, _, h'⟩ := smul_pos_of_mem_homogenize (Set.mem_preimage.mpr h) (ofPoint_ne_zero x)
  obtain ⟨_, ⟨_, _, hyy'⟩, hy'⟩ := Set.mem_smul_set.mp h'
  have := congrArg hom.weight hy'
  simp [← hyy', weight_one] at this
  simp only [this, Set.mem_image, one_smul, exists_eq_right] at h'
  obtain ⟨_, _, hxx'⟩ := h'
  simpa [← hom.ofPoint_injective hxx']

/-- Dehomogenizing the homogenization of a convex set yields the same set again. -/
theorem dehomogenize_homogenize_eq_id (P : ConvexSet R A) :
    dehomogenize A (homogenize W P) = P := by
  ext x; exact ofPoint_mem_homogenize_iff_mem _ _ _

/-- If the entire cone save the origin are at positive weight, homogenizing the dehomogenization
of the homogenize yields the cone again. -/
theorem homogenize_dehomogenize_eq_id_of_pos {C : PointedCone R W}
    (hC : ∀ x ∈ C, x ≠ 0 → 0 < hom.weight x) :
    homogenize W (dehomogenize A C) = (C : PointedCone R W) := by
  by_cases hbot : C = ⊥
  · simp [hbot, homogenize, dehomogenize]
  · apply SetLike.ext'
    unfold homogenize
    rw [eq_Ici_zero_smul_inter_preimage_of_pos_of_ne_bot hC zero_lt_one hbot,
      ofPoint_dehomogenize_eq_inter_ofPoint, ← hom.ofPoint_range_eq_preimage_weight_one]
    convert hull_eq_smul ?_ (C.isConvexSet.inter hom.ofPoint.range_isConvexSet)
    · obtain ⟨y, hyC, hy0⟩ := exists_mem_ne_zero_of_ne_bot hbot
      obtain ⟨_, hy'⟩ : (hom.weight y)⁻¹ • y ∈ (hom.ofPoint.range : Set W) := by
        simpa [ofPoint_range_eq_preimage_weight_one] using inv_mul_cancel₀ (hC y hyC hy0).ne.symm
      use (hom.weight y)⁻¹ • y, C.smul_mem (inv_nonneg.mpr (hC y hyC hy0).le) hyC
      simp [← hy']

section Faces

theorem homogenize_isFaceOf {F P : ConvexSet R A} (he : F.IsFaceOf P) :
    (homogenize W F).IsFaceOf (homogenize W P) where
  le := (hom.homogenizationHom).monotone' he.subset
  mem_of_smul_add_mem := by
    intro v w a hv hw ha hvw
    by_cases hnf : (F : Set A).Nonempty
    · have cF := F.isConvexSet.image hom.ofPoint.isAffineMap
      apply (mem_hull_iff_of_convex (hnf.image _) cF _).mpr
      by_cases hv0 : v = 0
      · exact ⟨0, le_rfl, Set.mem_smul_set.mpr (by simpa [hv0] using hnf)⟩
      · by_cases hw0 : w = 0
        · subst hw0
          obtain ⟨r, hr, r', ⟨w, hw, _⟩, hra⟩ :=
            smul_pos_of_mem_homogenize hvw (by simpa using smul_ne_zero ha.ne.symm hv0)
          simp only [add_zero] at ⊢ hra
          use a⁻¹ • r, (smul_pos (inv_pos.mpr ha) hr).le, r'
          constructor
          · use w, hw
          simp only
          rw [smul_assoc, hra, ← smul_assoc, smul_eq_mul, inv_mul_cancel₀ ha.ne.symm, one_smul]
        · obtain ⟨rw, rw0, q, ⟨q', qq, rfl⟩, _, _⟩ := smul_pos_of_mem_homogenize hw hw0
          obtain ⟨rv, rv0, _, ⟨p', pp, rfl⟩, _, _⟩ := smul_pos_of_mem_homogenize hv hv0
          have : a • (rv • hom.ofPoint p') + (rw • hom.ofPoint q') ≠ 0 := by
            intro hc
            have := homogenize_salient _ hw (smul_ne_zero rw0.ne.symm (ofPoint_ne_zero q'))
            rw [add_eq_zero_iff_neg_eq'.mp hc] at this
            exact this <| PointedCone.smul_mem _ ha.le hv
          obtain ⟨_, rvw0, _, ⟨_, qqp, rfl⟩, pdp⟩ := smul_pos_of_mem_homogenize hvw this
          have := he.left_mem_of_mem_openSegment pp qq qqp ?_
          · refine ⟨rv, rv0.le, smul_mem_smul_set <| mem_image_of_mem ofPoint this⟩
          rw [← smul_assoc _ rv] at pdp
          exact pos_combo_openSegment (smul_pos ha rv0) rw0 rvw0 pdp.symm
    · have := not_nonempty_iff_eq_empty.mp hnf
      simp_all only [homogenize, SetLike.coe, image_empty, span_empty, mem_bot]
      by_contra hxx
      apply homogenize_salient _ hv hxx
      have : -v = a⁻¹ • w := by
        simp [← neg_eq_of_add_eq_zero_right hvw, smul_neg, smul_smul, inv_mul_cancel₀ (ne_of_gt ha)]
      rw [this]
      exact PointedCone.smul_mem _ (by positivity) hw

variable (A) in
theorem dehomogenize_isFaceOf {F C : PointedCone R W} (hf : F.IsFaceOf C) :
    (dehomogenize A F).IsFaceOf (dehomogenize A C) where
  subset := preimage_mono (fun _ x ↦ hf.le x)
  left_mem_of_mem_openSegment  := by
    rintro x hx y hy z hz ⟨a, b, ha, hb, hab, hzo⟩
    refine hf.mem_of_smul_add_mem hx (C.smul_mem hb.le hy) ha ?_
    rwa [← convexCombPair_eq_sum _ _ ha.le hb.le hab,
      ← hom.ofPoint.isAffineMap.map_convexCombPair, hzo]

def Face.homogenizationIso {P : ConvexSet R A} : OrderIso P.Face (homogenize W P).Face where
  toFun F := ⟨_, hom.homogenize_isFaceOf F.isFaceOf⟩
  invFun F := ⟨_, by simpa [dehomogenize_homogenize_eq_id] using dehomogenize_isFaceOf A F.isFaceOf⟩
  map_rel_iff' := by
    intro a b
    refine ⟨fun h x xm ↦ ?_, fun h _ xm ↦ span_mono (image_mono h) xm⟩
    refine (ofPoint_mem_homogenize_iff_mem W x b.toConvexSet).mp (h ?_)
    exact (ofPoint_mem_homogenize_iff_mem W x a.toConvexSet).mpr xm
  left_inv _ := by simp [dehomogenize_homogenize_eq_id]
  right_inv F := by
    have := homogenize_dehomogenize_eq_id_of_pos
      (fun _ h n ↦ weight_pos_of_mem_homogenize (F.isFaceOf.le h) n)
    simp [this]

end Faces

end Affine.Homogenization.Field
