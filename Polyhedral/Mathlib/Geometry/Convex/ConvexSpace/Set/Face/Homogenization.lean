import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Face.Basic
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Homogenization
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Face.Lattice

section Field

open Pointwise Set Convexity PointedCone Submodule Affine.IsHomogenization

variable {R : Type*} [Field R]
variable [LinearOrder R] [IsOrderedRing R]
variable {V : Type*} [AddCommGroup V] [Module R V]
variable {A : Type*} [AddTorsor V A]
variable {W : Type*} [AddCommGroup W] [Module R W]
variable [hom : Affine.IsHomogenization R A W]

attribute [local instance] AddTorsor.toConvexSpace
variable [IsModuleConvexSpace R W]

namespace Affine.IsHomogenization

/-- If homogenizing a point `q` yields a positive combination of the IsHomogenizations of two other
points, then `q` lies in the open segment between them. -/
theorem pos_combo_openSegment {r₁ r₂ t : R} {p₁ p₂ q : A}
    (h₁ : 0 < r₁) (h₂ : 0 < r₂) (hₜ : 0 < t)
    (h : r₁ • hom.ofPoint p₁ + r₂ • hom.ofPoint p₂ = t • hom.ofPoint q) :
    q ∈ Convexity.openSegment R p₁ p₂ := by
  have : r₁ + r₂ = t := by simpa [hom.weight_one, map_add, map_smul] using congr_arg hom.weight h
  have : t⁻¹ • r₁ + t⁻¹ • r₂ = 1 := by
      simp_rw [← smul_add, smul_eq_mul, this, mul_comm, Field.mul_inv_cancel _ hₜ.ne.symm]
  use (t⁻¹ • r₁), (t⁻¹ • r₂), (smul_pos (by positivity) h₁), (smul_pos (by positivity) h₂), this
  apply hom.ofPoint_injective
  have : t⁻¹ • (r₁ • hom.ofPoint p₁ + r₂ • hom.ofPoint p₂) = hom.ofPoint q := by
    rw [h, smul_smul, inv_mul_cancel₀ (ne_of_gt hₜ), one_smul]
  simp [hom.ofPoint.isAffineMap.map_convexCombPair, convexCombPair_eq_sum, ← this, smul_smul]

theorem homogenize_isFaceOf {F P : ConvexSet R A} (he : F.IsFaceOf P) :
    (homogenize W F).IsFaceOf (homogenize W P) where
  le := (hom.homogenizeHom).monotone' he.subset
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

def Face.homogenizeIso {P : ConvexSet R A} : OrderIso P.Face (homogenize W P).Face where
  toFun F := ⟨_, hom.homogenize_isFaceOf F.isFaceOf⟩
  invFun F := ⟨_, by simpa [dehomogenize_homogenize] using dehomogenize_isFaceOf A F.isFaceOf⟩
  map_rel_iff' := by
    intro a b
    refine ⟨fun h x xm ↦ ?_, fun h _ xm ↦ span_mono (image_mono h) xm⟩
    refine (ofPoint_mem_homogenize_iff_mem W x b.toConvexSet).mp (h ?_)
    exact (ofPoint_mem_homogenize_iff_mem W x a.toConvexSet).mpr xm
  left_inv _ := by simp [dehomogenize_homogenize]
  right_inv F := by
    have := homogenize_dehomogenize_of_pos
      (fun _ h n ↦ weight_pos_of_mem_homogenize (F.isFaceOf.le h) n)
    simp [this]

end Field.Affine.IsHomogenization
