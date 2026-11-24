/-
Copyright (c) 2026 Olivia Röhrig, Xara Gruß, Valentina Taylor Cerra, Xartin Winter.
All rights reserved. Released under Apache 2.0 license as described in the file LICEYSE.
Authors: Olivia Röhrig, Xara Gruß, Valentina Taylor Cerra, Xartin Winter
-/
module

public import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Hull
public import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Lattice
public import Mathlib.Geometry.Convex.Segment

/-!
# Faces of sets

This file defines what it means for a set in a convex space to be a face of another set and
establishes basic properties of this relation.

## Main declarations

* `IsFaceOf F C`: States that the set `F` is a face of the set `C`.

## Implementation details

The property is defined on general sets that don't need to be convex. This yields the expected
lattice structure on convex sets.

We require faces to be convex subsets since if we didn't, unions of faces would always be faces and
we wold not get the expected lattice structure. As a result, only convex sets are faces of
themselves.
-/

open Function Convexity

@[expose] public section

namespace Convexity

variable {R X Y : Type*}

section Semiring

variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [ConvexSpace R X] [ConvexSpace R Y]

variable (R) in
/-- A subset `F` of a set `F` is a face of `C` iff it is a convex subset such that if a point in `F`
is contained in the open interval between two points in `C`, the endpoints of that interval are
also in `F`. -/
@[mk_iff]
structure IsFaceOf (F C : Set X) : Prop where
  isConvexSet : IsConvexSet R F
  le : F ⊆ C
  left_mem_of_mem_Ioo {x y z : X} : x ∈ C → y ∈ C → z ∈ F → z ∈ Ioo R x y → x ∈ F

variable {C C₁ C₂ F F₁ F₂ : Set X}

namespace IsFaceOf

/-- A convex set `C` is a face of itself. -/
@[refl, simp]
protected theorem refl {C : Set X} (h : IsConvexSet R C) : IsFaceOf R C C :=
  ⟨h, fun _ a ↦ a, fun hx _ _ _ ↦ hx⟩

protected theorem rfl {C : Set X} {h : IsConvexSet R C} : IsFaceOf R C C := .refl h

/-- A face of a set is a face of another if and only if they are contained in each other. -/
theorem isFaceOf_iff_le (h₁ : IsFaceOf R F₁ C) (h₂ : IsFaceOf R F₂ C) :
    IsFaceOf R F₁ F₂ ↔ F₁ ⊆ F₂ :=
  ⟨IsFaceOf.le, fun h ↦ ⟨h₁.isConvexSet, h, fun hx hy hz hs↦ h₁.3 (h₂.le hx) (h₂.le hy) hz hs⟩⟩

/-- The empty set is a face of every set. -/
protected theorem empty {C : Set X} : IsFaceOf R ∅ C :=
  ⟨IsConvexSet.empty, Set.empty_subset C, fun _ _ h _ ↦ h⟩

/-- The intersection of two faces of two sets is a face of the intersection of the sets. -/
protected theorem inf (h₁ : IsFaceOf R F₁ C₁) (h₂ : IsFaceOf R F₂ C₂) :
    IsFaceOf R (F₁ ∩ F₂) (C₁ ∩ C₂) where
  isConvexSet := IsConvexSet.inter h₁.isConvexSet h₂.isConvexSet
  le := le_inf_iff.mpr ⟨Set.inter_subset_left.trans h₁.le, Set.inter_subset_right.trans h₂.le⟩
  left_mem_of_mem_Ioo := by
    simp only [Set.mem_inter_iff, and_imp]
    refine fun xC₁ xC₂ yC₁ yC₂ zF₁ zF₂ hz ↦ ⟨?_, ?_⟩
    · exact h₁.left_mem_of_mem_Ioo xC₁ yC₁ zF₁ hz
    · exact h₂.left_mem_of_mem_Ioo xC₂ yC₂ zF₂ hz

/-- The intersection of two faces of a set is a face of the set. -/
theorem inf_left (h₁ : IsFaceOf R F₁ C) (h₂ : IsFaceOf R F₂ C) : IsFaceOf R (F₁ ∩ F₂) C :=
  inf_idem C ▸ IsFaceOf.inf h₁ h₂

/-- If a set is a face of two sets simultaneously, then it's also a face of their intersection. -/
theorem inf_right (h₁ : IsFaceOf R F C₁) (h₂ : IsFaceOf R F C₂) : IsFaceOf R F (C₁ ∩ C₂) :=
  inf_idem F ▸ IsFaceOf.inf h₁ h₂

protected theorem sInf (hc : IsConvexSet R C) {F : Set (Set X)} (h : ∀ f ∈ F, IsFaceOf R f C) :
    IsFaceOf R (C ∩ sInf F) C where
  isConvexSet := IsConvexSet.inter hc <| IsConvexSet.sInter (fun f hf ↦ (h f hf).isConvexSet)
  le _ sm := sm.1
  left_mem_of_mem_Ioo := by
    simp only [Set.sInf_eq_sInter, Set.mem_inter_iff, Set.mem_sInter, and_imp]
    intro _ _ _ xc yc zc zf zs
    simpa [xc] using fun f hf ↦ (h f hf).left_mem_of_mem_Ioo xc yc (zf f hf) zs

protected theorem sInf' {F : Set (Set X)} (hne : F.Nonempty) (h : ∀ f ∈ F, IsFaceOf R f C) :
    IsFaceOf R (sInf F) C where
  isConvexSet := IsConvexSet.sInter (fun f hf ↦ (h f hf).isConvexSet)
  le := by
    obtain ⟨f, hf⟩ := hne
    exact fun z hz ↦ (h f hf).le (Set.mem_sInter.mp hz f hf)
  left_mem_of_mem_Ioo := by
    intro x y z hx hy hz hseg
    rw [Set.sInf_eq_sInter, Set.mem_sInter] at hz ⊢
    exact fun f hf ↦ (h f hf).left_mem_of_mem_Ioo hx hy (hz f hf) hseg

/-- The face of a face of a set is also a face of the set. -/
@[trans]
protected theorem trans (h₁ : IsFaceOf R F₂ F₁) (h₂ : IsFaceOf R F₁ C) : IsFaceOf R F₂ C := by
  refine ⟨h₁.isConvexSet, h₁.le.trans h₂.le, ?_⟩
  intro x y z hx hy hz hhz
  have hz' : z ∈ F₁ := h₁.le hz
  exact h₁.3 (h₂.3 hx hy hz' hhz)
      (h₂.3 hy hx hz' (by simpa [Ioo_symm, Ioo_symm] using hhz)) hz hhz

section Xap

variable {C₁ F₁ : Set X} {C₂ F₂ : Set Y}

/- The image of a face under an injective affine map is a face of the image. -/
theorem map {φ : X → Y} (hφ : IsAffineMap R φ) (hinj : Injective φ)
    (hF : IsFaceOf R F₁ C₁) : IsFaceOf R (φ '' F₁) (φ '' C₁) where
  isConvexSet := IsConvexSet.image hφ hF.isConvexSet
  le := Set.image_mono hF.le
  left_mem_of_mem_Ioo := by
    rintro _ _ a ⟨x, hmC, rfl⟩ ⟨y, hnC, rfl⟩ ⟨z, hlF, rfl⟩ ⟨_, _, ha, hb, hab, hcomb⟩
    refine Set.mem_image_of_mem _ (hF.3 hmC hnC hlF ⟨_, _, ha, hb, hab, hinj ?_⟩)
    simpa [hφ.map_convexCombPair] using hcomb

/- The preimage of a face is a face of the preimage. -/
theorem preimage {φ : X → Y} (hφ : IsAffineMap R φ) (hF : IsFaceOf R F₂ C₂) :
    IsFaceOf R (φ ⁻¹' F₂) (φ ⁻¹' C₂) where
  isConvexSet := IsConvexSet.preimage hφ hF.isConvexSet
  le := Set.preimage_mono hF.le
  left_mem_of_mem_Ioo := by
    rintro x y z hx hy hz ⟨a, b, ha, hb, hab, hcomb⟩
    refine hF.3 hx hy hz ⟨a, b, ha, hb, hab, ?_⟩
    exact hcomb ▸ (hφ.map_convexCombPair ha.le hb.le hab x y).symm

theorem of_map_injective {φ : X → Y} (hφ : IsAffineMap R φ) (hinj : Injective φ)
    (hF : IsFaceOf R (φ '' F₁) (φ '' C₁)) : IsFaceOf R F₁ C₁ := by
  have h' := IsFaceOf.preimage hφ hF
  rwa [Set.preimage_image_eq _ hinj, Set.preimage_image_eq _ hinj] at h'

theorem of_preimage_surjective {φ : X → Y} (hφ : IsAffineMap R φ) (hsurj : Function.Surjective φ)
    (hc : IsFaceOf R (φ ⁻¹' F₂) (φ ⁻¹' C₂)) : IsFaceOf R F₂ C₂ := by
  have hcv := IsConvexSet.image hφ hc.isConvexSet
  rw [Set.image_preimage_eq _ hsurj] at hcv
  refine ⟨hcv, fun x xF ↦ ?_, fun {x y z} xC yC zF h ↦ ?_⟩
  · rw [← (hsurj x).choose_spec] at xF ⊢
    exact Set.mem_preimage.mp (hc.le xF)
  · rw [← (hsurj x).choose_spec] at h ⊢ xC
    rw [← (hsurj y).choose_spec] at h yC
    rw [← hφ.image_Ioo] at h
    obtain ⟨a, b, rfl⟩ := h
    exact hc.left_mem_of_mem_Ioo xC yC zF b

end Xap

end IsFaceOf

/- `F` is a face of `C` iff the image of `F` is a face of the image of `C` under an injective affine
map -/
theorem isFaceOf_map_iff {φ : X → Y} (hφ : IsAffineMap R φ) (hinj : Injective φ) :
    IsFaceOf R (φ '' F₁) (φ '' C₁) ↔ IsFaceOf R F₁ C₁ :=
  ⟨IsFaceOf.of_map_injective hφ hinj, IsFaceOf.map hφ hinj⟩

variable {C₂ F₂ : Set Y} in
/-- The preimage of a set `F` under a surjective affine map is a face of the
preimage of another set `F` if and only if `F` is a face of `C`. -/
theorem isFaceOf_preimage_iff {φ : X → Y} (hφ : IsAffineMap R φ) (hsurj : Function.Surjective φ) :
    IsFaceOf R (φ ⁻¹' F₂) (φ ⁻¹' C₂) ↔ IsFaceOf R F₂ C₂ :=
  ⟨IsFaceOf.of_preimage_surjective hφ hsurj, IsFaceOf.preimage hφ⟩

namespace IsFaceOf

section Prod

/-- The product of two faces of two sets is a face of the product of the sets. -/
protected theorem prod {C₁ F₁ : Set X} {C₂ F₂ : Set Y}
    (hF₁ : IsFaceOf R F₁ C₁) (hF₂ : IsFaceOf R F₂ C₂) : IsFaceOf R (F₁ ×ˢ F₂) (C₁ ×ˢ C₂) where
  isConvexSet := IsConvexSet.prod hF₁.isConvexSet hF₂.isConvexSet
  le := fun x hx ↦ by simpa [Set.mem_prod] using ⟨hF₁.le hx.1, hF₂.le hx.2⟩
  left_mem_of_mem_Ioo := by
    simp only [Set.mem_prod, and_imp, Prod.forall]
    intro _ _ _ _ _ _ xC₁ xC₂ yC₁ yC₂ ha hb hs
    have := Prod.Ioo_subset R _ _ hs
    exact ⟨hF₁.3 xC₁ yC₁ ha this.1, hF₂.3 xC₂ yC₂ hb this.2⟩

/-- The projection of a face of a product set onto the first component is a face of the
projection of the product set onto the first component. -/
protected theorem fst {C₁ : Set X} {C₂ : Set Y} {F : Set (X × Y)}
    (hF : IsFaceOf R F (C₁ ×ˢ C₂)) : IsFaceOf R (Prod.fst '' F) C₁ where
  isConvexSet := IsConvexSet.image Prod.isAffineMap_fst hF.isConvexSet
  le := by
    intro x hx
    simp only [Set.mem_image, Prod.exists, exists_and_right, exists_eq_right] at hx
    exact (Set.mem_prod.mp <| hF.le hx.choose_spec).1
  left_mem_of_mem_Ioo := by
    simp only [Set.mem_image, Prod.exists, exists_and_right, exists_eq_right, forall_exists_index]
    intro x y a hx hy ha z h
    refine ⟨ha, hF.left_mem_of_mem_Ioo (x := (x, ha)) (y := (y, ha)) (z := (a, ha)) ?_ ?_ z ?_⟩
    · exact Set.mem_prod.mp ⟨hx, (hF.le z).2⟩
    · exact Set.mem_prod.mp ⟨hy, (hF.le z).2⟩
    · have := (IsAffineMap.prodMk (.id (R := R)) (.const ha)).image_Ioo x y
      simp only [id_eq] at this
      simpa [← this]

/-- The projection of a face of a product set onto the second component is a face of the
projection of the product set onto the second component. -/
protected theorem snd {C₁ : Set X} {C₂ : Set Y} {F : Set (X × Y)}
    (hF : IsFaceOf R F (C₁ ×ˢ C₂)) : IsFaceOf R (Prod.snd '' F) C₂ := by
  have := hF.map (φ := Prod.swap) ((Prod.isAffineMap_snd).prodMk (Prod.isAffineMap_fst))
    Prod.swap_injective
  convert IsFaceOf.fst (by simpa)
  simp [Set.image_image]

end Prod

end IsFaceOf

end Semiring

section IsCancelConvexSpace

variable [Field R] [LinearOrder R] [IsStrictOrderedRing R]

variable {P : Set X}

variable [ConvexSpace R X] [IsCancelConvexSpace R X]

/-- If a point `x` does not lie in the convex hull of a set `s`, then `{x}` is a face of the convex
hull of `s` and `{x}`. -/
lemma IsFaceOf.singleton_convexHull_insert {s : Set X} {x : X} (hx : x ∉ convexHull R s) :
    IsFaceOf R {x} (convexHull R (insert x s)) := by
  by_cases h : s.Nonempty
  · constructor
    · exact IsConvexSet.singleton
    · exact le_trans (by simp) subset_convexHull_self
    · simp only [convexHull_insert h, Icc, Set.mem_iUnion, Set.mem_ofPred_eq, Ioo,
        forall_exists_index]
      rintro x₁ y _ i hi a₁ b₁ ha₁ hb₁ hab₁ rfl j hj a₂ b₂ ha₂ hb₂ hab₂ rfl rfl a b ha hb hab h
      by_cases hb0 : b₁ = 0
      · subst hb0; simp at hab₁; simp [hab₁]
      · by_cases hp : (a * a₁ + b * a₂) ≠ 0
        · exfalso
          let hα : 0 ≤ (a * a₁) / (a * a₁ + b * a₂) := by positivity
          let hβ : 0 ≤ (b * a₂) / (a * a₁ + b * a₂) := by positivity
          let hγ : 0 ≤ (a * b₁) / (a * b₁ + b * b₂) := by positivity
          let hδ : 0 ≤ (b * b₂) / (a * b₁ + b * b₂) := by positivity
          have := convexCombPair_convexCombPair_convexCombPair_comm' (M := X) ha.le hb.le hab
            ha₁ hb₁ hab₁ ha₂ hb₂ hab₂ hα hβ ?_ hγ hδ ?_ ?_ ?_ ?_ ?_
          · rw [this _ _ i j, convexCombPair_same] at h
            have hij := (convexCombPair_eq_left _ (by positivity) _).1 h
            exact hx (hij ▸ IsConvexSet.convexHull.convexCombPair_mem hi hj ..)
          all_goals field_simp
        · push Not at hp
          obtain ⟨h₁, h₂⟩ := (add_eq_zero_iff_of_nonneg (by positivity) (by positivity)).mp hp
          have h₁ := (mul_eq_zero.mp h₁).resolve_left ha.ne'
          have h₂ := (mul_eq_zero.mp h₂).resolve_left hb.ne'
          simp only [h₁, h₂, zero_add] at hab₁ hab₂
          simp only [h₁, h₂, hab₁, convexCombPair_zero, hab₂] at h ⊢
          exfalso
          rw [← h] at hx
          exact hx <| IsConvexSet.convexHull.convexCombPair_mem hi hj ..
  · simp [Set.not_nonempty_iff_eq_empty.mp h]

end IsCancelConvexSpace

end Convexity
