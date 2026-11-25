/-
Copyright (c) 2026 Olivia Röhrig, Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Olivia Röhrig, Mara Gruß, Valentina Taylor Cerra, Martin Winter
-/
module

public import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Lattice
public import Mathlib.Geometry.Convex.Segment

/-! This file defines faces of convex sets.

TODO: align this API with `IsFaceOf` for cones.
-/

@[expose] public section

namespace Convexity

open Function

variable {R M M₁ M₂ : Type*}

section Semiring

variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [ConvexSpace R M]

namespace ConvexSet

/- NOTE: maybe this should be defined on `Set` instead of `ConvexSet`. -/
/-- A subset `F` of a convex set `C` is a face of `C` iff it is an extreme subset. -/
structure IsFaceOf (F C : ConvexSet R M) where
  le : F ≤ C
  left_mem_of_mem_Ioo : ∀ ⦃x⦄, x ∈ C → ∀ ⦃y⦄, y ∈ C →
    ∀ ⦃z⦄, z ∈ F → z ∈ Ioo R x y → x ∈ F

namespace IsFaceOf

theorem empty {C : ConvexSet R M} : IsFaceOf ∅ C where
  le := SetLike.empty_le _
  left_mem_of_mem_Ioo := by simp

/- A convex set is a face of itself. -/
theorem refl (C : ConvexSet R M) : C.IsFaceOf C :=
  ⟨by simp , by intro x hx y hy z hz h; apply hx⟩

/- The face relation is transitive. -/
theorem trans {C F₁ F₂ : ConvexSet R M} (h₁ : F₂.IsFaceOf F₁) (h₂ : F₁.IsFaceOf C) :
    F₂.IsFaceOf C := by
  constructor
  · apply Set.Subset.trans h₁.le h₂.le
  · intro x hx y hy z hz hhz
    have hz' : z ∈ F₁.carrier := Set.mem_of_mem_of_subset hz h₁.le
    refine h₁.left_mem_of_mem_Ioo (h₂.left_mem_of_mem_Ioo hx hy hz' hhz)
      (h₂.left_mem_of_mem_Ioo hy hx hz' ?_) hz hhz
    simpa [Ioo_symm] using hhz

/- For two faces `F₁, F₂` of `C`, `F₁` is a face of `F₂` iff it is a subset of `F₂`. -/
theorem iff_le_of_isFaceOf {C F₁ F₂ : ConvexSet R M} (h₁ : F₁.IsFaceOf C) (h₂ : F₂.IsFaceOf C) :
    F₁.IsFaceOf F₂ ↔ F₁.carrier ⊆ F₂.carrier := by
  constructor
  · exact fun h => h.le
  · intro hh
    constructor
    · exact hh
    · intro x hx y hy z hz hhz
      exact h₁.left_mem_of_mem_Ioo (Set.mem_of_mem_of_subset hx h₂.le)
        (Set.mem_of_mem_of_subset hy h₂.le) hz hhz

/- A convex set is a face of a face iff it is contained in the face and it is a face
of the ambient set. -/
lemma isFaceOf_iff {F C : ConvexSet R M} (F₁ : ConvexSet R M) (H : F.IsFaceOf C) :
    F₁.IsFaceOf F ↔ F₁.carrier ⊆ F.carrier ∧ F₁.IsFaceOf C:= by
  apply Iff.intro
  · exact fun h => ⟨h.le, trans h H⟩
  · intro h
    constructor
    · apply h.1
    · intro x hx y hy z hz hhz
      exact h.2.left_mem_of_mem_Ioo (Set.mem_of_mem_of_subset hx H.le)
        (Set.mem_of_mem_of_subset hy H.le) hz hhz

/- The intersection of two faces of two convex sets is a face of the intersection of the convex
sets. -/
theorem inf {S₁ S₂ F₁ F₂ : ConvexSet R M} (h₁ : F₁.IsFaceOf S₁) (h₂ : F₂.IsFaceOf S₂) :
    (F₁ ⊓ F₂).IsFaceOf (S₁ ⊓ S₂) := by
  constructor
  · intro x hx
    exact ⟨Set.mem_of_mem_of_subset hx.1 h₁.le, Set.mem_of_mem_of_subset hx.2 h₂.le⟩
  · intro a ha b hb z hz hhz
    exact ⟨h₁.left_mem_of_mem_Ioo ha.1 hb.1 hz.1 hhz, h₂.left_mem_of_mem_Ioo ha.2 hb.2 hz.2 hhz⟩

/- The intersection of two faces is a face. -/
theorem inf_left {C F₁ F₂ : ConvexSet R M} (h₁ : F₁.IsFaceOf C) (h₂ : F₂.IsFaceOf C) :
    (F₁ ⊓ F₂).IsFaceOf C := by
  constructor
  · exact le_trans inf_le_left h₁.le
  · intro x hx y hy z hz hhz
    exact ⟨h₁.left_mem_of_mem_Ioo hx hy hz.1 hhz, h₂.left_mem_of_mem_Ioo hx hy hz.2 hhz⟩

/- The face of two convex sets is a face of the intersection. -/
theorem inf_right {S₁ S₂ F : ConvexSet R M} (h₁ : F.IsFaceOf S₁) (h₂ : F.IsFaceOf S₂) :
    F.IsFaceOf (S₁ ⊓ S₂) :=
  ⟨Set.subset_inter h₁.le h₂.le,
    by intro x hx y hy z hz hhz; exact h₁.left_mem_of_mem_Ioo hx.1 hy.1 hz hhz⟩

variable [ConvexSpace R M₁]
variable [ConvexSpace R M₂]

/- The image of a face under an injective affine map is a face of the image. -/
theorem map {f : M₁ → M₂} {F C : ConvexSet R M₁} (hhf : IsAffineMap R f) (hf : Injective f)
    (hF : F.IsFaceOf C) : (F.map hhf).IsFaceOf (C.map hhf) := by
  constructor
  · intro x hx
    rcases hx with ⟨y , hy, rfl⟩
    exact Set.mem_image_of_mem _ (Set.mem_of_mem_of_subset hy hF.le)
  · intro x hx y hy z hz hhz
    rcases hx with ⟨m , hmC, rfl⟩
    rcases hy with ⟨n , hnC, rfl⟩
    rcases hz with ⟨l , hlF, rfl⟩
    have hl : l ∈ Convexity.Ioo R m n := by
      rcases hhz with ⟨ a, b, ha, hb, hab, hcomb⟩
      have h : f (convexCombPair a b ha.le hb.le hab m n) =
      convexCombPair a b ha.le hb.le hab (f m) (f n) := hhf.map_convexCombPair ha.le hb.le hab m n
      have hh : f (convexCombPair a b ha.le hb.le hab m n) = f l := by
        simpa [h] using hcomb
      exact ⟨ a, b, ha, hb, hab, hf hh⟩
    exact Set.mem_image_of_mem _ (hF.left_mem_of_mem_Ioo hmC hnC hlF hl)

/- The preimage of a face is a face of the preimage. -/
theorem comap_face {f : M₁ → M₂} {F C : ConvexSet R M₂} (hf : IsAffineMap R f) (hF : F.IsFaceOf C) :
   (F.comap hf).IsFaceOf (C.comap hf) := by
  constructor
  · apply Set.preimage_mono hF.le
  · have hF1 := hF.left_mem_of_mem_Ioo
    intro x hx y hy z hz hhz
    have hhz' : f z ∈ Convexity.Ioo R (f x) (f y) := by
      rcases hhz with ⟨ a, b, ha, hb, hab, hcomb⟩
      have hff : f (convexCombPair a b ha.le hb.le hab x y) =
        convexCombPair a b ha.le hb.le hab (f x) (f y) := hf.map_convexCombPair ha.le hb.le hab x y
      rw [hcomb] at hff
      use a, b, ha, hb, hab, hff.symm
    specialize @hF1 (f x) (Set.mem_preimage.mp hx ) (f y) (Set.mem_preimage.mp hy) (f z) (
      Set.mem_preimage.mp hz) hhz'
    apply Set.mem_preimage.mp hF1

/- `F` is a face of `C` iff the image of `F` is a face of the image of `C` under an injective affine
map -/
theorem isFaceOf_map_iff {f : M₁ → M₂} {F C : ConvexSet R M₁} (hhf : IsAffineMap R f)
    (hf : Injective f) : (F.map hhf).IsFaceOf (C.map hhf) ↔ F.IsFaceOf C := by
  constructor
  · intro h
    have hh := comap_face hhf h
    have h (A : ConvexSet R M₁) : (A.map hhf).comap hhf = A := by
      ext z
      constructor
      · intro hz
        rcases hz with ⟨y, hy, hzy⟩
        rw [hf hzy] at hy
        use hy
      · intro hz
        exact ⟨z, hz, rfl⟩
    rw [h F, h C] at hh
    exact hh
  · intro h
    apply map hhf hf h

end IsFaceOf

end ConvexSet

end Semiring

end Convexity
