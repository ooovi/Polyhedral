/-
Copyright (c) 2026 Olivia Röhrig, Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Olivia Röhrig, Mara Gruß, Valentina Taylor Cerra, Martin Winter
-/
module

public import Mathlib.Geometry.Convex.ConvexSpace.Defs

/-! This file defines faces oF Convex sets.

TODO: align this API with `IsFaceOf` for cones.
-/

@[expose] public section

namespace Convexity

open Function

variable {R M M₁ M₂ : Type*}

section Semiring

variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [ConvexSpace R M]

/- NOTE: this is a copy of mathlib convexity API adapted to `ConvexSpace`. -/
variable (R) in
/-- Open segment in a convex space. Note that `openSegment 𝕜 x x = {x}` instead of being `∅` when
the base semiring has some element between `0` and `1`. -/
def openSegment (x y : M) : Set M :=
  { z : M | ∃ (a b : R) (a0 : 0 < a) (b0 : 0 < b) (ab : a + b = 1),
    convexCombPair a b a0.le b0.le ab x y = z }

/- (x,y) = (y,x) -/
theorem openSegment_symm (x y : M) : openSegment R x y = openSegment R y x := by
  ext z
  constructor
  all_goals (intro h; rcases h with ⟨m, n, hm , hn , hmn , hz⟩; use n, m, hn, hm)
  all_goals (rw [convexCombPair_symm] at hz; rw [add_comm] at hmn; use hmn)

variable (R) in
/-- A subset `F` of a set `c` is a face of `c` iff it is an extreme subset. -/
structure IsFaceOf (F C : Set M) : Prop where
  le : F ⊆ C
  left_mem_of_mem_openSegment : ∀ ⦃x⦄, x ∈ C → ∀ ⦃y⦄, y ∈ C →
    ∀ ⦃z⦄, z ∈ F → z ∈ openSegment R x y → x ∈ F

namespace IsFaceOf

variable {C F C₁ C₂ F₁ F₂ : Set M}

theorem empty : IsFaceOf R (∅ : Set M) C where
  le := Set.empty_subset C
  left_mem_of_mem_openSegment := by simp

/- A set is a face of itself. -/
theorem refl : IsFaceOf R C C :=
  ⟨subset_rfl, fun _ hx _ _ _ _ _ ↦ hx⟩

/- The face relation is transitive. -/
theorem trans (h₁ : IsFaceOf R F₂ F₁) (h₂ : IsFaceOf R F₁ C) : IsFaceOf R F₂ C := by
  refine ⟨h₁.le.trans h₂.le, ?_⟩
  intro x hx y hy z hz hhz
  have hz' : z ∈ F₁ := h₁.le hz
  exact h₁.2 (h₂.2 hx hy hz' hhz) (h₂.2 hy hx hz' (by simpa [openSegment_symm] using hhz)) hz hhz

/- For two faces `F₁, F₂` of `c`, `F₁` is a face of `F₂` iff it is a subset of `F₂`. -/
theorem iff_le_of_isFaceOf (h₁ : IsFaceOf R F₁ C) (h₂ : IsFaceOf R F₂ C) :
    IsFaceOf R F₁ F₂ ↔ F₁ ⊆ F₂ := by
  constructor
  · exact fun h ↦ h.1
  · intro hh
    refine ⟨hh, ?_⟩
    intro x hx y hy z hz hhz
    exact h₁.2 (h₂.le hx) (h₂.le hy) hz hhz

/- A set is a face of a face iff it is contained in the face and it is a face
of the ambient set. -/
lemma isFaceOf_iff (H : IsFaceOf R F C) :
    IsFaceOf R F₁ F ↔ F₁ ⊆ F ∧ IsFaceOf R F₁ C := by
  refine ⟨fun h ↦ ⟨h.1, trans h H⟩, fun h ↦ ⟨h.1, ?_⟩⟩
  intro x hx y hy z hz hhz
  exact h.2.2 (H.le hx) (H.le hy) hz hhz

/- The intersection of two faces of two sets is a face of the intersection of the sets. -/
theorem inf (h₁ : IsFaceOf R F₁ C₁) (h₂ : IsFaceOf R F₂ C₂) :
    IsFaceOf R (F₁ ∩ F₂) (C₁ ∩ C₂) := by
  refine ⟨fun x hx ↦ ⟨h₁.le hx.1, h₂.le hx.2⟩, ?_⟩
  intro a ha b hb z hz hhz
  exact ⟨h₁.2 ha.1 hb.1 hz.1 hhz, h₂.2 ha.2 hb.2 hz.2 hhz⟩

/- The intersection of two faces is a face. -/
theorem inf_left (h₁ : IsFaceOf R F₁ C) (h₂ : IsFaceOf R F₂ C) : IsFaceOf R (F₁ ∩ F₂) C := by
  refine ⟨fun x hx ↦ h₁.le hx.1, ?_⟩
  intro x hx y hy z hz hhz
  exact ⟨h₁.2 hx hy hz.1 hhz, h₂.2 hx hy hz.2 hhz⟩

/- A face of two sets is a face of the intersection. -/
theorem inf_right (h₁ : IsFaceOf R F C₁) (h₂ : IsFaceOf R F C₂) : IsFaceOf R F (C₁ ∩ C₂) :=
  ⟨Set.subset_inter h₁.1 h₂.1, fun _ hx _ hy _ hz hhz ↦ h₁.2 hx.1 hy.1 hz hhz⟩

/-- The intersection of a set `c` with any family of faces of `c` is a face of `c`. -/
theorem sInf {c : Set M} {Fs : Set (Set M)} (h : ∀ F ∈ Fs, IsFaceOf R F C) :
    IsFaceOf R (C ∩ ⋂₀ Fs) C where
  le _ sm := sm.1
  left_mem_of_mem_openSegment := by
    intro x hx y hy z hz hxyz
    refine ⟨hx, fun F hF => ?_⟩
    exact (h F hF).left_mem_of_mem_openSegment hx hy (hz.2 F hF) hxyz

section map

variable [ConvexSpace R M₁] [ConvexSpace R M₂]
variable {C₁ F₁ : Set M₁} {C₂ F₂ : Set M₂}

/- The image of a face under an injective affine map is a face of the image. -/
theorem map {φ : M₁ → M₂} (hφ : IsAffineMap R φ) (hinj : Injective φ)
    (hF : IsFaceOf R F₁ C₁) : IsFaceOf R (φ '' F₁) (φ '' C₁) := by
  refine ⟨fun x ⟨y, hy, hyx⟩ ↦ ⟨y, hF.le hy, hyx⟩, ?_⟩
  intro x hx y hy z hz hhz
  rcases hx with ⟨m, hmC, rfl⟩
  rcases hy with ⟨n, hnC, rfl⟩
  rcases hz with ⟨l, hlF, rfl⟩
  have hl : l ∈ openSegment R m n := by
    rcases hhz with ⟨a, b, ha, hb, hab, hcomb⟩
    have h : φ (convexCombPair a b ha.le hb.le hab m n) =
        convexCombPair a b ha.le hb.le hab (φ m) (φ n) :=
      hφ.map_convexCombPair ha.le hb.le hab m n
    have hh : φ (convexCombPair a b ha.le hb.le hab m n) = φ l := by
      simpa [h] using hcomb
    exact ⟨a, b, ha, hb, hab, hinj hh⟩
  exact Set.mem_image_of_mem _ (hF.2 hmC hnC hlF hl)

/- The preimage of a face is a face of the preimage. -/
theorem comap_face {φ : M₁ → M₂} (hφ : IsAffineMap R φ) (hF : IsFaceOf R F₂ C₂) :
    IsFaceOf R (φ ⁻¹' F₂) (φ ⁻¹' C₂) := by
  refine ⟨Set.preimage_mono hF.1, ?_⟩
  intro x hx y hy z hz hhz
  have hhz' : φ z ∈ openSegment R (φ x) (φ y) := by
    rcases hhz with ⟨a, b, ha, hb, hab, hcomb⟩
    have hff : φ (convexCombPair a b ha.le hb.le hab x y) =
        convexCombPair a b ha.le hb.le hab (φ x) (φ y) :=
      hφ.map_convexCombPair ha.le hb.le hab x y
    rw [hcomb] at hff
    exact ⟨a, b, ha, hb, hab, hff.symm⟩
  exact hF.2 hx hy hz hhz'

/- `F` is a face of `C` iff the image of `F` is a face of the image of `C` under an injective affine
map -/
theorem isFaceOf_map_iff {φ : M₁ → M₂} (hφ : IsAffineMap R φ) (hinj : Injective φ) :
    IsFaceOf R (φ '' F₁) (φ '' C₁) ↔ IsFaceOf R F₁ C₁ := by
  refine ⟨fun h ↦ ?_, map hφ hinj⟩
  have h' := comap_face hφ h
  rwa [Set.preimage_image_eq _ hinj, Set.preimage_image_eq _ hinj] at h'


end map

end IsFaceOf

end Semiring

end Convexity
